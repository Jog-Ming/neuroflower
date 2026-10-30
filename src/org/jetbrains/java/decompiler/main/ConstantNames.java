// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.ExceptionHandler;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructContext;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructConstantValueAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructEnclosingMethodAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructExceptionsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructInnerClassesAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructNestHostAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructNestMembersAttribute;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.Pair;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.collections.VBStyleCollection;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Restores references to inlined constants from the constant pool.
 *
 * <p>javac enters a class into the pool when the source names one of its constants, even though the
 * constant itself is folded to a literal. So a class the jar's pool holds and this file's text never
 * mentions is trace evidence that the original wrote {@code Owner.NAME} at some literal. The literal
 * is rewritten only when exactly one such missing owner declares that value, and the printed form is
 * valid source; nothing is compiled, so an ambiguous value is left alone.
 */
public final class ConstantNames {
  private ConstantNames() {
  }

  private record Constant(String owner, String name, VariableType kind) {
  }

  private enum VariableType {
    INT, LONG, FLOAT, DOUBLE, STRING, BOOLEAN, CHAR, BYTE, SHORT
  }

  private record Site(int start, int end, String replacement, String owner) {
  }

  /** The text with named constants restored, or the same text when nothing is provable. */
  public static String restore(String text, ClassNode root) {
    Set<String> present = new LinkedHashSet<>();
    Set<String> explained = new LinkedHashSet<>();
    collectPool(root, present, explained, new LinkedHashSet<>());
    Set<String> missing = new LinkedHashSet<>();
    for (String owner : present) {
      String simple = simpleName(owner);
      // A class the file already accounts for is no evidence that the source named one of its
      // constants.
      if (!simple.isEmpty() && !mentions(text, simple) && !explained.contains(owner)) {
        missing.add(owner);
      }
    }
    List<String> imports = imports(text);
    String packageName = packageName(text);
    String nest = root == null || root.classStruct == null ? "" : root.classStruct.qualifiedName;
    Map<String, List<Constant>> candidates = new HashMap<>();
    // A class's own constant is a candidate too: naming it interns the class into the pool at the
    // site of the first use, which the original's pool order records.
    StructClass own = root == null ? null : root.classStruct;
    if (own != null) {
      ownCandidates(candidates, own);
    }
    if (missing.isEmpty() && candidates.isEmpty()) {
      return text;
    }
    for (String owner : missing) {
      if (isBootstrapOwner(owner)) {
        continue; // present for a lambda/indy bootstrap, never a source-named constant owner
      }
      addOwnerCandidates(candidates, owner, nest, packageName, imports, true);
    }
    if (candidates.isEmpty()) {
      return text;
    }

    List<Site> sites = new ArrayList<>();
    Map<String, List<int[]>> ownInitializers = own == null ? Map.of() : ownInitializers(text, own);
    scan(text, candidates, imports, packageName, sites, own == null ? "" : own.qualifiedName,
      ownInitializers);
    if (sites.isEmpty()) {
      return text;
    }
    StringBuilder builder = new StringBuilder(text);
    for (int i = sites.size() - 1; i >= 0; i--) {
      Site site = sites.get(i);
      builder.replace(site.start(), site.end(), site.replacement());
    }
    return builder.toString();
  }

  /**
   * The text with named constants restored, attributing every nested class's text to the pool of
   * that class and bounding a foreign constant's naming site by the pool's interning order.
   *
   * <p>The printer writes a nested or anonymous class into the enclosing class's text, but javac
   * built that class's own constant pool. A literal inside the nested text can only be evidence
   * about the nested class's pool, and the pool order of that class bounds where its own naming
   * sites can be. {@code positions} maps each printed bytecode offset to its character offset and
   * {@code regions} marks the text ranges each class was printed into.
   */
  public static String restore(String text, ClassNode root,
                               Map<Pair<String, String>, Map<Integer, Integer>> positions,
                               List<TextBuffer.ClassRegion> regions) {
    if (positions == null) {
      return restore(text, root);
    }
    if (root == null) {
      return text;
    }
    List<ClassNode> nodes = new ArrayList<>();
    collectNodes(root, nodes);
    Map<String, ClassNode> byName = new LinkedHashMap<>();
    for (ClassNode node : nodes) {
      if (node.classStruct != null) {
        byName.put(node.classStruct.qualifiedName, node);
      }
    }

    // Regions nest: the class tree was printed linearly, so sort by start and keep a stack of
    // enclosing regions. A region's own text is what is left after its direct children.
    List<TextBuffer.ClassRegion> sorted = new ArrayList<>(regions == null ? List.of() : regions);
    sorted.sort(Comparator.comparingInt(TextBuffer.ClassRegion::getStart)
      .thenComparing(Comparator.comparingInt(TextBuffer.ClassRegion::getEnd).reversed()));
    Interval enclosing = new Interval(null, 0, text.length());
    Deque<Interval> stack = new ArrayDeque<>();
    stack.push(enclosing);
    for (TextBuffer.ClassRegion region : sorted) {
      if (region.getEnd() <= region.getStart()) {
        continue;
      }
      while (stack.size() > 1 && stack.peek().end <= region.getStart()) {
        stack.pop();
      }
      Interval interval = new Interval(region.getClassName(), region.getStart(), region.getEnd());
      stack.peek().children.add(interval);
      stack.push(interval);
    }
    Map<String, List<int[]>> spansByClass = new HashMap<>();
    List<int[]> rootSpans = computeSpans(enclosing, spansByClass);

    List<String> imports = imports(text);
    String packageName = packageName(text);
    List<Site> sites = new ArrayList<>();
    Rules rootRules = rules(text, rootSpans, root, positions, imports, packageName);
    if (rootRules != null) {
      scanClass(text, rootSpans, rootRules, sites);
    }
    expressionSites(text, rootSpans, root, sites);
    initializerSites(text, rootSpans, root, sites);
    deadNamings(text, rootSpans, rootRules, root.classStruct, packageName, sites,
      anonymousPadding(root.classStruct));
    for (Map.Entry<String, List<int[]>> entry : spansByClass.entrySet()) {
      ClassNode node = byName.get(entry.getKey());
      if (node == null) {
        continue; // text attributed to a class we have no pool for; leave it alone
      }
      Rules classRules = rules(text, entry.getValue(), node, positions, imports, packageName);
      if (classRules != null) {
        scanClass(text, entry.getValue(), classRules, sites);
      }
      expressionSites(text, entry.getValue(), node, sites);
      initializerSites(text, entry.getValue(), node, sites);
      deadNamings(text, entry.getValue(), classRules, node.classStruct, packageName, sites, 0);
    }
    if (sites.isEmpty()) {
      return text;
    }
    sites.sort(Comparator.comparingInt(Site::start));
    StringBuilder builder = new StringBuilder(text);
    for (int i = sites.size() - 1; i >= 0; i--) {
      Site site = sites.get(i);
      builder.replace(site.start(), site.end(), site.replacement());
    }
    return builder.toString();
  }

  /** What one class's text may name: its candidates and where the pool order places each owner. */
  private record Rules(Map<String, List<Constant>> candidates, Placement placement,
                       Set<String> strict, Set<String> missing,
                       Map<String, List<Constant>> compositeCandidates, Set<String> compositeOwners,
                       String own, Map<String, List<int[]>> ownInitializers,
                       List<String> imports, String packageName) {
  }

  /**
   * Where a naming site may lie, in text and in code generation order.
   *
   * <p>{@code windows} bounds a site by character offsets; {@code coordinates} bounds it by the
   * (method, instruction) point at which the printer's position map places it. The coordinate check
   * is the exact form: javac knows the pool order in generation order, and the text order only
   * approximates it when an instruction has no printed position.
   */
  private record Placement(Map<String, int[]> windows, Map<String, long[]> coordinates,
                           List<SiteSpace> spaces, Set<String> strict,
                           Map<String, Double> folded, Map<String, Long> internedAt,
                           Map<String, Long> namingAt, Set<String> lexical,
                           List<int[]> spans, Set<String> prefix, Set<String> inherited,
                           Map<String, PairSite> pairs, Map<String, ValueSite> values,
                           Set<String> bares, Set<String> earlyOwners, boolean ownEarly,
                           boolean ownProven, StructClass cls, String text) {
    /**
     * Whether this text position lies where the pool order proves the owner was named.
     *
     * <p>Before a window or a coordinate can prove a site, one contradiction can exclude it. When
     * the owner's {@code Class} entry sits after a pool entry that references the owner, javac
     * entered the Class as that reference's operand while generating it, not through a naming: a
     * naming would have been resolved first and interned the Class before the reference. The
     * reference's own instruction is then the earliest point at which the Class exists, so a site
     * printed before it would move the entry earlier than the original had it. Within one call this
     * is exactly the case of a literal in an argument: the call's name is printed before its
     * arguments, although they are generated first.
     */
    boolean proves(String owner, int start) {
      if (lexical != null && lexical.contains(owner)) {
        // The enclosing Class entry was interned while the class's names were resolved, before
        // any generated code and independently of where the source put the name.
        return existsAt(owner, start);
      }
      if (!existsAt(owner, start)) {
        return false;
      }
      // The pair's own record is the exact placement; a printed-line window only approximates it.
      // Where the site has a generation point, the pair's bracket decides and the window cannot
      // admit a literal it rejects (an unplaceable site, such as a field initializer's, has no
      // generation point and is left to the window).
      PairSite pair = pairs == null ? null : pairs.get(owner);
      if (pair != null) {
        long coordinate = siteCoordinate(spaces, start);
        if (coordinate != NO_COORDINATE) {
          if (pair.successorKey() != null && !pairProvesBounds(pair, start, this)) {
            return false; // a folded value's own instruction is the only place its naming stood
          }
          if (pair.successorKey() == null
              && (coordinate <= pair.lower() || coordinate >= pair.successor())) {
            return false; // outside the generation gap the pair leaves for its reference
          }
        }
      }
      int[] window = windows == null ? null : windows.get(owner);
      if (window != null && start >= window[0] && start < window[1]) {
        return true;
      }
      return byCoordinate(owner, start);
    }

    /**
     * Whether the pool allows this owner's {@code Class} entry to exist at the site: the entry's
     * first field or method reference, and the first naming of a pool-unexplained owner, cannot
     * be preceded by a naming.
     */
    boolean existsAt(String owner, int start) {
      if (earlyOwners.contains(owner)) {
        return true; // entered while the class's names were resolved, before any generated code
      }
      return withinInterned(owner, start) && afterNaming(owner, start);
    }

    /**
     * Whether this site comes after the point where the owner's first naming entered its
     * {@code Class} entry, or before it where the pool order still admits it.
     *
     * <p>A naming earlier than the original moves the Class entry earlier in the pool, and that
     * reorders every lower entry interned in between. The literal at such a site is itself usually
     * a pooled value interned right there, and the name would enter the Class and its name before
     * it instead of after, so a mere "nothing between" test is not enough: the site must lie after
     * every lower entry's first use, the same bound that places a first naming exactly.
     */
    private boolean afterNaming(String owner, int start) {
      Long naming = namingAt == null ? null : namingAt.get(owner);
      if (naming == null) {
        return true;
      }
      long nearest = printedCoordinate(spaces, start);
      if (nearest == NO_COORDINATE || nearest >= naming) {
        return true;
      }
      return byCoordinate(owner, start);
    }

    /**
     * Whether the generation order alone puts the site in the pool slot, without the looser
     * printed-line window. Choosing among several constants of one owner needs this: a line
     * window only proves the owner appeared somewhere on that line, and a frequent value on the
     * same line proves nothing about which literal the source named.
     */
    boolean provesExactly(String owner, int start) {
      return (lexical != null && lexical.contains(owner))
        || existsAt(owner, start) && byCoordinate(owner, start);
    }

    /**
     * Whether the generation order places this site outside the owner's pool-order bounds.
     *
     * <p>A naming site must fall after every lower pool entry's first use and before every higher
     * one's, so a printed position beyond either bound cannot be the site that interned the
     * owner's {@code Class} entry. An unplaceable site (a field initializer, or a method the
     * printer mapped no instruction in) is not contradicted: the pool says nothing about it.
     */
    boolean contradicts(String owner, int start) {
      if (earlyOwners.contains(owner)) {
        return false;
      }
      long[] bounds = coordinates == null ? null : coordinates.get(owner);
      if (bounds == null) {
        return false;
      }
      long coordinate = siteCoordinate(spaces, start);
      if (coordinate == NO_COORDINATE) {
        return false;
      }
      Long naming = namingAt == null ? null : namingAt.get(owner);
      // Only a bound on the far side of the point the pool proves interns the Class can bracket
      // the naming. A lower entry first used after that point was interned earlier regardless,
      // and a higher entry first used before it shows the rank model placed a use too early;
      // neither is evidence against the site.
      boolean beforePred = coordinate <= bounds[0] && (naming == null || bounds[0] < naming);
      boolean afterSucc = coordinate >= bounds[1] && (naming == null || bounds[1] > naming);
      return beforePred || afterSucc;
    }

    private boolean byCoordinate(String owner, int start) {
      if (coordinates == null) {
        return false;
      }
      long[] bounds = coordinates.get(owner);
      if (bounds == null) {
        return false;
      }
      long coordinate = siteCoordinate(spaces, start);
      return coordinate != NO_COORDINATE && coordinate > bounds[0] && coordinate < bounds[1];
    }

    /** The pool proves the owner's Class entry already exists at this printed position. */
    private boolean withinInterned(String owner, int start) {
      Long interned = internedAt == null ? null : internedAt.get(owner);
      if (interned == null) {
        return true;
      }
      long nearest = printedCoordinate(spaces, start);
      return nearest == NO_COORDINATE || nearest >= interned;
    }
  }

  private static final Placement NO_PLACEMENT =
    new Placement(null, null, List.of(), Set.of(), Map.of(), Map.of(), Map.of(), Set.of(),
      List.of(), null, Set.of(), Map.of(), Map.of(), Set.of(), Set.of(), false, false, null, "");

  /** One method's printed positions: bytecode offset to character offset, and the method's rank. */
  private record SiteSpace(int rank, Map<Integer, Integer> positions, int min, int max, String key) {
  }

  /** The first instruction that references a pool entry, in javac's code generation order. */
  private record FirstUse(int order, int offset, String methodKey) {
  }

  private static final long NO_COORDINATE = Long.MIN_VALUE;

  /**
   * The attribute names javac's class-file writer interns while writing. Every entry a naming
   * interned exists before the first of these, because all code generation precedes the write.
   */
  private static final Set<String> ATTRIBUTE_NAMES = Set.of(
    "ConstantValue", "Code", "StackMapTable", "Exceptions", "InnerClasses", "EnclosingMethod",
    "Synthetic", "Signature", "SourceFile", "SourceDebugExtension", "LineNumberTable",
    "LocalVariableTable", "LocalVariableTypeTable", "Deprecated", "RuntimeVisibleAnnotations",
    "RuntimeInvisibleAnnotations", "RuntimeVisibleParameterAnnotations",
    "RuntimeInvisibleParameterAnnotations", "RuntimeVisibleTypeAnnotations",
    "RuntimeInvisibleTypeAnnotations", "AnnotationDefault", "BootstrapMethods",
    "MethodParameters", "NestHost", "NestMembers", "Record", "PermittedSubclasses");

  /** The first pool entry the class-file writer interns for an attribute, or MAX when none. */
  private static int attributeStart(StructClass cls) {
    List<PooledConstant> pool = cls.getPool().getPool();
    int start = Integer.MAX_VALUE;
    for (int i = 1; i < pool.size(); i++) {
      if (pool.get(i) instanceof PrimitiveConstant utf8 && utf8.type == CodeConstants.CONSTANT_Utf8
          && ATTRIBUTE_NAMES.contains(utf8.getString())) {
        start = Math.min(start, i);
      }
    }
    return start;
  }

  /** A (generation rank, instruction offset) point packed into one comparable value. */
  private static long coordinate(int rank, int offset) {
    return ((long) rank << 32) | (offset & 0xffffffffL);
  }

  /**
   * The point a text position occupies in one class's generation order, or {@link #NO_COORDINATE}.
   *
   * <p>Only positions the printer recorded can place a site. The literal a name replaces usually
   * has no position of its own (it is folded before printing), so the point is the greatest offset
   * printed at or before it, inside the method block whose printed positions bracket the site.
   */
  private static long siteCoordinate(List<SiteSpace> spaces, int position) {
    SiteSpace space = innermost(spaces, position);
    if (space != null) {
      int bestPosition = Integer.MIN_VALUE;
      int offset = -1;
      for (Map.Entry<Integer, Integer> entry : space.positions.entrySet()) {
        int printed = entry.getValue();
        if (printed > position) {
          continue;
        }
        // The nearest printed item before the site, and at one position the instruction that
        // starts there (the lowest offset). A lambda body records its synthetic exit at the body
        // start with a high offset; taking the highest offset instead would mistake it for the
        // item nearest the site.
        if (printed > bestPosition || (printed == bestPosition && (offset < 0 || entry.getKey() < offset))) {
          bestPosition = printed;
          offset = entry.getKey();
        }
      }
      if (offset >= 0) {
        return coordinate(space.rank, offset);
      }
    }
    return NO_COORDINATE;
  }

  /**
   * The printed method block a text position belongs to.
   *
   * <p>A lambda body is printed inside the expression that creates it, so the creating method's
   * printed range encloses the lambda's. A position inside the lambda belongs to the lambda's own
   * generation order, not the enclosing method's: the innermost range containing it.
   */
  private static SiteSpace innermost(List<SiteSpace> spaces, int position) {
    SiteSpace best = null;
    for (SiteSpace space : spaces) {
      if (position < space.min || position > space.max) {
        continue;
      }
      if (best == null || space.max - space.min < best.max - best.min) {
        best = space;
      }
    }
    return best;
  }

  /**
   * The generation point of the item printed nearest before this text position, or
   * {@link #NO_COORDINATE}.
   *
   * <p>Text order, not bytecode order, picks that item: a call's name and invoke are printed before
   * its arguments although the arguments are generated first, so an argument's offset can be lower
   * than the offset printed at the call. At one printed position the lowest offset is the
   * instruction that starts there; higher offsets are bytes inside it. This is the position the
   * source occupies at the site, so it can contradict the pool order even where the looser
   * {@link #siteCoordinate} admits a window.
   */
  private static long printedCoordinate(List<SiteSpace> spaces, int position) {
    SiteSpace space = innermost(spaces, position);
    if (space != null) {
      int bestPosition = Integer.MIN_VALUE;
      int offset = -1;
      for (Map.Entry<Integer, Integer> entry : space.positions.entrySet()) {
        int printed = entry.getValue();
        if (printed > position) {
          continue;
        }
        if (printed > bestPosition || (printed == bestPosition && (offset < 0 || entry.getKey() < offset))) {
          bestPosition = printed;
          offset = entry.getKey();
        }
      }
      if (offset >= 0) {
        return coordinate(space.rank, offset);
      }
    }
    return NO_COORDINATE;
  }

  /**
   * The exact generation-order bounds of a naming site for pool entry {@code index}: every lower
   * entry's first use precedes the site and every higher entry's first use follows it. Entries with
   * no instruction use are absent from {@code firstUses}; they cannot bound anything.
   *
   * <p>The class's own, superclass and interface {@code Class} entries are interned when the class
   * is entered, before any body is generated, so an instruction that uses one says nothing about
   * the pool order and it is never used as a bound. {@code folded} is the value entry javac entered
   * together with this {@code Class} entry; its first use is the naming site itself, so it cannot
   * bound the site from above.
   */
  private static long[] coordinates(Map<Integer, FirstUse> firstUses, int index, Set<Integer> early,
                                    int folded) {
    long pred = Long.MIN_VALUE;
    long succ = Long.MAX_VALUE;
    for (Map.Entry<Integer, FirstUse> entry : firstUses.entrySet()) {
      int key = entry.getKey();
      if (key == index || key == folded || early.contains(key)) {
        continue;
      }
      long point = coordinate(entry.getValue().order(), entry.getValue().offset());
      if (key < index) {
        pred = Math.max(pred, point);
      }
      else {
        succ = Math.min(succ, point);
      }
    }
    return new long[]{pred, succ};
  }

  private static int compare(FirstUse a, FirstUse b) {
    return a.order != b.order ? Integer.compare(a.order, b.order) : Integer.compare(a.offset, b.offset);
  }

  /**
   * The generation-order bounds of the point that interned the class's own {@code Class} entry.
   *
   * <p>Every lower entry was interned before that point and every higher one after it, so a site
   * outside the bounds would enter the {@code Class} at another position. A lower entry may be
   * first used long after it was entered: a {@code Class} operand of a reference is numbered after
   * the reference and entered with it, so the reference's first use is the operand's entry point,
   * even when the class's own literals use it in a later-generated method. Capping each operand's
   * point this way keeps the lower bound from running past the naming the pool records.
   */
  private static long[] ownBounds(StructClass cls, int ownIndex, Map<Integer, FirstUse> firstUses,
                                  Map<String, Integer> classIndices, Set<Integer> early) {
    Map<Integer, Long> upper = new HashMap<>();
    long succ = Long.MAX_VALUE;
    for (Map.Entry<Integer, FirstUse> entry : firstUses.entrySet()) {
      int key = entry.getKey();
      if (key == ownIndex || early.contains(key)) {
        continue;
      }
      long point = coordinate(entry.getValue().order(), entry.getValue().offset());
      if (key < ownIndex) {
        upper.put(key, point);
      }
      else {
        succ = Math.min(succ, point);
      }
    }
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = 1; i < pool.size(); i++) {
      if (!(pool.get(i) instanceof LinkConstant link) || link.classname == null) {
        continue;
      }
      Integer operand = classIndices.get(link.classname);
      FirstUse use = firstUses.get(i);
      if (operand == null || use == null || operand >= ownIndex || i >= operand
          || early.contains(operand)) {
        continue;
      }
      long point = coordinate(use.order(), use.offset());
      upper.merge(operand, point, Math::min);
    }
    long pred = Long.MIN_VALUE;
    for (long point : upper.values()) {
      pred = Math.max(pred, point);
    }
    return new long[]{pred, succ};
  }

  private static final class Interval {
    final String className;
    final int start;
    final int end;
    final List<Interval> children = new ArrayList<>();

    Interval(String className, int start, int end) {
      this.className = className;
      this.start = start;
      this.end = end;
    }
  }

  private static void collectNodes(ClassNode node, List<ClassNode> out) {
    out.add(node);
    for (ClassNode nested : node.nested) {
      collectNodes(nested, out);
    }
  }

  /** The parts of an interval that belong to no child region, plus each child's own parts by name. */
  private static List<int[]> computeSpans(Interval interval, Map<String, List<int[]>> byClass) {
    List<int[]> spans = new ArrayList<>();
    int cursor = interval.start;
    for (Interval child : interval.children) {
      if (child.start > cursor) {
        spans.add(new int[]{cursor, child.start});
      }
      cursor = Math.max(cursor, child.end);
      List<int[]> childSpans = computeSpans(child, byClass);
      if (child.className != null) {
        byClass.computeIfAbsent(child.className, k -> new ArrayList<>()).addAll(childSpans);
      }
    }
    if (cursor < interval.end) {
      spans.add(new int[]{cursor, interval.end});
    }
    return spans;
  }

  private static Rules rules(String text, List<int[]> spans, ClassNode node,
                             Map<Pair<String, String>, Map<Integer, Integer>> positions,
                             List<String> imports, String packageName) {
    StructClass own = node.classStruct;
    if (own == null || spans.isEmpty()) {
      return null;
    }
    StringBuilder self = new StringBuilder();
    for (int[] span : spans) {
      self.append(text, span[0], span[1]);
    }
    String selfText = self.toString();

    Set<String> catchTypes = new HashSet<>();
    Map<Integer, FirstUse> firstUses = firstUses(own, catchTypes);
    List<Map.Entry<Integer, FirstUse>> orderedUses = new ArrayList<>(firstUses.entrySet());
    orderedUses.sort((a, b) -> compare(a.getValue(), b.getValue()));
    Set<String> present = new LinkedHashSet<>();
    Set<String> explained = new LinkedHashSet<>();
    Set<String> referenced = new LinkedHashSet<>();
    collectPool(own, present, explained, referenced, firstUses);
    Set<String> missing = new LinkedHashSet<>();
    for (String owner : present) {
      String simple = simpleName(owner);
      // A class the file already accounts for is no evidence that the source named one of its
      // constants. The text test reads this class's own spans: its host prints into the same file,
      // so a name used there says nothing about this class's pool.
      if (!simple.isEmpty() && !mentions(selfText, simple) && !explained.contains(owner)) {
        missing.add(owner);
      }
    }

    Map<String, List<Constant>> candidates = new HashMap<>();
    ownCandidates(candidates, own);
    Map<String, int[]> windows = new HashMap<>();
    Map<String, long[]> coordinates = new HashMap<>();
    Set<String> strict = new HashSet<>();
    Map<String, Integer> classIndices = classIndices(own);
    Set<Integer> early = earlyClassEntries(own, classIndices);
    Set<Integer> setup = setupClassEntries(own, classIndices);
    Set<String> earlyOwners = earlyOwners(own, classIndices, setup, firstUses);
    boolean ownEarly = false;
    boolean ownProven = false;
    {
      Integer ownIndex = classIndices.get(own.qualifiedName);
      // No instruction uses the class's own Class entry, so nothing in the code can have entered
      // it: whatever position it holds was created by a folded constant naming before the code.
      // A field or method reference to the class that sits below the entry did enter it, as that
      // reference's operand, and then the entry says nothing about a naming.
      boolean selfReferenceBelow = false;
      if (ownIndex != null) {
        List<PooledConstant> pool = own.getPool().getPool();
        for (int i = 1; i < ownIndex && i < pool.size(); i++) {
          if (pool.get(i) instanceof LinkConstant link
              && own.qualifiedName.equals(link.classname)) {
            selfReferenceBelow = true;
            break;
          }
        }
      }
      ownEarly = ownIndex != null && !firstUses.containsKey(ownIndex) && !nested(own)
        && !selfReferenceBelow;
      // An entry no reference of the class itself can explain, with an instruction-referenced
      // entry above it, was interned before that instruction was generated: not as a reference
      // operand and not at write time. A folded own-constant naming is the only mechanism that
      // enters the class's own Class at a code point (a name resolved before any code enters it
      // earlier still), so the pool order brackets every site the naming can occupy exactly as
      // it does for a foreign owner.
      boolean referencedAbove = false;
      for (int key : firstUses.keySet()) {
        if (ownIndex != null && key > ownIndex) {
          referencedAbove = true;
          break;
        }
      }
      ownProven = ownIndex != null && !firstUses.containsKey(ownIndex) && !selfReferenceBelow
        && referencedAbove;
      if (ownProven) {
        coordinates.put(own.qualifiedName,
          ownBounds(own, ownIndex, firstUses, classIndices, early));
      }
    }
    Map<String, Double> folded = new HashMap<>();
    for (Map.Entry<String, Integer> entry : classIndices.entrySet()) {
      Double value = foldedValue(own, entry.getValue());
      if (value != null) {
        folded.put(entry.getKey(), value);
      }
    }
    String nest = nestOf(own.qualifiedName);
    Map<String, Long> namingAt = new HashMap<>();
    Set<String> lexical = new HashSet<>();
    Set<String> claimed = new HashSet<>(); // owners another rule already places sites for
    Set<String> candidateOwners = new HashSet<>();
    // An enclosing class whose Class entry opens the pool was named with the simple name while
    // the class's names were resolved, before any generated code. The nesting attributes explain
    // that Class entry, so the missing and referenced tests never see the owner; visit every
    // enclosing name directly instead.
    for (String ancestor : enclosings(own.qualifiedName)) {
      Integer index = classIndices.get(ancestor);
      if (index != null && earlyOwners.contains(ancestor)) {
        lexical.add(ancestor);
        claimed.add(ancestor);
        if (candidateOwners.add(ancestor)) {
          addOwnerCandidates(candidates, ancestor, nest, packageName, imports);
        }
      }
    }
    // The pool's own record of a naming -- the Class pair and the folded value entered with it --
    // places the site exactly, so it is read before the looser windows and takes precedence over
    // them: an owner the pool records this way is not offered to the window rules at all.
    Map<String, PairSite> pairs = pairSites(own, text, firstUses, catchTypes, setup, early, positions,
      ownProven);
    Map<String, PairSite> activePairs = new HashMap<>();
    Map<String, ValueSite> values = valueSites(own, firstUses, catchTypes, setup, early, positions);
    Map<String, ValueSite> activeValues = new HashMap<>();
    for (Map.Entry<String, PairSite> entry : pairs.entrySet()) {
      String owner = entry.getKey();
      if (claimed.contains(owner) || isBootstrapOwner(owner)) {
        continue;
      }
      // A pair of the class's own entry exists only when the pool proved a folded naming created
      // it; the class's own constants are already candidates through ownCandidates.
      if (!owner.equals(own.qualifiedName) && candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports, true);
      }
      activePairs.put(owner, entry.getValue());
    }
    for (Map.Entry<String, ValueSite> entry : values.entrySet()) {
      String owner = entry.getKey();
      if (claimed.contains(owner) || owner.equals(own.qualifiedName) || isBootstrapOwner(owner)
          || activePairs.containsKey(owner)) {
        continue;
      }
      if (candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports, true);
      }
      activeValues.put(owner, entry.getValue());
    }
    Set<String> inheritedNames = new HashSet<>();
    for (String owner : missing) {
      if (isBootstrapOwner(owner)) {
        continue;
      }
      if (candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports, true);
      }
      inheritedNames.addAll(addInheritedCandidates(candidates, owner, packageName, imports));
      claimed.add(owner);
      Integer index = classIndices.get(owner);
      if (index != null) {
        if (opensPool(own, index, setup, firstUses) && own.qualifiedName.startsWith(owner + "$")) {
          // The enclosing Class opens the pool, so the simple name was written while the class's
          // names were resolved; the lexical rule places the site and writes it unqualified.
          lexical.add(owner);
          continue;
        }
        int[] window = window(text, own, index, orderedUses, positions, false);
        if (window != null) {
          windows.put(owner, window);
        }
        // This owner's Class entry exists only because the source named one of its constants
        // (nothing else in the class file explains it), and javac entered the folded value right
        // after the Class and its name. That value's use is the naming site, so it cannot bound it.
        coordinates.put(owner, coordinates(firstUses, index, early, foldedNeighbor(own, index)));
        Long naming = namingPoint(own, index, firstUses, positions);
        if (naming != null) {
          namingAt.put(owner, naming);
        }
      }
    }
    // A Class entry the pool leaves unexplained may still be the one a flags-word naming entered:
    // the source wrote several constants of that owner OR-ed together, and javac interned the
    // owner's Class without a field reference. These owners are not offered to the ordinary scan;
    // the composite pass uses the exact pool-order proof only.
    Map<String, List<Constant>> compositeCandidates = new HashMap<>();
    Set<String> compositeOwners = new LinkedHashSet<>();
    for (String owner : present) {
      if (explained.contains(owner) || owner.equals(own.qualifiedName) || isBootstrapOwner(owner)
          || lexical.contains(owner) || claimed.contains(owner)) {
        continue;
      }
      Integer index = classIndices.get(owner);
      if (index == null) {
        continue;
      }
      if (!missing.contains(owner)) {
        coordinates.put(owner, coordinates(firstUses, index, early, foldedNeighbor(own, index)));
        Long naming = namingPoint(own, index, firstUses, positions);
        if (naming != null) {
          namingAt.put(owner, naming);
        }
      }
      addOwnerCandidates(compositeCandidates, owner, nest, packageName, imports);
      compositeOwners.add(owner);
    }
    // A class the pool uses through a field or method names nothing by itself, but the position of
    // its Class entry still records where javac first entered it: an entry before the first such
    // use was interned by a folded constant naming, and the pool order bounds that site the same
    // way. Naming the constant there cannot add a pool entry, so a wrong guess costs text, not
    // bytes; the window has to be fully bounded for the placement to be trustworthy.
    for (String owner : referenced) {
      if (missing.contains(owner) || owner.equals(own.qualifiedName) || isBootstrapOwner(owner)) {
        continue;
      }
      Integer index = classIndices.get(owner);
      if (index == null) {
        continue;
      }
      int[] window = window(text, own, index, orderedUses, positions, true);
      if (window == null && opensPool(own, index, setup, firstUses)
          && own.qualifiedName.startsWith(owner + "$")) {
        // The owner's Class entry is the first pool entry and no instruction references any
        // entry yet, so javac entered it while it resolved the class's names: a nested class
        // naming an enclosing constant with the simple name does exactly this, in a field
        // initializer or in a method body, before any generated code. The name is written
        // without a qualifier (javac interns the enclosing Class only from the simple name),
        // and the pool order places nothing around it, so no window is needed; the ordering
        // guard in the site pass keeps it ahead of every other name in the class.
        lexical.add(owner);
        claimed.add(owner);
        if (candidateOwners.add(owner)) {
          addOwnerCandidates(candidates, owner, nest, packageName, imports);
        }
        continue;
      }
      if (window == null) {
        // The owner's Class entry sits below the first reference that names it, so javac entered
        // it earlier -- by a folded constant naming. The naming must lie before that reference in
        // the text, which is the only bound left when the neighbouring entries have no printed
        // position.
        int[] before = beforeReferenceWindow(text, own, index, firstUses, positions);
        if (before == null) {
          continue;
        }
        window = before;
      }
      if (candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports);
      }
      claimed.add(owner);
      windows.put(owner, window);
      coordinates.put(owner, coordinates(firstUses, index, early, -1));
      strict.add(owner);
    }
    // A Class entry that follows its own first field or method reference was entered as that
    // reference's operand; the reference's instruction is where the Class first exists.
    Map<String, Long> internedAt = new HashMap<>();
    List<PooledConstant> pool = own.getPool().getPool();
    for (int i = 1; i < pool.size(); i++) {
      if (!(pool.get(i) instanceof LinkConstant link) || link.classname == null) {
        continue;
      }
      Integer classIndex = classIndices.get(link.classname);
      FirstUse use = firstUses.get(i);
      if (classIndex != null && i < classIndex && use != null && !internedAt.containsKey(link.classname)) {
        internedAt.put(link.classname, coordinate(use.order(), use.offset()));
      }
    }
    // Everything javac generates is interned before the class-file writer interns the first
    // attribute name; from there on the pool holds attribute data exactly as written, including
    // the InnerClasses table's and the StackMapTable's Class entries. A pair above that point is
    // attribute data, not a folded naming, however pair-shaped it looks.
    int writeStart = attributeStart(own);
    // A Class entry the pool leaves completely unexplained, entered as a bare pair (its name, then
    // neither a value nor a reference), exists only because the source named one of the owner's
    // constants, and that naming left no value entry: the constant folded to an immediate or to a
    // value already pooled. The pair's position is still the pool's record of the site, so a
    // literal of any value the owner's constants reproduce can be the naming.
    Set<String> bares = new HashSet<>();
    for (String owner : present) {
      if (explained.contains(owner) || owner.equals(own.qualifiedName) || isBootstrapOwner(owner)) {
        continue;
      }
      Integer index = classIndices.get(owner);
      if (index == null || index + 1 >= pool.size() || index >= writeStart) {
        continue; // absent, or interned by the class-file writer's attribute data
      }
      if (!(pool.get(index) instanceof PrimitiveConstant entry)
          || entry.type != CodeConstants.CONSTANT_Class || entry.index != index + 1
          || !owner.equals(entry.getString())) {
        continue;
      }
      if (!(pool.get(index + 1) instanceof PrimitiveConstant name)
          || name.type != CodeConstants.CONSTANT_Utf8) {
        continue;
      }
      boolean operand = false;
      for (int i = 1; i < index && i < pool.size(); i++) {
        if (pool.get(i) instanceof LinkConstant link && owner.equals(link.classname)) {
          operand = true; // a reference below the entry created it as its operand
          break;
        }
      }
      if (operand) {
        continue;
      }
      PooledConstant next = index + 2 < pool.size() ? pool.get(index + 2) : null;
      if (next instanceof LinkConstant) {
        continue; // the pair rules read this shape exactly
      }
      if (next instanceof PrimitiveConstant value
          && (value.type == CodeConstants.CONSTANT_Integer || value.type == CodeConstants.CONSTANT_Long
          || value.type == CodeConstants.CONSTANT_Float || value.type == CodeConstants.CONSTANT_Double
          || value.type == CodeConstants.CONSTANT_String)) {
        continue; // the value rules read the folded value exactly
      }
      bares.add(owner);
    }
    // A bare pair's owner has no value or reference successor to anchor its site, but the pool
    // order still bounds it: every lower entry's first use precedes the naming, and a higher
    // entry's first use follows it. The generation-order bracket is the bare site's evidence.
    for (String owner : bares) {
      Integer index = classIndices.get(owner);
      if (index != null && !coordinates.containsKey(owner) && !activePairs.containsKey(owner)) {
        coordinates.put(owner, coordinates(firstUses, index, early, foldedNeighbor(own, index)));
      }
    }
    if (candidates.isEmpty() && bares.isEmpty()) {
      return null;
    }
    return new Rules(candidates,
      new Placement(windows, coordinates, spaces(own, positions), strict, folded, internedAt,
        namingAt, lexical, spans, new HashSet<>(prefixOwners(own)), inheritedNames, activePairs,
        activeValues, bares, earlyOwners, ownEarly, ownProven, own, text),
      strict, missing, compositeCandidates, compositeOwners, own.qualifiedName,
      ownInitializers(text, spans, own), imports, packageName);
  }

  /**
   * The printed positions of this class's method bodies and static initializers, each tagged with
   * its generation rank. Instance field initializers are printed under a {@code <field-init>} key
   * that does not name the constructor their offsets belong to, so they are left out.
   */
  private static List<SiteSpace> spaces(StructClass own,
                                        Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    Map<String, Integer> ranks = methodRanks(own);
    List<SiteSpace> spaces = new ArrayList<>();
    for (Map.Entry<Pair<String, String>, Map<Integer, Integer>> entry : positions.entrySet()) {
      if (!own.qualifiedName.equals(entry.getKey().a) || entry.getValue().isEmpty()) {
        continue;
      }
      Integer rank = entry.getKey().b.startsWith("<field-init ")
        ? initializerRank(own, ranks, entry.getValue()) : ranks.get(entry.getKey().b);
      if (rank == null) {
        continue; // a key that names no method body, or an initializer no one constructor owns
      }
      int min = Integer.MAX_VALUE;
      int max = Integer.MIN_VALUE;
      for (int position : entry.getValue().values()) {
        min = Math.min(min, position);
        max = Math.max(max, position);
      }
      spaces.add(new SiteSpace(rank, entry.getValue(), min, max, entry.getKey().b));
    }
    return spaces;
  }

  /**
   * The generation rank of the constructor a lifted field initializer was printed from, or null.
   *
   * <p>The printer records an initializer's offsets under a key naming the field, not the method
   * that generated it. The offsets belong to a constructor only when its code contains every one
   * of them; a buffer no single constructor owns places nothing, and one shared by several is
   * left out rather than guessed.
   */
  private static Integer initializerRank(StructClass own, Map<String, Integer> ranks,
                                         Map<Integer, Integer> positions) {
    Integer found = null;
    for (StructMethod method : own.getMethods()) {
      if (!CodeConstants.INIT_NAME.equals(method.getName())) {
        continue;
      }
      String methodKey = InterpreterUtil.makeUniqueKey(method.getName(), method.getDescriptor());
      if (method.getInstructionSequence() == null) {
        try {
          method.expandData(own);
        }
        catch (Exception e) {
          continue;
        }
      }
      FullInstructionSequence code = method.getInstructionSequence();
      if (code == null || !containsOffsets(code, positions.keySet())) {
        continue;
      }
      if (found != null) {
        return null; // several constructors contain the offsets; the owner is ambiguous
      }
      found = ranks.get(methodKey);
    }
    return found;
  }

  /**
   * The generation rank of every method body, keyed like the printer's position map.
   *
   * <p>javac generates the method bodies in the class file's method order -- which for the
   * compiler's own output is the source declaration order -- and {@code <clinit>} last. The rank
   * must come from the class's method list rather than from the
   * pool's first uses: a method that only repeats references introduced earlier holds no first use,
   * yet its body still has a place in the generation order, and a site in it must still be
   * comparable with a bound placed in another method.
   */
  private static Map<String, Integer> methodRanks(StructClass cls) {
    Map<String, Integer> ranks = new HashMap<>();
    VBStyleCollection<StructMethod, String> methods = cls.getMethods();
    int count = methods.size();
    for (int i = 0; i < count; i++) {
      StructMethod method = methods.get(i);
      int rank = CodeConstants.CLINIT_NAME.equals(method.getName()) ? 2 * count + i : i;
      ranks.put(InterpreterUtil.makeUniqueKey(method.getName(), method.getDescriptor()), rank);
    }
    return ranks;
  }

  /**
   * The pool indices javac enters before generating any body: the class itself and its supertypes.
   * A use of one of these says nothing about where in the generation order the entry was created.
   */
  private static Set<Integer> earlyClassEntries(StructClass own, Map<String, Integer> classIndices) {
    Set<Integer> early = new HashSet<>();
    Integer ownIndex = classIndices.get(own.qualifiedName);
    if (ownIndex != null) {
      early.add(ownIndex);
    }
    if (own.superClass != null && own.superClass.getString() != null) {
      Integer index = classIndices.get(own.superClass.getString());
      if (index != null) {
        early.add(index);
      }
    }
    for (String name : own.getInterfaceNames()) {
      Integer index = classIndices.get(name);
      if (index != null) {
        early.add(index);
      }
    }
    return early;
  }

  /**
   * The entries that cannot be a folded-constant naming's own Class entry: the class itself and its
   * superclass. Interfaces are not among them: javac enters a class's superclass at class setup but
   * reaches an implemented interface only when a name or a reference first needs it, so an
   * interface's {@code Class} pair can record a naming.
   */
  private static Set<Integer> setupClassEntries(StructClass own, Map<String, Integer> classIndices) {
    Set<Integer> setup = new HashSet<>();
    Integer ownIndex = classIndices.get(own.qualifiedName);
    if (ownIndex != null) {
      setup.add(ownIndex);
    }
    if (own.superClass != null && own.superClass.getString() != null) {
      Integer index = classIndices.get(own.superClass.getString());
      if (index != null) {
        setup.add(index);
      }
    }
    return setup;
  }

  /**
   * The folded value javac entered together with the {@code Class} entry at {@code index}, or -1.
   *
   * <p>When the source names {@code Owner.NAME} and the constant folds, javac enters the owner's
   * {@code Class} entry, its name UTF8 and then the constant's value, in that order. A Class entry
   * created for a field or method reference is followed by a NameAndType instead. The value is the
   * pool's record of the very site the name stood at, so its first use is that site.
   */
  private static int foldedNeighbor(StructClass cls, int index) {
    List<PooledConstant> pool = cls.getPool().getPool();
    if (index + 2 >= pool.size()) {
      return -1;
    }
    if (!(pool.get(index) instanceof PrimitiveConstant owner)
        || owner.type != CodeConstants.CONSTANT_Class
        || owner.index != index + 1) {
      return -1;
    }
    if (!(pool.get(index + 2) instanceof PrimitiveConstant value)) {
      return -1;
    }
    return switch (value.type) {
      case CodeConstants.CONSTANT_Integer, CodeConstants.CONSTANT_Float,
           CodeConstants.CONSTANT_Long, CodeConstants.CONSTANT_Double,
           CodeConstants.CONSTANT_String -> index + 2;
      default -> -1;
    };
  }

  /**
   * The generation point at which a pool-unexplained owner was first named, or null.
   *
   * <p>javac enters the owner's {@code Class}, its name and the folded constant's value together
   * when the source first names one of the owner's constants, so that value's first instruction use
   * is the naming site. Only a pooled value can be that neighbour: a constant the source folds to
   * an immediate (a small int or char) enters no value, and the following entry then belongs to
   * whatever was entered next. An equal constant already in the pool is reused instead, with the
   * same consequence. Without a printed position for the use, the point is unknown.
   */
  private static Long namingPoint(StructClass cls, int index, Map<Integer, FirstUse> firstUses,
                                  Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    int folded = foldedNeighbor(cls, index);
    if (folded < 0 || !pooledValue(cls, folded) || hasEarlierEqual(cls, folded)) {
      return null;
    }
    FirstUse use = firstUses.get(folded);
    if (use == null || position(cls, use, positions) == null) {
      return null;
    }
    return coordinate(use.order(), use.offset());
  }

  /** Whether the pool entry is a long, float or double value, which javac always pools. */
  private static boolean pooledValue(StructClass cls, int index) {
    return index > 0 && index < cls.getPool().getPool().size()
      && cls.getPool().getPool().get(index) instanceof PrimitiveConstant primitive
      && (primitive.type == CodeConstants.CONSTANT_Long
          || primitive.type == CodeConstants.CONSTANT_Float
          || primitive.type == CodeConstants.CONSTANT_Double);
  }

  /** The site key a pool value entry folds to, or null for an entry no literal names. */
  private static String valueKey(PrimitiveConstant value) {
    VariableType kind = switch (value.type) {
      case CodeConstants.CONSTANT_Integer -> VariableType.INT;
      case CodeConstants.CONSTANT_Long -> VariableType.LONG;
      case CodeConstants.CONSTANT_Float -> VariableType.FLOAT;
      case CodeConstants.CONSTANT_Double -> VariableType.DOUBLE;
      case CodeConstants.CONSTANT_String -> VariableType.STRING;
      default -> null;
    };
    return kind == null || value.value == null ? null : kind + "|" + value.value;
  }

  /**
   * The pool entry a literal key names, with the kinds javac folds into one entry merged: a char
   * constant and an int literal of the same value share an {@code Integer}, and a boolean constant
   * is an {@code Integer} 0 or 1.
   */
  private static String canonicalKey(String key) {
    if (key == null) {
      return "";
    }
    int bar = key.indexOf('|');
    if (bar < 0) {
      return key;
    }
    String kind = key.substring(0, bar);
    String value = key.substring(bar + 1);
    if (kind.equals(VariableType.CHAR.name()) || kind.equals(VariableType.INT.name())) {
      return VariableType.INT.name() + '|' + value;
    }
    if (kind.equals(VariableType.BOOLEAN.name())) {
      return VariableType.INT.name() + '|' + (value.equals("true") ? "1" : "0");
    }
    return key;
  }

  /** Whether a constant equal to the pool entry at {@code index} already sat before it. */
  private static boolean hasEarlierEqual(StructClass cls, int index) {
    List<PooledConstant> pool = cls.getPool().getPool();
    if (index <= 0 || index >= pool.size() || !(pool.get(index) instanceof PrimitiveConstant value)
        || value.value == null) {
      return true; // a long/double second slot or an empty entry proves nothing
    }
    for (int i = 1; i < index; i++) {
      if (pool.get(i) instanceof PrimitiveConstant other && other.value != null
          && other.type == value.type && other.equals(value)) {
        return true;
      }
    }
    return false;
  }

  /** The pool index of each Class entry, keyed by the class name it names. */
  private static Map<String, Integer> classIndices(StructClass cls) {
    Map<String, Integer> indices = new HashMap<>();
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = 1; i < pool.size(); i++) {
      PooledConstant constant = pool.get(i);
      if (constant instanceof PrimitiveConstant primitive && primitive.type == CodeConstants.CONSTANT_Class
          && primitive.getString() != null) {
        indices.putIfAbsent(primitive.getString(), i);
      }
    }
    return indices;
  }

  /**
   * The value of the float or double constant the pool holds immediately after the Class entry at
   * {@code index}, or null when the next entry is not one.
   *
   * <p>When the source named an inlined constant in a float or double context, javac enters the
   * owner's Class entry and then the folded constant right after it. That neighbouring constant is
   * the pool's record of the value the original named there, and a float or double literal whose
   * value differs did not come from that constant. A sibling entry of another kind in between means
   * the Class entry was interned by something else, so nothing is proven.
   */
  private static Double foldedValue(StructClass cls, int index) {
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = index + 1; i < pool.size(); i++) {
      if (!(pool.get(i) instanceof PrimitiveConstant primitive)) {
        return null;
      }
      if (primitive.type == CodeConstants.CONSTANT_Utf8) {
        continue; // the Class entry's own name follows it
      }
      if (primitive.type == CodeConstants.CONSTANT_Float && primitive.value instanceof Float value) {
        return (double) value;
      }
      if (primitive.type == CodeConstants.CONSTANT_Double && primitive.value instanceof Double value) {
        return value;
      }
      return null;
    }
    return null;
  }

  /**
   * Where each pool entry an instruction references is first used.
   *
   * <p>javac generates the method bodies in the class file's method order and {@code <clinit>}
   * last. The instruction's offset orders the uses inside one method.
   */
  private static Map<Integer, FirstUse> firstUses(StructClass cls) {
    return firstUses(cls, null);
  }

  private static Map<Integer, FirstUse> firstUses(StructClass cls, Set<String> catchTypes) {
    Map<Integer, FirstUse> first = new HashMap<>();
    VBStyleCollection<StructMethod, String> methods = cls.getMethods();
    int count = methods.size();
    for (int i = 0; i < count; i++) {
      StructMethod method = methods.get(i);
      int rank = CodeConstants.CLINIT_NAME.equals(method.getName()) ? 2 * count + i : i;
      if (method.getInstructionSequence() == null) {
        try {
          method.expandData(cls); // released after decompilation; reparse for the pool order
        } catch (Exception e) {
          continue;
        }
      }
      FullInstructionSequence code = method.getInstructionSequence();
      if (code == null) {
        continue;
      }
      if (catchTypes != null && code.exceptionTable() != null) {
        for (ExceptionHandler handler : code.exceptionTable().getHandlers()) {
          if (handler.exceptionClass() != null) {
            catchTypes.add(handler.exceptionClass()); // a catch type is a Class entry with no use
          }
        }
      }
      String methodKey = InterpreterUtil.makeUniqueKey(method.getName(), method.getDescriptor());
      for (Instruction instruction : code) {
        int index = poolReference(instruction);
        if (index <= 0) {
          continue;
        }
        FirstUse use = new FirstUse(rank, instruction.startOffset, methodKey);
        FirstUse known = first.get(index);
        if (known == null || compare(use, known) < 0) {
          first.put(index, use);
        }
      }
    }
    return first;
  }

  /** The constant pool index an instruction's operand refers to, or -1 for a local operand. */
  private static int poolReference(Instruction instruction) {
    if (instruction.group == CodeConstants.GROUP_FIELDACCESS
        || instruction.group == CodeConstants.GROUP_INVOCATION) {
      return instruction.operand(0);
    }
    return switch (instruction.opcode) {
      case CodeConstants.opc_ldc, CodeConstants.opc_ldc_w, CodeConstants.opc_ldc2_w,
           CodeConstants.opc_new, CodeConstants.opc_anewarray, CodeConstants.opc_checkcast,
           CodeConstants.opc_instanceof, CodeConstants.opc_multianewarray -> instruction.operand(0);
      default -> -1;
    };
  }

  /**
   * The instructions of the method whose generation rank is {@code rank}, or {@code null}.
   *
   * <p>The ranks are the ones {@link #firstUses} assigns: the class's method order, static
   * initializers last.
   */
  private static FullInstructionSequence codeOfRank(StructClass cls, int rank) {
    VBStyleCollection<StructMethod, String> methods = cls.getMethods();
    int count = methods.size();
    for (int i = 0; i < count; i++) {
      StructMethod method = methods.get(i);
      int rankOf = CodeConstants.CLINIT_NAME.equals(method.getName()) ? 2 * count + i : i;
      if (rankOf != rank) {
        continue;
      }
      if (method.getInstructionSequence() == null) {
        try {
          method.expandData(cls); // released after decompilation; reparse for the operand window
        }
        catch (Exception e) {
          return null;
        }
      }
      return method.getInstructionSequence();
    }
    return null;
  }

  /**
   * Whether the long literal at this printed position decides the type of its own expression.
   *
   * <p>javac folds an int constant written where a long is wanted into the same long constant, so
   * naming an int constant at a long literal reproduces the bytes only where the surrounding
   * context does that coercing. A long arithmetic operation whose sibling operand the class file
   * widens with {@code i2l} is not such a context: that sibling was int-typed in the source, so
   * the operation is long because of this operand, and an int constant written here would have
   * compiled to int arithmetic. The widening conversion is the proof, and it can sit on either
   * side of the literal: operands are generated left to right.
   */
  private static boolean drivesLongType(Placement placement, int start, long value) {
    StructClass cls = placement.cls();
    if (cls == null || placement.spaces() == null) {
      return false;
    }
    long coordinate = siteCoordinate(placement.spaces(), start);
    if (coordinate == NO_COORDINATE) {
      return false;
    }
    FullInstructionSequence code = codeOfRank(cls, (int)(coordinate >>> 32));
    if (code == null || code.isEmpty()) {
      return false;
    }
    int offset = (int)(coordinate & 0xffffffffL);
    int size = code.length();
    int from = 0;
    while (from < size && code.getInstr(from).startOffset < offset) {
      from++;
    }
    // The printed position is the literal's own instruction, or the last printed one before it.
    int literal = -1;
    for (int i = from; i < size && i < from + 8; i++) {
      Instruction insn = code.getInstr(i);
      if (insn.opcode == CodeConstants.opc_ldc2_w && longConstant(cls, insn) == value) {
        literal = i;
        break;
      }
      if (consumes(cls, insn)) {
        break;
      }
    }
    if (literal < 0) {
      return false;
    }
    boolean widened = false;
    for (int i = literal - 1; i >= 0 && i >= literal - 16; i--) {
      Instruction insn = code.getInstr(i);
      if (insn.opcode == CodeConstants.opc_i2l) {
        widened = true;
        break;
      }
      if (consumes(cls, insn)) {
        break;
      }
    }
    for (int i = literal + 1; i < size && i <= literal + 32; i++) {
      Instruction insn = code.getInstr(i);
      int opcode = insn.opcode;
      if (opcode == CodeConstants.opc_i2l) {
        widened = true;
      }
      else if (isLongBinary(opcode)) {
        return widened;
      }
      else if (consumes(cls, insn)) {
        return false;
      }
    }
    return false;
  }

  /** The constant an {@code ldc2_w} pushes, when it is a long, or a value no literal has. */
  private static long longConstant(StructClass cls, Instruction insn) {
    PooledConstant constant = cls.getPool().getConstant(insn.operand(0));
    return constant instanceof PrimitiveConstant primitive && primitive.value instanceof Long number
      ? number : Long.MIN_VALUE;
  }

  private static boolean isLongBinary(int opcode) {
    return switch (opcode) {
      case CodeConstants.opc_ladd, CodeConstants.opc_lsub, CodeConstants.opc_lmul,
           CodeConstants.opc_ldiv, CodeConstants.opc_lrem, CodeConstants.opc_land,
           CodeConstants.opc_lor, CodeConstants.opc_lxor, CodeConstants.opc_lshl,
           CodeConstants.opc_lshr, CodeConstants.opc_lushr -> true;
      default -> false;
    };
  }

  /**
   * Whether an instruction ends this value's stay on the stack without a long arithmetic
   * operation: a store, return, branch, comparison, narrowing conversion or consuming call.
   */
  private static boolean consumes(StructClass cls, Instruction insn) {
    int opcode = insn.opcode;
    if (opcode >= CodeConstants.opc_istore && opcode <= CodeConstants.opc_astore) {
      return true;
    }
    if (opcode >= CodeConstants.opc_ireturn && opcode <= CodeConstants.opc_return) {
      return true;
    }
    if (opcode >= CodeConstants.opc_ifeq && opcode <= CodeConstants.opc_if_acmpne) {
      return true;
    }
    switch (opcode) {
      case CodeConstants.opc_ifnull, CodeConstants.opc_ifnonnull, CodeConstants.opc_goto,
           CodeConstants.opc_goto_w, CodeConstants.opc_tableswitch, CodeConstants.opc_lookupswitch,
           CodeConstants.opc_lcmp, CodeConstants.opc_l2i, CodeConstants.opc_l2f,
           CodeConstants.opc_l2d, CodeConstants.opc_lastore, CodeConstants.opc_pop,
           CodeConstants.opc_pop2, CodeConstants.opc_athrow, CodeConstants.opc_putfield,
           CodeConstants.opc_putstatic:
        return true;
      case CodeConstants.opc_invokevirtual, CodeConstants.opc_invokespecial,
           CodeConstants.opc_invokestatic, CodeConstants.opc_invokeinterface,
           CodeConstants.opc_invokedynamic:
        // A call with parameters may be consuming this value as one of its arguments; only a
        // parameterless call leaves it on the stack.
        PooledConstant constant = cls.getPool().getConstant(insn.operand(0));
        return !(constant instanceof LinkConstant link) || link.descriptor == null
          || !link.descriptor.startsWith("()");
      default:
        return false;
    }
  }

  /**
   * The text range a naming site that interns pool entry {@code index} must fall in.
   *
   * <p>The class was entered into the pool at that site, so the site lies after the last use of a
   * lower-index entry and before the first use of a higher-index one, both taken in generation
   * order. Uses without a printed position (folded constants, initializers) cannot bracket anything
   * and are skipped rather than failing the window. Both bounds are widened to the whole printed
   * line, because a line is the finest text unit the printer proves.
   */
  /**
   * Whether pool entry {@code index} is the first entry and was interned before any instruction
   * output, with no reference beside it that could have created it as an operand.
   *
   * <p>javac visits the fields before it generates any method body; a folded constant naming in a
   * field initializer interns the owner's {@code Class} entry there. Nothing else produces a pool
   * where the owner's Class entry leads and every instruction-referenced entry follows, while no
   * nearby reference names the owner; the class's own, superclass and interface entries are
   * entered as the class is, so they never count.
   */
  private static boolean opensPool(StructClass cls, int index, Set<Integer> setup,
                                   Map<Integer, FirstUse> uses) {
    if (index != 1 || setup.contains(index)) {
      return false;
    }
    for (int key : uses.keySet()) {
      if (key < index) {
        return false; // an instruction already references an entry, so the class was generating
      }
    }
    List<PooledConstant> pool = cls.getPool().getPool();
    if (!(pool.get(index) instanceof PrimitiveConstant primitive) || primitive.getString() == null) {
      return false;
    }
    String owner = primitive.getString();
    for (int i = index + 1; i < Math.min(pool.size(), index + 5); i++) {
      if (pool.get(i) instanceof LinkConstant link && owner.equals(link.classname)) {
        return false; // the Class entry is the reference's operand, not a naming
      }
    }
    return true;
  }

  /** Whether the class file names itself in its own {@code InnerClasses} attribute. */
  private static boolean nested(StructClass own) {
    StructInnerClassesAttribute inner = own.getAttribute(StructGeneralAttribute.ATTRIBUTE_INNER_CLASSES);
    if (inner == null) {
      return false;
    }
    for (StructInnerClassesAttribute.Entry entry : inner.getEntries()) {
      if (own.qualifiedName.equals(entry.innerName)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The owners whose {@code Class} entry the pool holds before any generated code.
   *
   * <p>A protected constant of a superclass in another package, and an unqualified constant of the
   * enclosing class, are resolved while the class's names are resolved: javac enters the owner's
   * {@code Class} then, ahead of every entry the code generation later creates. The entry cannot be
   * a reference's operand (that would be entered with the reference) and cannot be the class's own
   * or its superclass's setup entry.
   */
  private static Set<String> earlyOwners(StructClass own, Map<String, Integer> classIndices,
                                         Set<Integer> setup, Map<Integer, FirstUse> firstUses) {
    Set<String> owners = new HashSet<>();
    int firstReferenced = Integer.MAX_VALUE;
    for (int key : firstUses.keySet()) {
      firstReferenced = Math.min(firstReferenced, key);
    }
    if (firstReferenced == Integer.MAX_VALUE) {
      return owners; // no generated code, so nothing proves an early entry
    }
    String nest = nestOf(own.qualifiedName);
    String packageName = packageOf(own.qualifiedName);
    List<PooledConstant> pool = own.getPool().getPool();
    for (Map.Entry<String, Integer> entry : classIndices.entrySet()) {
      int index = entry.getValue();
      String owner = entry.getKey();
      if (index >= firstReferenced || setup.contains(index) || owner.equals(own.qualifiedName)) {
        continue;
      }
      // Only two kinds of name are resolved before any generated code: the enclosing class's,
      // written unqualified, and a protected constant of a superclass in another package. Any
      // other early entry is entered for a reason the pool does not record here.
      boolean enclosing = own.qualifiedName.startsWith(owner + "$");
      boolean remoteSuper = !packageName.equals(packageOf(owner)) && extendsClass(nest, owner);
      if (!enclosing && !remoteSuper) {
        continue;
      }
      boolean operand = false;
      for (int i = index + 1; i < Math.min(pool.size(), index + 5); i++) {
        if (pool.get(i) instanceof LinkConstant link && owner.equals(link.classname)) {
          operand = true;
          break;
        }
      }
      if (!operand) {
        owners.add(owner);
      }
    }
    return owners;
  }

  private static int[] window(String text, StructClass cls, int index,
                              List<Map.Entry<Integer, FirstUse>> ordered,
                              Map<Pair<String, String>, Map<Integer, Integer>> positions,
                              boolean requireBoth) {
    FirstUse succ = null;
    Integer succPosition = null;
    for (Map.Entry<Integer, FirstUse> entry : ordered) {
      if (entry.getKey() > index) {
        Integer p = position(cls, entry.getValue(), positions);
        if (p != null) {
          succ = entry.getValue();
          succPosition = p;
          break;
        }
      }
    }
    FirstUse pred = null;
    Integer predPosition = null;
    for (int i = ordered.size() - 1; i >= 0; i--) {
      Map.Entry<Integer, FirstUse> entry = ordered.get(i);
      if (entry.getKey() >= index) {
        continue;
      }
      if (succ != null && compare(entry.getValue(), succ) >= 0) {
        continue; // generated after the upper bound, so not a lower bound
      }
      Integer p = position(cls, entry.getValue(), positions);
      if (p != null) {
        pred = entry.getValue();
        predPosition = p;
        break;
      }
    }
    if (requireBoth && (predPosition == null || succPosition == null)) {
      return null;
    }
    if (predPosition == null && succPosition == null) {
      return null;
    }
    int from = predPosition == null ? 0 : lineStart(text, predPosition);
    int to = succPosition == null ? text.length() : lineEnd(text, succPosition);
    if (from > to) {
      return null; // the text order contradicts the pool order; no window is provable
    }
    return new int[]{from, to};
  }

  /**
   * The text before the first reference that names an owner whose {@code Class} entry the pool
   * entered earlier, or null when the entry is not provably earlier.
   *
   * <p>javac enters a reference's Class as that reference is generated, so a Class entry below its
   * first reference was entered by something else before it -- in this file, a folded constant
   * naming. That naming precedes the reference in text order; the window extends from the start of
   * the class to the end of the reference's line.
   */
  private static int[] beforeReferenceWindow(String text, StructClass cls, int classIndex,
                                             Map<Integer, FirstUse> firstUses,
                                             Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    String owner = cls.getPool().getPool().get(classIndex) instanceof PrimitiveConstant primitive
      ? primitive.getString() : null;
    if (owner == null) {
      return null;
    }
    List<PooledConstant> pool = cls.getPool().getPool();
    int linkIndex = -1;
    for (int i = 1; i < pool.size(); i++) {
      if (pool.get(i) instanceof LinkConstant link && owner.equals(link.classname)) {
        linkIndex = i;
        break;
      }
    }
    if (linkIndex < 0 || linkIndex <= classIndex) {
      return null;
    }
    FirstUse use = firstUses.get(linkIndex);
    Integer printed = position(cls, use, positions);
    if (printed == null) {
      return null;
    }
    // The naming that entered the Class just before this reference was evaluated in the same
    // method, after the method began: the arguments of a call are generated there, not in the
    // class body. A site in another method would move the entry to that method's own point.
    int from = 0;
    for (SiteSpace space : spaces(cls, positions)) {
      if (space.key().equals(use.methodKey())) {
        from = space.min();
        break;
      }
    }
    if (from > printed) {
      return null;
    }
    return new int[]{from, lineEnd(text, printed)};
  }

  private static Integer position(StructClass cls, FirstUse use,
                                  Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    if (use == null) {
      return null;
    }
    Map<Integer, Integer> method = positions.get(Pair.of(cls.qualifiedName, use.methodKey()));
    if (method != null && method.containsKey(use.offset())) {
      return method.get(use.offset());
    }
    // A field initializer is printed at its declaration but generated inside <clinit> or a
    // constructor, and the printer records its positions under a field-initializer key rather
    // than the generating method's. The initializer's offsets all come from one constructor, so
    // the map belongs to a use only when that constructor's code contains every one of them;
    // a coincident offset in some unrelated method's buffer then cannot place anything.
    Integer lifted = liftedPosition(cls, use, positions);
    if (lifted != null) {
      return lifted;
    }
    return method == null ? null : method.get(use.offset());
  }

  /** The printed position of a use generated into a lifted field initializer, or null. */
  private static Integer liftedPosition(StructClass cls, FirstUse use,
                                        Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    if (!use.methodKey().startsWith(CodeConstants.INIT_NAME + " ")
        && !use.methodKey().startsWith(CodeConstants.CLINIT_NAME + " ")) {
      return null;
    }
    StructMethod method = cls.getMethod(use.methodKey());
    if (method == null) {
      return null;
    }
    if (method.getInstructionSequence() == null) {
      try {
        method.expandData(cls);
      }
      catch (Exception e) {
        return null;
      }
    }
    FullInstructionSequence code = method.getInstructionSequence();
    if (code == null) {
      return null;
    }
    for (Map.Entry<Pair<String, String>, Map<Integer, Integer>> entry : positions.entrySet()) {
      if (!cls.qualifiedName.equals(entry.getKey().a)
          || !entry.getKey().b.startsWith("<field-init ")
          || !entry.getValue().containsKey(use.offset())) {
        continue;
      }
      if (containsOffsets(code, entry.getValue().keySet())) {
        return entry.getValue().get(use.offset());
      }
    }
    return null;
  }

  private static boolean containsOffsets(FullInstructionSequence code, Set<Integer> offsets) {
    Set<Integer> remaining = new HashSet<>(offsets);
    for (Instruction instruction : code) {
      // The tracer records operand bytes as well as instruction starts, so an offset is inside
      // the method when any instruction covers it.
      for (int offset = instruction.startOffset; offset < instruction.startOffset + instruction.length; offset++) {
        remaining.remove(offset);
      }
      if (remaining.isEmpty()) {
        return true;
      }
    }
    return remaining.isEmpty();
  }

  /**
   * A folded-constant naming the pool records as a free-standing Class+name pair.
   *
   * <p>{@code open}/{@code close} are the argument list of the call the pair precedes; a field
   * reference has no argument list and stores -1 in both, leaving the generation-order gap between
   * {@code lower} and {@code successor} to place the site. {@code successorAt} is the character
   * position the successor's first use was printed at, or -1; a value successor printed inside a
   * field initializer places its naming at the literal in that same initializer.
   */
  private record PairSite(int classIndex, long successor, long lower, long after, int open, int close,
                          String member, String successorKey, Set<String> pooled, int successorAt,
                          int lowerAt, int nextClass) {
    /** Whether naming a constant of this value enters no pool entry the original did not have. */
    boolean valueAvailable(String key) {
      if (key.equals(successorKey)) {
        return true; // the naming entered this very value; the pair's neighbour is it
      }
      if (key.startsWith(VariableType.BOOLEAN.name() + "|")) {
        return true; // a boolean folds to an immediate
      }
      try {
        if (key.startsWith(VariableType.INT.name() + "|")) {
          long value = Long.parseLong(key.substring(VariableType.INT.name().length() + 1));
          return (value >= Short.MIN_VALUE && value <= Short.MAX_VALUE) || pooled.contains(key);
        }
        if (key.startsWith(VariableType.CHAR.name() + "|")) {
          long value = Long.parseLong(key.substring(VariableType.CHAR.name().length() + 1));
          return (value >= 0 && value <= Short.MAX_VALUE) || pooled.contains(key);
        }
      }
      catch (NumberFormatException e) {
        return false;
      }
      return pooled.contains(key);
    }
  }

  /**
   * The owners the pool records as named by a folded constant in an argument list.
   *
   * <p>javac enters a named folded constant's owner as a bare {@code Class} entry with its name,
   * then whatever entry it creates next. An owner no instruction uses and no attribute explains
   * can only have been named by a constant; a name written in a method body is entered while the
   * code around it is generated, and javac's attribute writers run after all code. So when the
   * entry right after the pair is a reference the generation enters at one instruction, the pair
   * was entered by a naming immediately before that instruction, inside its argument list.
   */
  private static Map<String, PairSite> pairSites(StructClass cls, String text,
                                                 Map<Integer, FirstUse> firstUses,
                                                 Set<String> catchTypes,
                                                 Set<Integer> setup, Set<Integer> early,
                                                 Map<Pair<String, String>, Map<Integer, Integer>> positions,
                                                 boolean ownProven) {
    Map<String, PairSite> pairs = new HashMap<>();
    List<PooledConstant> pool = cls.getPool().getPool();
    Map<String, Integer> indices = classIndices(cls);
    int writeStart = attributeStart(cls);
    Integer ownIndex = indices.get(cls.qualifiedName);
    // An own entry directly after another naming's pair is the continuation of that expression
    // (`Other.X + Own.Y` or `Own.Nested.X`), so the own pair records a naming even though the
    // same Class entry is also what `this_class` and any `Own.class` literal use.
    boolean ownChain = ownIndex != null && ownIndex < writeStart && ownIndex - 2 >= 1
      && anotherNaming(pool, ownIndex - 2);
    for (int i = 1; i + 2 < pool.size(); i++) {
      if (!(pool.get(i) instanceof PrimitiveConstant entry)
          || entry.type != CodeConstants.CONSTANT_Class
          || entry.getString() == null || entry.index != i + 1) {
        continue;
      }
      String owner = entry.getString();
      // The class's own entry is `this_class`'s unless the pool proves it was interned before the
      // attribute data existed: then a folded naming of one of the class's own constants created
      // it, and a pair there records that naming like any other.
      boolean ownNaming = owner.equals(cls.qualifiedName) && i < writeStart
        && (ownProven || ownChain);
      if (catchTypes.contains(owner) || (setup.contains(i) && !ownNaming)
          || (owner.equals(cls.qualifiedName) && !ownNaming)) {
        continue; // the class is entered as itself, a catch type or a class-setup entry
      }
      boolean call = false;
      String member = null;
      String methodName = null;
      LinkConstant link = pool.get(i + 2) instanceof LinkConstant value ? value : null;
      if (link != null) {
        call = link.type == CodeConstants.CONSTANT_Methodref
          || link.type == CodeConstants.CONSTANT_InterfaceMethodref;
        boolean field = link.type == CodeConstants.CONSTANT_Fieldref;
        if (!call && !field) {
          continue; // the entry after the pair is neither a call nor a field reference
        }
        if (owner.equals(link.classname) && firstUses.get(i) != null
            && firstUses.get(i + 2) != null
            && compare(firstUses.get(i), firstUses.get(i + 2)) <= 0) {
          continue; // the class is used directly before this reference, so a naming proves nothing
        }
        member = field ? link.elementname : null;
        methodName = call ? link.elementname : null;
      }
      // Any other entry after the pair is the next entry the generation created: the naming that
      // entered the pair was the last pool-entering event before it, so a site in the generation
      // gap between the neighbouring entries' first uses reproduces the same order.
      FirstUse use;
      long point;
      if (anotherNaming(pool, i + 2)) {
        // The entry after the pair is another naming's Class entry. Its own first use may come
        // later (a `Own.class` literal, or the class's own entry reused by `this_class`), and it
        // does not bound this naming: the pool still says this pair precedes the next naming, so
        // the first higher entry an instruction uses is the upper bound on the generation point
        // the naming occupies, and the pair is placed from that generation gap.
        long[] until = pairBounds(cls, firstUses, i, early, indices);
        if (until[1] == Long.MAX_VALUE) {
          continue;
        }
        point = until[1];
        FirstUse successorUse = null;
        for (FirstUse candidate : firstUses.values()) {
          if (coordinate(candidate.order(), candidate.offset()) == point) {
            successorUse = candidate;
            break;
          }
        }
        use = successorUse;
        if (use == null) {
          continue;
        }
      }
      else {
        use = firstUses.get(i + 2);
        if (use == null) {
          continue;
        }
        point = coordinate(use.order(), use.offset());
      }
      // A direct instruction use of the owner's Class entry (new, checkcast, an array type) says
      // the entry already existed when that instruction was generated. The pool puts the entry
      // before this reference, so only a direct use after the reference leaves the pair as the
      // entry's origin: a naming in the reference's argument list, or in the expression whose
      // value the field access stores. An earlier one would explain the entry, and the pair would
      // prove nothing.
      FirstUse direct = firstUses.get(i);
      if (direct != null && coordinate(direct.order(), direct.offset()) <= point) {
        continue;
      }
      long[] bounds = pairBounds(cls, firstUses, i, early, indices);
      if (bounds[1] != point) {
        continue; // a higher entry was created before this reference; the pair is not its naming
      }
      int open = -1;
      int close = -1;
      if (call) {
        // A constructor call's invoke offset is never printed: the `new` expression's buffer maps
        // no bytecode at all. The pair is still usable through the generation gap between the
        // neighbouring entries' first uses, so a missing position leaves the parens unknown
        // rather than dropping the pair.
        Integer printed = position(cls, use, positions);
        if (printed != null) {
          int found = nextOpenParen(text, printed);
          if (found < 0) {
            // An autoboxing call's recorded position sits at the boxed value, inside the argument
            // list, so the call's own parenthesis is the nearest unmatched one to its left.
            found = enclosingParen(text, printed);
          }
          int end = found < 0 ? -1 : matchingParen(text, found);
          if (found >= 0 && end >= 0) {
            open = found;
            close = end;
          }
        }
      }
      if (call && open < 0 && !CodeConstants.INIT_NAME.equals(methodName)) {
        // A call whose invoke was never printed cannot place a site, and recording the pair would
        // keep the window rules from placing one through the deferred fallback. Constructor calls
        // are the exception: their argument list is bounded by the new instruction and the invoke.
        continue;
      }
      String successorKey = pool.get(i + 2) instanceof PrimitiveConstant pv ? valueKey(pv) : null;
      // A pair whose Class entry directly follows another naming's pair belongs to that one
      // expression, so its folded value is the whole expression's, not this owner's own constant.
      boolean continuation = i - 2 >= 1 && anotherNaming(pool, i - 2);
      if (successorKey != null && successorKey.startsWith(VariableType.STRING.name() + "|")
          && !continuation && !ownerDeclares(owner, successorKey)
          && !ownerTilesString(owner, successorKey)) {
        // A numeric value after the pair may be the fold of an expression over the owner's
        // constants, so it can never be refuted. A string cannot be built from an int constant,
        // and a string value no constant of the owner holds is not the value the naming folded to:
        // the naming entered nothing and the next entry belongs to whatever was entered next. The
        // naming was still the last pool-entering event before it, so the pair's generation gap
        // places the site exactly as a reference successor's does.
        successorKey = null;
      }
      Integer at = position(cls, use, positions);
      Integer lowerAt = position(cls, lastPoolUseEntry(firstUses, use), positions);
      // A pair whose successor is another naming's Class entry records that the two names were
      // written in one expression, in pool order: the source named this owner, then the next.
      int nextClass = anotherNaming(pool, i + 2) ? i + 2 : -1;
      pairs.putIfAbsent(owner, new PairSite(i, point, bounds[0], lastPoolUse(firstUses, use),
        open, close, member, successorKey, pooledKeys(cls, i), at == null ? -1 : at,
        lowerAt == null ? -1 : lowerAt, nextClass));
    }
    return pairs;
  }

  /**
   * Whether one of the owner's string constants is a segment of this pooled value.
   *
   * <p>A concatenation's folded value contains each named constant verbatim, so a string value one
   * of the owner's constants sits inside is not refuted by the owner's declaration alone.
   */
  private static boolean ownerTilesString(String owner, String key) {
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return true; // an owner off the classpath cannot be refuted
    }
    String value = key.substring(VariableType.STRING.name().length() + 1);
    return tilesString(cls, value, 0);
  }

  private static boolean tilesString(StructClass cls, String value, int depth) {
    if (cls == null || depth > 8) {
      return false;
    }
    for (StructField field : cls.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      PrimitiveConstant constant = constantValue(cls, field);
      if (constant != null && constant.value instanceof String text && !text.isEmpty()
          && value.contains(text)) {
        return true;
      }
    }
    String superName = cls.superClass == null ? null : cls.superClass.getString();
    return superName != null
      && tilesString(DecompilerContext.getStructContext().getClass(superName), value, depth + 1);
  }

  /** Whether the pool entry is a {@code Class} entry followed by its own name: another naming. */
  private static boolean anotherNaming(List<PooledConstant> pool, int index) {
    if (index + 1 >= pool.size()) {
      return false;
    }
    if (!(pool.get(index) instanceof PrimitiveConstant entry)
        || entry.type != CodeConstants.CONSTANT_Class || entry.getString() == null
        || entry.index != index + 1) {
      return false;
    }
    return pool.get(index + 1) instanceof PrimitiveConstant name
      && name.type == CodeConstants.CONSTANT_Utf8;
  }

  /**
   * The generation-order bounds of a pair's naming site, read from the pool.
   *
   * <p>The same bracket as {@link #coordinates}, except that a {@code Class} entry entered as a
   * reference's operand is bounded by that reference's first use: the operand is numbered after
   * the reference and enters the pool with it, so the reference's instruction is the operand's
   * entry point even when the class's own first instruction use lies in a later method. Without
   * the cap a lower entry first used after the pair would put the bound past a site the pool
   * still admits.
   */
  private static long[] pairBounds(StructClass cls, Map<Integer, FirstUse> firstUses, int index,
                                   Set<Integer> early, Map<String, Integer> classIndices) {
    Map<Integer, Long> upper = new HashMap<>();
    long succ = Long.MAX_VALUE;
    for (Map.Entry<Integer, FirstUse> entry : firstUses.entrySet()) {
      int key = entry.getKey();
      if (key == index || early.contains(key)) {
        continue;
      }
      long point = coordinate(entry.getValue().order(), entry.getValue().offset());
      if (key < index) {
        upper.put(key, point);
      }
      else {
        succ = Math.min(succ, point);
      }
    }
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = 1; i < pool.size(); i++) {
      if (!(pool.get(i) instanceof LinkConstant link) || link.classname == null) {
        continue;
      }
      Integer operand = classIndices.get(link.classname);
      FirstUse use = firstUses.get(i);
      if (operand == null || use == null || operand >= index || i >= operand
          || early.contains(operand)) {
        continue;
      }
      upper.merge(operand, coordinate(use.order(), use.offset()), Math::min);
    }
    long pred = Long.MIN_VALUE;
    for (long point : upper.values()) {
      pred = Math.max(pred, point);
    }
    return new long[]{pred, succ};
  }

  /**
   * Whether the owner declares (or inherits) a constant whose folded value is this pool value key.
   *
   * <p>A string value no constant of the owner holds cannot be the value the naming entered, so the
   * pair must be read as a bare Class+name pair. An owner whose class file is not on this run's
   * classpath keeps the value reading; nothing can refute it.
   */
  private static boolean ownerDeclares(String owner, String successorKey) {
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return true;
    }
    if (declares(cls, successorKey)) {
      return true;
    }
    for (InheritedConstant inherited : inheritedConstants(cls)) {
      if (inheritedKey(inherited).equals(successorKey)) {
        return true;
      }
    }
    return false;
  }

  private static boolean declares(StructClass cls, String key) {
    for (StructField field : cls.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      StructConstantValueAttribute attribute =
        field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
      if (attribute == null) {
        continue;
      }
      PrimitiveConstant value = cls.getPool().getPrimitiveConstant(attribute.getIndex());
      VariableType kind = kind(field.getDescriptor());
      if (value == null || value.value == null || kind == null) {
        continue;
      }
      String printed = kind == VariableType.BOOLEAN && value.value instanceof Integer flag
        ? Boolean.toString(flag != 0) : String.valueOf(value.value);
      if ((kind + "|" + printed).equals(key)) {
        return true;
      }
    }
    return false;
  }

  private static String inheritedKey(InheritedConstant inherited) {
    return inherited.kind() + "|" + inherited.printed();
  }

  /**
   * The generation point of the last pool entry first used before the reference in its method, or
   * {@link #NO_COORDINATE}.
   *
   * <p>The pair sits immediately before its successor in the pool, so the source named the constant
   * after that successor's predecessors were all created and before any later entry was. Nothing
   * can have been entered between the naming and the reference; a site printed before an earlier
   * entry's first use would create its own entry after the pair instead and reorder the pool.
   */
  private static long lastPoolUse(Map<Integer, FirstUse> firstUses, FirstUse successor) {
    FirstUse entry = lastPoolUseEntry(firstUses, successor);
    return entry == null ? NO_COORDINATE : coordinate(entry.order(), entry.offset());
  }

  /** The last pool entry first used before the reference in its method, or null when none is. */
  private static FirstUse lastPoolUseEntry(Map<Integer, FirstUse> firstUses, FirstUse successor) {
    FirstUse last = null;
    for (FirstUse use : firstUses.values()) {
      if (use.order() != successor.order() || use.offset() >= successor.offset()) {
        continue;
      }
      if (last == null || compare(use, last) > 0) {
        last = use;
      }
    }
    return last;
  }

  /** The first '(' printed after this position that belongs to a call on the same statement. */
  private static int nextOpenParen(String text, int from) {
    int limit = Math.min(text.length(), Math.max(0, from) + 200);
    for (int i = Math.max(0, from); i < limit; i++) {
      char c = text.charAt(i);
      if (c == '(') {
        return i;
      }
      // A static field initializer prints its invoke at the assignment: the position the tracer
      // recorded points at the '=', and the call being named is the initializer's own right-hand
      // side. Crossing the '=' stays inside one statement; the statement's other boundaries
      // still end the search.
      if (c == ';' || c == '{' || c == '}' || c == '\n') {
        return -1;
      }
      if (c == '"' || c == '\'') {
        i = skipQuoted(text, i, c) - 1;
      }
      else if (c == '/' && i + 1 < text.length()) {
        char next = text.charAt(i + 1);
        if (next == '/') {
          return -1;
        }
        if (next == '*') {
          int end = text.indexOf("*/", i + 2);
          if (end < 0) {
            return -1;
          }
          i = end + 1;
        }
      }
    }
    return -1;
  }

  /**
   * The nearest unmatched '(' to the left of this position on the same statement, or -1.
   *
   * <p>The printer records a call's position at the buffer the call is printed from; for an
   * autoboxing conversion that buffer is the boxed value, one level inside the argument list, so
   * the call's own parenthesis is the last '(' whose group has not been closed by the time the scan
   * reaches it. A quote before the position makes the scan give up rather than guess.
   */
  private static int enclosingParen(String text, int from) {
    int depth = 0;
    for (int i = Math.min(from, text.length()) - 1; i >= 0 && i >= from - 400; i--) {
      char c = text.charAt(i);
      if (c == ')' || c == ']') {
        depth++;
      }
      else if (c == '(') {
        if (depth == 0) {
          return i;
        }
        depth--;
      }
      else if (c == '\n' || c == ';' || c == '{' || c == '}' || c == '"' || c == '\'') {
        return -1;
      }
    }
    return -1;
  }

  /** The ')' closing the '(' at {@code open}, skipping text inside literals and comments. */
  private static int matchingParen(String text, int open) {
    int depth = 0;
    for (int i = open; i < text.length(); i++) {
      char c = text.charAt(i);
      if (c == '"' || c == '\'') {
        i = skipQuoted(text, i, c) - 1;
        continue;
      }
      if (c == '/' && i + 1 < text.length()) {
        char next = text.charAt(i + 1);
        if (next == '/') {
          int end = text.indexOf('\n', i);
          if (end < 0) {
            return -1;
          }
          i = end;
          continue;
        }
        if (next == '*') {
          int end = text.indexOf("*/", i + 2);
          if (end < 0) {
            return -1;
          }
          i = end + 1;
          continue;
        }
      }
      if (c == '(') {
        depth++;
      }
      else if (c == ')') {
        depth--;
        if (depth == 0) {
          return i;
        }
      }
    }
    return -1;
  }

  /** A folded-constant naming whose value the pool entered right after the Class and name. */
  private record ValueSite(int classIndex, long naming, String poolKey) {
    /** Whether this literal would fold to the very value the pool entered with the pair. */
    boolean accepts(String key) {
      if (key.equals(poolKey)) {
        return true;
      }
      // A char constant folds to the same int value; javac enters the same Integer entry.
      return poolKey.startsWith(VariableType.INT.name() + "|")
        && key.startsWith(VariableType.CHAR.name() + "|")
        && key.substring(key.indexOf('|') + 1).equals(poolKey.substring(poolKey.indexOf('|') + 1));
    }
  }

  /**
   * The owners whose Class pair the pool follows with the folded value it entered there.
   *
   * <p>When the source names a folded constant whose value the pool does not hold yet, javac
   * enters the Class, its name and that value, in that order. The value's first instruction use is
   * then the literal the name folded to, so the pool records the naming's exact generation point.
   * An owner no instruction uses and no attribute explains is the only kind a naming enters;
   * a value an equal entry already covers would have been reused, and its pair would not precede
   * it, so those are skipped too.
   */
  private static Map<String, ValueSite> valueSites(StructClass cls,
                                                   Map<Integer, FirstUse> firstUses,
                                                   Set<String> catchTypes, Set<Integer> setup,
                                                   Set<Integer> early,
                                                   Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    Map<String, ValueSite> sites = new HashMap<>();
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = 1; i + 2 < pool.size(); i++) {
      if (!(pool.get(i) instanceof PrimitiveConstant entry)
          || entry.type != CodeConstants.CONSTANT_Class
          || entry.getString() == null || entry.index != i + 1) {
        continue;
      }
      String owner = entry.getString();
      if (owner.equals(cls.qualifiedName) || setup.contains(i) || catchTypes.contains(owner)
          || hasEarlierEqual(cls, i + 2)) {
        continue;
      }
      if (!(pool.get(i + 2) instanceof PrimitiveConstant value) || value.value == null) {
        continue;
      }
      VariableType kind = switch (value.type) {
        case CodeConstants.CONSTANT_Integer -> VariableType.INT;
        case CodeConstants.CONSTANT_Long -> VariableType.LONG;
        case CodeConstants.CONSTANT_Float -> VariableType.FLOAT;
        case CodeConstants.CONSTANT_Double -> VariableType.DOUBLE;
        case CodeConstants.CONSTANT_String -> VariableType.STRING;
        default -> null;
      };
      if (kind == null) {
        continue;
      }
      FirstUse use = firstUses.get(i + 2);
      if (use == null || position(cls, use, positions) == null) {
        continue;
      }
      FirstUse direct = firstUses.get(i);
      if (direct != null
          && coordinate(direct.order(), direct.offset()) <= coordinate(use.order(), use.offset())) {
        continue; // an earlier instruction explains the Class entry; the triplet proves nothing
      }
      sites.putIfAbsent(owner, new ValueSite(i, coordinate(use.order(), use.offset()),
        kind + "|" + value.value));
    }
    return sites;
  }

  /**
   * The literal keys whose values the pool already holds below {@code classIndex}.
   *
   * <p>A naming enters the folded value right after the Class and name unless an equal value is
   * already in the pool. Reproducing the naming at a site whose value is not there would insert
   * it in front of the pair, so such a site cannot be the original's.
   */
  private static Set<String> pooledKeys(StructClass cls, int classIndex) {
    Set<String> keys = new HashSet<>();
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = 1; i < classIndex && i < pool.size(); i++) {
      if (!(pool.get(i) instanceof PrimitiveConstant primitive) || primitive.value == null) {
        continue;
      }
      switch (primitive.type) {
        case CodeConstants.CONSTANT_Integer -> {
          keys.add(VariableType.INT.name() + "|" + primitive.value);
          keys.add(VariableType.CHAR.name() + "|" + primitive.value);
        }
        case CodeConstants.CONSTANT_Long -> keys.add(VariableType.LONG.name() + "|" + primitive.value);
        case CodeConstants.CONSTANT_Float -> keys.add(VariableType.FLOAT.name() + "|" + primitive.value);
        case CodeConstants.CONSTANT_Double -> keys.add(VariableType.DOUBLE.name() + "|" + primitive.value);
        case CodeConstants.CONSTANT_String -> keys.add(VariableType.STRING.name() + "|" + primitive.value);
        default -> {
        }
      }
    }
    return keys;
  }

  private static int lineStart(String text, int position) {
    int newline = position <= 0 ? -1 : text.lastIndexOf('\n', position - 1);
    return newline < 0 ? 0 : newline + 1;
  }

  private static int lineEnd(String text, int position) {
    int newline = text.indexOf('\n', Math.max(0, position));
    return newline < 0 ? text.length() : newline + 1;
  }

  /**
   * Scans one class's own text. A site outside the pool-order window of its owner is held back;
   * when an owner's window turns out to contain no site at all, the window was too narrow (a bound
   * may have been placed in the wrong text order) and that owner's sites are allowed again, except
   * where the generation order contradicts them: a site whose printed position lies outside the
   * pool-order bounds is not where the owner's Class entry can have been entered.
   */
  /** Whether a placed site lies earlier in the generation order than another placeable one. */
  private static boolean before(Site site, Site other, Placement placement) {
    long a = siteCoordinate(placement.spaces(), site.start());
    long b = siteCoordinate(placement.spaces(), other.start());
    return a != NO_COORDINATE && b != NO_COORDINATE && a < b;
  }

  /** Whether a literal site opens with a quote, whose content the printer's mapping covers. */
  private static boolean quoted(String text, int position) {
    return position >= 0 && position < text.length()
      && (text.charAt(position) == '"' || text.charAt(position) == '\'');
  }

  private static void scanClass(String text, List<int[]> spans, Rules rules, List<Site> sites) {
    // A run of naming pairs is one folded expression over several owners, and the pool records
    // only its owner order. It is solved before the single-pair rules so no one of its owners is
    // placed on its own.
    Set<String> chained = chainSites(text, spans, rules, sites);
    Map<String, List<Site>> deferred = new HashMap<>();
    // Sites the expression solver invented: it admits any literal of a reference successor's
    // generation gap, so a direct naming found later in the same gap withdraws the guess.
    Map<String, List<Site>> invented = new HashMap<>();
    Set<String> inWindow = new HashSet<>();
    for (int[] span : spans) {
      scan(text, span[0], span[1], rules.candidates(), rules.imports(), rules.packageName(),
        sites, rules.own(), rules.ownInitializers(), rules.placement(), deferred, inWindow,
        invented);
    }
    // The pool's own records place a site exactly, so they are tried before the printed-line
    // windows. A record that finds no site leaves the owner to the window rules below.
    if (rules.placement().values() != null) {
      for (Map.Entry<String, ValueSite> entry : rules.placement().values().entrySet()) {
        ValueSite valueSite = entry.getValue();
        if (hasSiteFor(sites, entry.getKey())) {
          continue;
        }
        List<Site> candidates = deferred.get(entry.getKey());
        if (candidates == null) {
          continue;
        }
        for (Site site : candidates) {
          // The value's first use is the literal itself, so the site must sit at that very point.
          if (siteCoordinate(rules.placement().spaces(), site.start()) == valueSite.naming()) {
            addSiteOnce(sites, site);
            break;
          }
        }
      }
    }
    if (rules.placement().pairs() != null) {
      for (Map.Entry<String, PairSite> entry : rules.placement().pairs().entrySet()) {
        PairSite pair = entry.getValue();
        if (hasSiteFor(sites, entry.getKey()) || chained.contains(entry.getKey())) {
          continue; // one naming per class reproduces the pair; later names enter nothing
        }
        List<Site> candidates = deferred.get(entry.getKey());
        if (candidates == null) {
          continue;
        }
        Site best = null;
        Site fieldBest = null;
        int fieldMatches = 0;
        long bestCoordinate = NO_COORDINATE;
        for (Site site : candidates) {
          boolean inArgs = pair.open() >= 0 && site.start() > pair.open()
            && site.start() < pair.close();
          // A quoted literal's recorded position sits one past its opening quote (the printer
          // maps the buffer's content, not the quote it adds): the point a string or char naming
          // occupies is that recorded position, exactly as the scan's own anchor rule reads it.
          int anchor = quoted(text, site.start()) ? site.start() + 1 : site.start();
          long coordinate = siteCoordinate(rules.placement().spaces(), anchor);
          if (coordinate == NO_COORDINATE) {
            // A field initializer's folded literal is printed in the class body, where the
            // printer maps no instruction point for it. The field reference right after the pair
            // names the field, and that field's own initializer is the only place the literal
            // can sit: its <field-init> line is the site the pool orders.
            if (pair.open() < 0 && fieldInitializerSite(text, rules.placement().spaces(),
                site.start(), pair)) {
              fieldBest = site;
              fieldMatches++;
            }
            else if (pair.successorKey() != null && pairedInitializer(text,
                rules.placement().spaces(), rules.placement().spans(), site.start(),
                pair.successorAt())) {
              // The successor is the folded value the naming entered, and its printed point is
              // this very initializer: the literal here is the naming that entered it.
              fieldBest = site;
              fieldMatches++;
            }
            continue;
          }
          boolean sameRank = (coordinate >>> 32) == (pair.successor() >>> 32);
          if (pair.successorKey() == null && sameRank && pair.after() != NO_COORDINATE
              && coordinate <= pair.after()) {
            continue; // an entry the pair precedes was used between this site and the reference
          }
          long offset = coordinate & 0xffffffffL;
          long successorOffset = pair.successor() & 0xffffffffL;
          // A value successor is the entry the naming itself entered, so the literal's own point
          // is the successor's point; a reference is created after its arguments and needs a
          // strictly earlier site.
          boolean atValue = pair.member() == null && offset == successorOffset;
          boolean atOrBefore = offset < successorOffset || atValue;
          if (sameRank) {
            if (!atOrBefore) {
              continue; // after the reference was generated
            }
            if (pair.open() >= 0 && inArgs) {
              // the naming sits in the call's own argument list, between the pair and the invoke
            }
            else if (!atValue
                && coordinate <= (pair.successorKey() == null ? pair.after() : pair.lower())) {
              continue; // before the previous entry's first use; the naming would move it
            }
          }
          else if (pair.successorKey() != null
              || !(coordinate < pair.successor() && coordinate > pair.lower())) {
            // A value successor lies at the literal's own point, in its own method. A naming in an
            // earlier method can only precede a reference, and only where the interval bound
            // (capped at each operand's reference) stays below it.
            continue;
          }
          if (best == null || coordinate > bestCoordinate) {
            best = site;
            bestCoordinate = coordinate;
          }
        }
        if (best != null) {
          addSiteOnce(sites, best);
        }
        else if (fieldBest != null && fieldMatches == 1) {
          addSiteOnce(sites, fieldBest);
        }
      }
    }
    for (Map.Entry<String, List<Site>> entry : deferred.entrySet()) {
      if (hasSiteFor(sites, entry.getKey())) {
        continue; // the naming is already placed
      }
      if ((rules.placement().pairs() != null && rules.placement().pairs().containsKey(entry.getKey()))
          || (rules.placement().values() != null && rules.placement().values().containsKey(entry.getKey()))) {
        continue; // the pool record is the only evidence of the site; it found none, so place none
      }
      if (!inWindow.contains(entry.getKey())) {
        // A referenced owner's window is the only evidence of where the original named it; without
        // a site inside the window there is nothing to place the name against.
        if (!rules.strict().contains(entry.getKey())
            && !rules.placement().earlyOwners().contains(entry.getKey())) {
          for (Site site : entry.getValue()) {
            if (rules.placement().existsAt(entry.getKey(), site.start())
                && !rules.placement().contradicts(entry.getKey(), site.start())) {
              addSiteOnce(sites, site);
            }
          }
        }
        continue;
      }
      // A site inside the window already interns this owner's Class entry, so naming the owner
      // again later cannot move it and adds nothing to the pool. A site before the window could
      // move the entry earlier than the original did, and stays out.
      int[] window = rules.placement().windows() == null
        ? null : rules.placement().windows().get(entry.getKey());
      for (Site site : entry.getValue()) {
        if (window != null && site.start() >= window[1]) {
          addSiteOnce(sites, site);
        }
      }
    }
    earlySites(text, spans, rules, deferred, sites);
    bareSites(text, spans, rules, sites);
    compositeSites(text, spans, rules, sites);
  }

  /**
   * Names a constant of an owner whose pair has no value or reference successor at all.
   *
   * <p>A {@code Class}+name pair whose next entry is neither a reference nor a value was entered
   * by a folded naming that left no other trace: the constant folded to an immediate (or to a
   * value the pool already held). The literal the source wrote is therefore any literal that one
   * of the owner's constants can reproduce, and the pool order places it between the lower
   * entries' first uses and the higher ones'. Which literal of that value the source used is not
   * recorded and does not matter: naming any constant of the owner enters the same pair.
   */
  private static void bareSites(String text, List<int[]> spans, Rules rules, List<Site> sites) {
    if (!org.jetbrains.java.decompiler.modules.decompiler.RoundTrip.selector("barepairs")) {
      return;
    }
    if (rules.placement().bares().isEmpty() || rules.placement().pairs() == null) {
      return;
    }
    StructClass cls = rules.placement().cls();
    if (cls == null) {
      return;
    }
    List<long[]> literals = intLiterals(text, spans);
    Map<String, Integer> indices = classIndices(cls);
    for (String owner : rules.placement().bares()) {
      if (siteIn(sites, owner, spans) || rules.placement().pairs().containsKey(owner)) {
        continue;
      }
      Integer index = indices.get(owner);
      if (index == null) {
        continue;
      }
      List<SourceConstant> sources = sourceConstants(owner, cls, rules.imports(), rules.packageName());
      if (sources.isEmpty()) {
        continue;
      }
      Set<String> pooledBefore = pooledKeys(cls, index);
      Site found = null;
      for (long[] literal : literals) {
        int start = (int) literal[0];
        long raw = literal[2];
        if (raw < Integer.MIN_VALUE || raw > Integer.MAX_VALUE || hasSiteAt(sites, start)) {
          continue;
        }
        String key = VariableType.INT.name() + "|" + raw;
        if ((!immediateKey(key) && !pooledBefore.contains(key))
            || !rules.placement().provesExactly(owner, start)) {
          continue;
        }
        for (SourceConstant source : sources) {
          if (!numeric(source.kind())) {
            continue;
          }
          String expression = constantExpression(new FieldConstant(null, VariableType.INT, (int) raw),
            source.kind(), source.value(), source.name());
          if (expression == null || !poolFree(expression, pooledBefore)) {
            continue;
          }
          if (source.kind() != VariableType.INT && expression.equals(source.name())) {
            continue; // a bare constant of another kind would change the literal's type
          }
          found = new Site(start, (int) literal[1], "(" + expression + ")", owner);
          break;
        }
        if (found != null) {
          break;
        }
      }
      if (found != null) {
        addSiteOnce(sites, found);
      }
    }
  }

  /** Whether the pair's folded successor is a string value. */
  private static boolean stringSuccessor(PairSite pair) {
    return pair.successorKey() != null
      && pair.successorKey().startsWith(VariableType.STRING.name() + "|");
  }

  /**
   * Whether a chain's naming site lies where the pool order puts it.
   *
   * <p>When the run ends in a folded value, that value's own use is the naming site: the literal
   * occupies exactly that instruction. Otherwise the first pair's generation bracket places the
   * site, as for a single reference successor.
   */
  private static boolean chainProves(PairSite first, PairSite last, String key, int position,
                                     Placement placement) {
    if (last.successorKey() == null) {
      return pairProvesSite(first, key, position, placement);
    }
    if (!key.equals(last.successorKey())) {
      return false;
    }
    // The printer maps a quoted literal's content start, one past the opening quote.
    int anchor = key.startsWith(VariableType.STRING.name() + "|")
      || key.startsWith(VariableType.CHAR.name() + "|") ? position + 1 : position;
    long coordinate = siteCoordinate(placement.spaces(), anchor);
    if (coordinate == NO_COORDINATE) {
      return false;
    }
    long offset = coordinate & 0xffffffffL;
    long successorOffset = last.successor() & 0xffffffffL;
    return (coordinate >>> 32) == (last.successor() >>> 32) && offset == successorOffset
      && coordinate > first.lower();
  }

  /**
   * Names a run of owners whose pairs are adjacent in the pool with one folded expression.
   *
   * <p>When a pair's successor is the next owner's {@code Class}+name pair, the source named the
   * two constants in one expression and the pool recorded the owners in evaluation order. The
   * folded result is a literal at the site (usually an immediate the code pushes), so the literal's
   * value only has to be reproducible by an expression over the run's constants, with the owners
   * named left to right. One such expression reproduces the pair sequence exactly; choosing a
   * different operator or member is byte-equivalent, so the first that folds wins.
   *
   * @return the owners the pass accounted for; their single-pair rules must not run
   */
  private static Set<String> chainSites(String text, List<int[]> spans, Rules rules, List<Site> sites) {
    Map<String, PairSite> pairs = rules.placement().pairs();
    Set<String> claimed = new HashSet<>();
    if (pairs == null || pairs.isEmpty()) {
      return claimed;
    }
    Map<Integer, String> byIndex = new HashMap<>();
    for (Map.Entry<String, PairSite> entry : pairs.entrySet()) {
      byIndex.put(entry.getValue().classIndex(), entry.getKey());
    }
    List<List<String>> runs = new ArrayList<>();
    Set<Integer> continued = new HashSet<>();
    for (Map.Entry<String, PairSite> entry : pairs.entrySet()) {
      PairSite pair = entry.getValue();
      String next = pair.nextClass() < 0 ? null : byIndex.get(pair.nextClass());
      if (next != null) {
        continued.add(pair.nextClass());
      }
    }
    for (Map.Entry<String, PairSite> entry : pairs.entrySet()) {
      if (continued.contains(entry.getValue().classIndex())) {
        continue;
      }
      List<String> run = new ArrayList<>();
      PairSite pair = entry.getValue();
      String owner = entry.getKey();
      while (owner != null && !run.contains(owner)) {
        run.add(owner);
        String next = pair.nextClass() < 0 ? null : byIndex.get(pair.nextClass());
        pair = next == null ? null : pairs.get(next);
        owner = next;
      }
      if (run.size() >= 2 || (run.size() == 1
          && stringSuccessor(pairs.get(run.get(0))))) {
        runs.add(run);
      }
    }
    if (runs.isEmpty()) {
      return claimed;
    }
    StructClass cls = rules.placement().cls();
    if (cls == null) {
      return claimed;
    }
    List<long[]> literals = intLiterals(text, spans);
    for (List<String> run : runs) {
      PairSite first = pairs.get(run.get(0));
      List<List<SourceConstant>> sources = new ArrayList<>();
      boolean writable = true;
      for (String owner : run) {
        List<SourceConstant> constants =
          sourceConstants(owner, cls, rules.imports(), rules.packageName());
        if (constants.isEmpty()) {
          writable = false;
          break;
        }
        sources.add(constants);
      }
      if (!writable) {
        continue;
      }
      Site found = null;
      PairSite last = pairs.get(run.get(run.size() - 1));
      String successorKey = last.successorKey();
      if (successorKey != null
          && successorKey.startsWith(VariableType.STRING.name() + "|")) {
        // A string constant names concatenate into one folded value, which the last pair records
        // as its successor. The pieces between the names are literals of the concatenation; the
        // whole expression is folded at attribution, so they enter nothing.
        String target = successorKey.substring(VariableType.STRING.name().length() + 1);
        String expression = stringChainExpression(target, sources);
        if (expression != null) {
          for (int[] literal : stringLiteralSpans(text, spans, target)) {
            if (hasSiteAt(sites, literal[0])
                || !chainProves(first, last, successorKey, literal[0], rules.placement())) {
              continue;
            }
            found = new Site(literal[0], literal[1], expression, run.get(0));
            break;
          }
        }
      }
      else if (successorKey != null && variableType(
          successorKey.substring(0, successorKey.indexOf('|'))) != null) {
        VariableType kind = variableType(successorKey.substring(0, successorKey.indexOf('|')));
        Object value = kindValue(kind, successorKey);
        if (value != null) {
          Set<String> pooledBefore = pooledKeys(cls, first.classIndex());
          for (int[] literal : literalSpansFor(text, spans, successorKey)) {
            if (hasSiteAt(sites, literal[0])
                || !chainProves(first, last, successorKey, literal[0], rules.placement())) {
              continue;
            }
            String expression = chainExpression(new FieldConstant(null, kind, value), sources,
              pooledBefore);
            if (expression == null) {
              continue;
            }
            found = new Site(literal[0], literal[1], "(" + expression + ")", run.get(0));
            break;
          }
        }
      }
      else {
        Set<String> pooledBefore = pooledKeys(cls, first.classIndex());
        for (long[] literal : literals) {
          int start = (int) literal[0];
          long raw = literal[2];
          if (raw < Integer.MIN_VALUE || raw > Integer.MAX_VALUE || hasSiteAt(sites, start)) {
            continue;
          }
          String key = VariableType.INT.name() + "|" + raw;
          if (!chainProves(first, last, key, start, rules.placement())) {
            continue;
          }
          String expression = chainExpression(new FieldConstant(null, VariableType.INT, (int) raw),
            sources, pooledBefore);
          if (expression == null) {
            continue;
          }
          found = new Site(start, (int) literal[1], "(" + expression + ")", run.get(0));
          break;
        }
      }
      if (found != null) {
        addSiteOnce(sites, found);
        claimed.addAll(run);
      }
    }
    return claimed;
  }

  /**
   * Places one naming for an owner whose {@code Class} entry precedes all generated code.
   *
   * <p>The site is not placed by the pool order, because the entry was not created at a generated
   * point; one naming anywhere reproduces it. Only an immediate value is accepted: naming a pooled
   * value would enter that value at the site, and the target pool did not put it there.
   */
  private static void earlySites(String text, List<int[]> spans, Rules rules,
                                 Map<String, List<Site>> deferred, List<Site> sites) {
    if (rules.placement().earlyOwners() == null || rules.placement().earlyOwners().isEmpty()) {
      return;
    }
    for (String owner : rules.placement().earlyOwners()) {
      if (siteIn(sites, owner, spans) || rules.placement().lexical().contains(owner)) {
        continue;
      }
      List<Site> candidates = deferred.get(owner);
      if (candidates == null) {
        continue;
      }
      Site best = null;
      for (Site site : candidates) {
        if ((best == null || site.start() < best.start()) && bareName(text, site)) {
          best = site;
        }
      }
      if (best != null) {
        addSiteOnce(sites, best);
      }
    }
  }

  /** Whether a site for this owner already lies inside one of this class's own text ranges. */
  private static boolean siteIn(List<Site> sites, String owner, List<int[]> spans) {
    for (Site site : sites) {
      if (site.owner().equals(owner) && inside(spans, site.start())) {
        return true;
      }
    }
    return false;
  }

  /** Whether the site replaces a literal with a plain constant name. */
  private static boolean bareName(String text, Site site) {
    if (site.start() < 0 || site.start() >= site.end() || site.end() > text.length()) {
      return false;
    }
    return site.replacement().matches("[A-Za-z_$][A-Za-z0-9_$.]*");
  }


  /** One constant field of a pool-unexplained owner, for a bitwise combination. */
  private record CompositeField(String name, long value) {
  }

  /**
   * A literal no single constant folds to may still be a flags word: several constants of one
   * owner combined by bitwise OR. Such an owner's {@code Class} entry exists only because the
   * source named one of its constants, and the pool order proves where.
   */
  private static void compositeSites(String text, List<int[]> spans, Rules rules, List<Site> sites) {
    if (rules.compositeOwners().isEmpty()) {
      return;
    }
    Map<String, List<CompositeField>> byOwner = new LinkedHashMap<>();
    for (Map.Entry<String, List<Constant>> entry : rules.compositeCandidates().entrySet()) {
      String key = entry.getKey();
      int bar = key.indexOf('|');
      if (bar < 0 || !key.substring(0, bar).equals(VariableType.INT.name())) {
        continue;
      }
      long value;
      try {
        value = Long.parseLong(key.substring(bar + 1));
      }
      catch (NumberFormatException e) {
        continue;
      }
      if (value <= 0 || value > Integer.MAX_VALUE) {
        continue;
      }
      for (Constant constant : entry.getValue()) {
        if (!rules.compositeOwners().contains(constant.owner())) {
          continue;
        }
        byOwner.computeIfAbsent(constant.owner(), k -> new ArrayList<>())
          .add(new CompositeField(constant.name(), value));
      }
    }
    if (byOwner.isEmpty()) {
      return;
    }
    List<long[]> literals = intLiterals(text, spans);
    Map<Long, Integer> counts = new HashMap<>();
    for (long[] literal : literals) {
      counts.merge(literal[2], 1, Integer::sum);
    }
    for (long[] literal : literals) {
      long value = literal[2];
      int start = (int)literal[0];
      if (value <= 0 || counts.get(value) != 1 || hasSiteAt(sites, start)) {
        continue;
      }
      Site match = compositeMatch(byOwner, rules, start, (int)literal[1], value);
      if (match != null) {
        addSiteOnce(sites, match);
      }
    }
  }

  private static Site compositeMatch(Map<String, List<CompositeField>> byOwner, Rules rules,
                                     int start, int end, long value) {
    Site found = null;
    for (Map.Entry<String, List<CompositeField>> entry : byOwner.entrySet()) {
      String owner = entry.getKey();
      if (!rules.placement().provesExactly(owner, start)) {
        continue;
      }
      List<CompositeField> picked = compositePick(entry.getValue(), value);
      if (picked == null) {
        continue;
      }
      String qualifier = solverQualifier(owner, rules.packageName());
      if (qualifier == null) {
        continue;
      }
      StringBuilder expression = new StringBuilder();
      for (CompositeField field : picked) {
        if (expression.length() > 0) {
          expression.append(" | ");
        }
        expression.append(qualifier).append('.').append(field.name());
      }
      if (found != null) {
        return null; // two owners or two combinations reproduce the word; neither is proven
      }
      found = new Site(start, end, "(" + expression + ")", owner);
    }
    return found;
  }

  /** The unique free-pair or free-triple OR of the owner's constants that equals the word. */
  private static List<CompositeField> compositePick(List<CompositeField> fields, long word) {
    List<CompositeField> best = null;
    for (int a = 0; a < fields.size(); a++) {
      CompositeField fa = fields.get(a);
      if ((fa.value() & word) != fa.value() || fa.value() == word) {
        continue;
      }
      for (int b = a + 1; b < fields.size(); b++) {
        CompositeField fb = fields.get(b);
        if ((fa.value() & fb.value()) != 0 || (fa.value() | fb.value()) != word) {
          continue;
        }
        if (best != null) {
          return null;
        }
        best = List.of(fa, fb);
      }
    }
    if (best != null) {
      return best;
    }
    for (int a = 0; a < fields.size(); a++) {
      CompositeField fa = fields.get(a);
      if ((fa.value() & word) != fa.value() || fa.value() == word) {
        continue;
      }
      for (int b = a + 1; b < fields.size(); b++) {
        CompositeField fb = fields.get(b);
        if ((fa.value() & fb.value()) != 0) {
          continue;
        }
        for (int c = b + 1; c < fields.size(); c++) {
          CompositeField fc = fields.get(c);
          if ((fb.value() & fc.value()) != 0 || (fa.value() & fc.value()) != 0
              || (fa.value() | fb.value() | fc.value()) != word) {
            continue;
          }
          if (best != null) {
            return null;
          }
          best = List.of(fa, fb, fc);
        }
      }
    }
    return best;
  }

  private static boolean hasSiteAt(List<Site> sites, int start) {
    for (Site site : sites) {
      if (site.start() == start) {
        return true;
      }
    }
    return false;
  }

  /** Every non-negative int literal of the class text, as {start, end, value}. */
  private static List<long[]> intLiterals(String text, List<int[]> spans) {
    List<long[]> literals = new ArrayList<>();
    for (int[] span : spans) {
      int i = span[0];
      while (i < span[1]) {
        char c = text.charAt(i);
        char next = i + 1 < text.length() ? text.charAt(i + 1) : '\0';
        if (c == '/' && next == '/') {
          int nl = text.indexOf('\n', i);
          i = nl < 0 ? span[1] : nl;
          continue;
        }
        if (c == '/' && next == '*') {
          int end = text.indexOf("*/", i + 2);
          i = end < 0 ? span[1] : end + 2;
          continue;
        }
        if (c == '"' || c == '\'') {
          i = skipQuoted(text, i, c);
          continue;
        }
        if (Character.isDigit(c) && (i == span[0] || !isIdentifierPart(text.charAt(i - 1)))) {
          long[] value = new long[1];
          int end = intLiteral(text, i, span[1], value);
          if (end > 0) {
            literals.add(new long[]{i, end, value[0]});
            i = end;
            continue;
          }
        }
        i++;
      }
    }
    return literals;
  }

  /** The end of a plain int literal at i, or -1; sets value[0]. No sign, dot or suffix. */
  private static int intLiteral(String text, int i, int to, long[] value) {
    int start = i;
    long number;
    if (text.charAt(i) == '0' && i + 1 < to
        && (text.charAt(i + 1) == 'x' || text.charAt(i + 1) == 'X')) {
      i += 2;
      int digits = i;
      while (i < to && Character.digit(text.charAt(i), 16) >= 0) {
        i++;
      }
      if (i == digits) {
        return -1;
      }
      try {
        number = Long.parseLong(text.substring(digits, i), 16);
      }
      catch (NumberFormatException e) {
        return -1;
      }
    }
    else {
      while (i < to && Character.isDigit(text.charAt(i))) {
        i++;
      }
      if (i == start) {
        return -1;
      }
      try {
        number = Long.parseLong(text.substring(start, i));
      }
      catch (NumberFormatException e) {
        return -1;
      }
    }
    if (i < to && (text.charAt(i) == '.' || text.charAt(i) == 'e' || text.charAt(i) == 'E'
        || text.charAt(i) == 'f' || text.charAt(i) == 'F' || text.charAt(i) == 'd'
        || text.charAt(i) == 'D' || text.charAt(i) == 'l' || text.charAt(i) == 'L'
        || isIdentifierPart(text.charAt(i)))) {
      return -1;
    }
    value[0] = number;
    return i;
  }

  /**
   * Whether the site is printed on the line of the {@code <field-init>} buffer the successor field
   * reference writes, in the constructor that generated it.
   */
  private static boolean fieldInitializerSite(String text, List<SiteSpace> spaces, int position,
                                              PairSite pair) {
    if (spaces == null || pair.member() == null) {
      return false;
    }
    int rank = (int) (pair.successor() >>> 32);
    String key = "<field-init " + pair.member() + ">";
    for (SiteSpace space : spaces) {
      if (space.rank() != rank || !key.equals(space.key())) {
        continue;
      }
      return position >= lineStart(text, space.min()) && position <= lineEnd(text, space.max());
    }
    return false;
  }

  /**
   * The constant whose owner's pair proves this site.
   *
   * <p>The pool entered the owner's Class and name immediately before the entry that follows the
   * pair. A literal generated in the gap between the neighbouring entries' first uses is that
   * naming, even when other owners declare the same value: their Class entries have no pair there.
   */
  private static Constant pairOwner(List<Constant> constants, int position, Placement placement) {
    if (placement == null || placement.pairs() == null || placement.spaces() == null) {
      return null;
    }
    long coordinate = siteCoordinate(placement.spaces(), position);
    if (coordinate == NO_COORDINATE) {
      return null;
    }
    for (Constant constant : constants) {
      PairSite pair = placement.pairs().get(constant.owner());
      if (pair == null || pair.open() >= 0) {
        continue; // a call pair places its site inside the argument list, not by the gap
      }
      if (gapAdmits(pair, position, placement)) {
        return constant;
      }
    }
    return null;
  }

  /** Whether the generation gap of a reference-free pair admits this printed site. */
  private static boolean gapAdmits(PairSite pair, int position, Placement placement) {
    if (placement.spaces() == null) {
      return false;
    }
    long coordinate = siteCoordinate(placement.spaces(), position);
    if (coordinate == NO_COORDINATE) {
      return false;
    }
    long offset = coordinate & 0xffffffffL;
    long successorOffset = pair.successor() & 0xffffffffL;
    // A value successor is the entry the naming itself entered, so the literal's own point is the
    // successor's point; a reference is created after its arguments and needs an earlier site.
    boolean atValue = pair.member() == null && offset == successorOffset;
    boolean atOrBefore = offset < successorOffset || atValue;
    // Within a reference successor's method the offsets follow the generation order, so the last
    // entry first used before the successor is the exact lower bound: an entry created after that
    // use and before the successor would be used there, and the pair would not precede it. The
    // interval-wide first-use bound is a proxy only and can lie above this point when an early
    // entry is first used in a later method.
    long lower = pair.successorKey() == null ? pair.after() : pair.lower();
    return (coordinate >>> 32) == (pair.successor() >>> 32) && atOrBefore
      && (atValue || coordinate > lower);
  }

  /**
   * The expression a pool-proven naming site wrote.
   *
   * <p>A pair directly before the site records that the source named a constant of its owner as
   * the last pool-entering event there; the folded value it produced is the recorded literal. When
   * no constant of that value exists, the source wrote an expression over one of the owner's
   * constants and a literal. Each constant is tried with the verified solver, which folds the
   * whole expression back in the recorded type and accepts only a bit-exact result; the literal
   * is printed parenthesised so the surrounding expression keeps its precedence.
   */
  private static Site solvedSite(String key, int start, int end, String own, List<String> imports,
                                 String packageName, Placement placement, boolean[] exactProof) {
    if (placement == null || placement.pairs() == null || placement.spaces() == null) {
      return null;
    }
    int bar = key.indexOf('|');
    if (bar < 0) {
      return null;
    }
    VariableType kind = variableType(key.substring(0, bar));
    if (kind == null) {
      return null;
    }
    Object value;
    try {
      String text = key.substring(bar + 1);
      value = switch (kind) {
        case INT -> Integer.valueOf(Integer.parseInt(text));
        case LONG -> Long.valueOf(Long.parseLong(text));
        case FLOAT -> Float.valueOf(Float.parseFloat(text));
        case DOUBLE -> Double.valueOf(Double.parseDouble(text));
        case BOOLEAN -> Boolean.valueOf(text);
        case STRING -> text;
        default -> null;
      };
    }
    catch (NumberFormatException e) {
      return null;
    }
    if (value == null) {
      return null;
    }
    StructClass site = DecompilerContext.getStructContext().getClass(own);
    if (site == null) {
      return null;
    }
    // A value successor is the pool's own record of the folded value the naming produced, so its
    // match is exact and takes precedence. A reference successor only says that some naming of the
    // owner was the last pool-entering event before the reference; several owners' pairs can admit
    // the same argument list, and one candidate's expression must not hide another's exact record.
    Site exact = null;
    boolean exactDirect = false;
    Site directSite = null;
    Site invented = null;
    for (Map.Entry<String, PairSite> entry : placement.pairs().entrySet()) {
      PairSite pair = entry.getValue();
      if (!pairProvesSite(pair, key, start, placement)) {
        continue;
      }
      boolean referenceSuccessor = pair.successorKey() == null;
      if (referenceSuccessor) {
        boolean inArgs = pair.open() >= 0 && start > pair.open() && start < pair.close();
        if (inArgs) {
          // Inside the call's own argument list the naming must come after the last entry the
          // generation placed below the pair; naming before it would create the pair ahead of that
          // entry. A folded literal usually has no printed position of its own, so the coordinate
          // of the preceding operand cannot tell the two apart, while the character offsets can:
          // the arguments are printed in the order they are generated. When that last use has no
          // printed position nothing can place it, and the pool-free expression rule below is the
          // only evidence left.
          if (pair.lowerAt() >= 0 && start <= pair.lowerAt()) {
            continue;
          }
        }
        else {
          long sitePoint = siteCoordinate(placement.spaces(), start);
          // The last use before the reference bounds the site only inside the reference's own
          // method: there the offsets order the two exactly. A site in an earlier method is
          // generated before every use in the successor's method, so that comparison would reject
          // a site the pool admits; the pair's own bracket already placed it.
          if (sitePoint == NO_COORDINATE) {
            continue;
          }
          boolean sameRank = (sitePoint >>> 32) == (pair.successor() >>> 32);
          if (sameRank && sitePoint <= pair.after()) {
            // An instruction between this site and the reference used an entry the pair precedes,
            // so the original named the constant after that instruction; naming it here would
            // reorder the pool.
            continue;
          }
        }
      }
      String owner = entry.getKey();
      String qualifier = solverQualifier(owner, packageName);
      if (qualifier == null) {
        continue; // the owner cannot be named unambiguously from this class
      }
      List<SourceConstant> sources = sourceConstants(owner, site, imports, packageName);
      Set<String> pooledBefore = referenceSuccessor ? pooledKeys(site, pair.classIndex()) : Set.of();
      String direct = null;
      String first = null;
      String expression = null;
      for (SourceConstant source : sources) {
        if (kind == VariableType.BOOLEAN) {
          if (source.kind() != VariableType.BOOLEAN) {
            continue;
          }
        }
        else if (kind == VariableType.STRING) {
          if (source.kind() != VariableType.STRING) {
            continue;
          }
        }
        else if (!numeric(source.kind()) || (promote(source.kind(), kind) != kind
            && !castable(source.kind(), kind))) {
          continue; // the expression's static type must be the recorded literal's own type
        }
        String fieldName = source.name().substring(source.name().lastIndexOf('.') + 1);
        String name = qualifier + "." + fieldName;
        String solved = constantExpression(new FieldConstant(null, kind, value),
          source.kind(), source.value(), name);
        if (solved == null) {
          continue;
        }
        if (source.kind() != kind && (solved.equals(name) || solved.equals("-" + name)
            || solved.equals("~" + name))) {
          // A bare constant keeps its own type: an int constant where a float literal stood would
          // turn a division or multiplication into integer arithmetic.
          continue;
        }
        if (first == null) {
          // A value successor is the folded value itself, so any expression that folds to it
          // enters the same value at the pair; the first declared constant reproduces the bytes.
          first = solved;
        }
        if (direct == null && solved.equals(name)) {
          direct = solved;
        }
        if (expression == null && (immediateKey(key) || pooledBefore.contains(key))
            && poolFree(solved, pooledBefore)) {
          // Named before a reference successor, the folded expression's value would be entered
          // right after the class and its name; the pair admitted this literal only because that
          // value is an immediate or already pooled below the pair. The solved expression's own
          // literals must obey the same rule: a pooled value one of them introduces would land
          // after the pair, where the original had none.
          expression = solved;
        }
      }
      // A constant whose own value is the literal reproduces the interned neighbour exactly and
      // is the original's form whenever the pool offers one; only without it does an expression
      // stand in, and only where the pair leaves the neighbour free-standing.
      String found = direct != null ? direct : referenceSuccessor ? expression : first;
      if (found == null) {
        continue;
      }
      Site solved = new Site(start, end, "(" + found + ")", owner);
      if (!referenceSuccessor) {
        if (exact != null) {
          return null; // two value successors of one value cannot both name this literal
        }
        exact = solved;
        exactDirect = direct != null;
      }
      else if (direct != null) {
        if (directSite != null) {
          return null; // two owners declare the literal's own value; the pool cannot choose
        }
        directSite = solved;
      }
      else {
        if (invented != null) {
          return null; // two owners' expressions fold here; the pool does not record which
        }
        invented = solved;
      }
    }
    Site chosen = exact != null ? exact : directSite != null ? directSite : invented;
    if (chosen != null && exactProof != null) {
      exactProof[0] = exact != null;
      exactProof[1] = exact != null ? exactDirect : chosen == directSite;
    }
    return chosen;
  }

  /** The fully qualified form of the owner's name, unambiguous at any site, or null. */
  private static String solverQualifier(String owner, String packageName) {
    if (anonymous(owner)) {
      return null;
    }
    if (!publiclyNameable(owner, packageName) && !packageName.equals(packageOf(owner))) {
      return null;
    }
    return owner.replace('/', '.').replace('$', '.');
  }

  private static VariableType variableType(String name) {
    return switch (name) {
      case "INT" -> VariableType.INT;
      case "LONG" -> VariableType.LONG;
      case "FLOAT" -> VariableType.FLOAT;
      case "DOUBLE" -> VariableType.DOUBLE;
      case "BOOLEAN" -> VariableType.BOOLEAN;
      case "STRING" -> VariableType.STRING;
      default -> null;
    };
  }

  /** Whether the pair's own record places a naming at this literal, for that literal's value. */
  private static boolean pairProvesSite(PairSite pair, String key, int position, Placement placement) {
    if (pair.successorKey() != null && !key.equals(pair.successorKey())) {
      return false; // the value the naming entered is not this literal's
    }
    return pair.valueAvailable(key) && pairProvesBounds(pair, position, placement);
  }

  /**
   * Whether the pool order admits a naming of the pair's owner at this text position.
   *
   * <p>A chain's later pairs record the folded value, so the first pair's own value check does not
   * apply; only the generation-order bracket does. A value successor's point is the value's own
   * first use, which {@link #chainProves} compares against the last pair instead.
   */
  private static boolean pairProvesBounds(PairSite pair, int position, Placement placement) {
    long coordinate = siteCoordinate(placement.spaces(), position);
    if (coordinate == NO_COORDINATE) {
      // A field initializer's folded literal is printed at its declaration, where the printer maps
      // no instruction point. A value successor's printed point lying in the same initializer is
      // the record that this literal is the one the naming produced.
      return pair.successorKey() != null && pair.member() == null
        && pairedInitializer(placement.text(), placement.spaces(), placement.spans(), position,
        pair.successorAt());
    }
    long offset = coordinate & 0xffffffffL;
    long successorOffset = pair.successor() & 0xffffffffL;
    boolean sameRank = (coordinate >>> 32) == (pair.successor() >>> 32);
    boolean atValue = pair.member() == null && offset == successorOffset;
    if (pair.successorKey() != null) {
      // The pair's next entry is the folded value the naming entered; the caller checked that the
      // literal is that very value, so its own first use is the naming site.
      return sameRank && atValue;
    }
    // A naming may stand in an earlier method than the pair's successor: the coordinate orders
    // methods by generation, so any site below the successor is still generated before it. Only
    // the argument window is bound to the successor's own method.
    boolean before = coordinate < pair.successor();
    // In a reference successor's own method the last use before it is the exact lower bound; in an
    // earlier method the interval-wide first-use bound is the only one the pool order offers.
    long lower = sameRank && pair.successorKey() == null ? pair.after() : pair.lower();
    if (pair.open() >= 0 && sameRank) {
      boolean inArgs = position > pair.open() && position < pair.close();
      return inArgs || before && coordinate > lower;
    }
    return before && coordinate > lower;
  }

  /** Whether some site already names this owner in the class text. */
  private static boolean hasSiteFor(List<Site> sites, String owner) {
    for (Site site : sites) {
      if (owner.equals(site.owner())) {
        return true;
      }
    }
    return false;
  }

  // -------------------------------------------------------- constant expressions

  /** A constant field of the class itself: its declaration, kind and folded value. */
  private record FieldConstant(StructField field, VariableType kind, Object value) {
  }

  private enum Op { ADD, SUB, MUL, DIV, SHL, SHR, AND, OR, XOR }

  /**
   * Rewrites one constant initializer of a class whose own {@code Class} entry opens the pool.
   *
   * <p>javac visits the fields before it generates any method body, and a constant expression that
   * names a constant of the class itself interns the class's own {@code Class} entry right there;
   * the entry {@code this_class} writes later finds it already present. No generated construct can
   * put the own entry at index 1: the constructor's super call is always entered first. So an own
   * {@code Class} entry at index 1 proves the original source named one of this class's constants
   * in a field initializer. The folded value is all that survives, so any expression over another
   * of the class's constants that folds to the field's exact value reproduces the pool; one such
   * rewrite per class is enough, because later names of the class add no entry.
   *
   * <p>The sites are added after the literal scan, so the literals introduced here are never taken
   * as evidence for another constant's naming site.
   */
  private static void expressionSites(String text, List<int[]> spans, ClassNode node, List<Site> sites) {
    StructClass own = node == null ? null : node.classStruct;
    if (own == null || (own.getAccessFlags() & CodeConstants.ACC_INTERFACE) != 0) {
      return;
    }
    List<String> owners = prefixOwners(own);
    if (owners.isEmpty()) {
      return;
    }
    List<FieldConstant> constants = new ArrayList<>();
    for (StructField field : own.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      PrimitiveConstant constant = constantValue(own, field);
      VariableType kind = constant == null ? null : kind(field.getDescriptor());
      if (constant == null || kind == null || constant.value == null) {
        continue;
      }
      constants.add(new FieldConstant(field, kind, constant.value));
    }
    if (constants.isEmpty()) {
      return;
    }
    Map<String, List<int[]>> initializers = ownInitializers(text, spans, own);
    List<String> imports = imports(text);
    String packageName = packageName(text);
    int last = -1;
    int k = 0;
    while (k < owners.size()) {
      String owner = owners.get(k);
      Site existing = firstInitializerSite(sites, owner, spans, initializers);
      if (existing != null) {
        last = Math.max(last, existing.start());
        k++;
        continue;
      }
      // A later pair that already has a site in an initializer fixes the upper end of the field
      // interval this naming may use; a placement after it would reorder the pool.
      int limit = initializerLimit(sites, owners, k + 1, spans, initializers);
      boolean self = owner.equals(own.qualifiedName);
      if (self) {
        // `Own.Nested.CONST` interns the class's own Class entry when it resolves the nested
        // type's qualifier, then the nested owner's: the pool's own pair immediately followed by
        // a nested owner's pair is that one expression, and both entries open the pool together.
        List<List<SourceConstant>> rooted = new ArrayList<>();
        int rootedEnd = k;
        while (rootedEnd + 1 < owners.size()
            && owners.get(rootedEnd + 1).startsWith(own.qualifiedName + "$")
            && firstInitializerSite(sites, owners.get(rootedEnd + 1), spans, initializers) == null) {
          List<SourceConstant> next = sourceConstants(owners.get(rootedEnd + 1), own, imports,
            packageName, own.qualifiedName);
          if (next.isEmpty()) {
            break;
          }
          rooted.add(next);
          rootedEnd++;
        }
        if (!rooted.isEmpty()) {
          int[] rootedUsed = new int[1];
          Site rootedSite = placeChain(owner, constants, rooted, initializers, text, sites, last,
            limit, rootedUsed, constants);
          if (rootedSite != null) {
            addSiteOnce(sites, rootedSite);
            last = rootedSite.start();
            k += 1 + rootedUsed[0];
            continue;
          }
        }
        Site placed = placeOwnConstant(owner, constants, initializers, text, sites, last, limit);
        if (placed == null) {
          return;
        }
        addSiteOnce(sites, placed);
        last = placed.start();
        k++;
        continue;
      }
      // The pool names the prefix owners in source order, and one constant-field initializer may
      // name several of them: `Tag.TAG_BYTE + Byte.SIZE`. The run stops at a name that already
      // has a site, at the class itself (whose own naming is a separate rule), and at an owner
      // whose name cannot be written here.
      List<List<SourceConstant>> run = new ArrayList<>();
      List<SourceConstant> sources = sourceConstants(owner, own, imports, packageName);
      if (sources.isEmpty()) {
        return; // this owner's naming cannot be written, and a later one would move into its slot
      }
      run.add(sources);
      int end = k;
      while (end + 1 < owners.size() && !owners.get(end + 1).equals(own.qualifiedName)
          && firstInitializerSite(sites, owners.get(end + 1), spans, initializers) == null) {
        List<SourceConstant> next = sourceConstants(owners.get(end + 1), own, imports, packageName);
        if (next.isEmpty()) {
          break;
        }
        run.add(next);
        end++;
      }
      int[] used = new int[1];
      Site placed = placeChain(owner, constants, run, initializers, text, sites, last, limit, used);
      if (placed == null) {
        return;
      }
      addSiteOnce(sites, placed);
      last = placed.start();
      // The expression may have named fewer owners than the run offered; the rest still need a
      // site of their own, after this one.
      k += used[0];
    }
  }

  /** The site naming the class's own constant in an initializer, or null when none fits. */
  private static Site placeOwnConstant(String owner, List<FieldConstant> constants,
                                       Map<String, List<int[]>> initializers, String text,
                                       List<Site> sites, int last, int limit) {
    for (int i = 1; i < constants.size(); i++) {
      FieldConstant target = constants.get(i);
      List<int[]> ranges = initializers.get(target.field().getName());
      if (ranges == null || ranges.isEmpty()) {
        continue;
      }
      int[] range = ranges.get(0);
      if (range[0] <= last || (limit >= 0 && range[0] >= limit) || occupied(sites, range)) {
        continue; // outside the interval the pool order leaves, or already rewritten
      }
      int equals = text.indexOf('=', range[0]);
      if (equals < 0 || equals >= range[1]) {
        continue;
      }
      for (int j = 0; j < i; j++) {
        FieldConstant source = constants.get(j);
        String expression = constantExpression(target, source.kind(), source.value(),
          source.field().getName());
        if (expression != null) {
          return new Site(equals + 1, range[1], " " + expression, owner);
        }
      }
    }
    return null;
  }

  /**
   * The first initializer that can name a run of prefix owners in pool order, or null.
   *
   * <p>The fields are scanned in source order, and the longest run that an expression can name is
   * preferred: a later owner the run names needs no initializer of its own, and every prefix
   * owner's first naming must appear before the next one's. {@code used} reports how many owners
   * the chosen expression named.
   */
  private static Site placeChain(String firstOwner, List<FieldConstant> constants,
                                 List<List<SourceConstant>> run,
                                 Map<String, List<int[]>> initializers, String text,
                                 List<Site> sites, int last, int limit, int[] used) {
    return placeChain(firstOwner, constants, run, initializers, text, sites, last, limit, used,
      null);
  }

  /**
   * The same, optionally starting the expression with a bare own constant.
   *
   * <p>{@code Own.Nested.CONST} needs the class's own pair before the nested owner's, and a bare
   * reference to an own constant interns that pair while the qualified nested name interns the
   * nested owner's. Only own constants declared before the target field may be written there; a
   * forward simple-name reference is not valid Java.
   */
  private static Site placeChain(String firstOwner, List<FieldConstant> constants,
                                 List<List<SourceConstant>> run,
                                 Map<String, List<int[]>> initializers, String text,
                                 List<Site> sites, int last, int limit, int[] used,
                                 List<FieldConstant> ownPrefix) {
    for (int t = 0; t < constants.size(); t++) {
      FieldConstant target = constants.get(t);
      List<int[]> ranges = initializers.get(target.field().getName());
      if (ranges == null || ranges.isEmpty()) {
        continue;
      }
      int[] range = ranges.get(0);
      if (range[0] <= last || (limit >= 0 && range[0] >= limit) || occupied(sites, range)) {
        continue;
      }
      int equals = text.indexOf('=', range[0]);
      if (equals < 0 || equals >= range[1]) {
        continue;
      }
      List<List<SourceConstant>> chain = run;
      int first = 1;
      if (ownPrefix != null) {
        List<SourceConstant> terms = new ArrayList<>();
        for (int j = 0; j < t && j < ownPrefix.size(); j++) {
          FieldConstant own = ownPrefix.get(j);
          terms.add(new SourceConstant(own.field().getName(), own.kind(), own.value()));
        }
        if (terms.isEmpty()) {
          continue; // no own constant declared before this field can open the expression
        }
        chain = new ArrayList<>();
        chain.add(terms);
        chain.addAll(run);
        first = 2; // the own term alone names the own class, which has its own rule
      }
      for (int count = chain.size(); count >= first; count--) {
        String expression = chainExpression(target, chain.subList(0, count), null);
        if (expression != null) {
          used[0] = ownPrefix == null ? count : count - 1;
          return new Site(equals + 1, range[1], " " + expression, firstOwner);
        }
      }
    }
    return null;
  }

  /**
   * A string concatenation naming every owner of the run in order and folding to the value.
   *
   * <p>Each owner contributes one of its string constants; the pieces of the value between the
   * names are literal segments. The leftmost occurrence of each constant that leaves room for the
   * rest of the run is the one that keeps the names in pool order.
   */
  private static String stringChainExpression(String value, List<List<SourceConstant>> run) {
    List<String> parts = new ArrayList<>();
    int pos = 0;
    for (List<SourceConstant> terms : run) {
      SourceConstant chosen = null;
      int at = -1;
      for (SourceConstant term : terms) {
        if (term.kind() != VariableType.STRING || !(term.value() instanceof String text)
            || text.isEmpty()) {
          continue;
        }
        int index = value.indexOf(text, pos);
        if (index < 0) {
          continue;
        }
        if (chosen == null || index < at) {
          chosen = term;
          at = index;
        }
      }
      if (chosen == null) {
        return null;
      }
      if (at > pos) {
        parts.add(quote(value.substring(pos, at)));
      }
      parts.add(chosen.name());
      pos = at + ((String) chosen.value()).length();
    }
    if (pos < value.length()) {
      parts.add(quote(value.substring(pos)));
    }
    return parts.isEmpty() ? null : String.join(" + ", parts);
  }

  /** The value a literal key names, in its own kind, or null. */
  private static Object kindValue(VariableType kind, String key) {
    int bar = key.indexOf('|');
    if (bar < 0) {
      return null;
    }
    String text = key.substring(bar + 1);
    try {
      return switch (kind) {
        case INT -> Integer.valueOf(Integer.parseInt(text));
        case LONG -> Long.valueOf(Long.parseLong(text));
        case FLOAT -> Float.valueOf(Float.parseFloat(text));
        case DOUBLE -> Double.valueOf(Double.parseDouble(text));
        case BOOLEAN -> Boolean.valueOf(text);
        case STRING -> text;
        case CHAR -> Integer.valueOf(Integer.parseInt(text));
        default -> null;
      };
    }
    catch (NumberFormatException e) {
      return null;
    }
  }

  /** The spans of the numeric literals whose key is {@code key}. */
  private static List<int[]> literalSpansFor(String text, List<int[]> spans, String key) {
    List<int[]> found = new ArrayList<>();
    for (int[] span : spans) {
      int i = span[0];
      while (i < span[1]) {
        char c = text.charAt(i);
        char next = i + 1 < text.length() ? text.charAt(i + 1) : '\0';
        if (c == '/' && next == '/') {
          int newline = text.indexOf('\n', i);
          i = newline < 0 ? span[1] : newline;
          continue;
        }
        if (c == '/' && next == '*') {
          int end = text.indexOf("*/", i + 2);
          i = end < 0 ? span[1] : end + 2;
          continue;
        }
        if (c == '"' || c == '\'') {
          i = skipQuoted(text, i, c);
          continue;
        }
        if (Character.isDigit(c) && (i == span[0] || !isIdentifierPart(text.charAt(i - 1)))) {
          int end = i;
          boolean dot = false;
          while (end < span[1]) {
            char d = text.charAt(end);
            if (Character.isLetterOrDigit(d) || d == '_') {
              end++;
              continue;
            }
            if (d == '.' && !dot) {
              dot = true;
              end++;
              continue;
            }
            if ((d == '+' || d == '-') && end > i
                && (text.charAt(end - 1) == 'e' || text.charAt(end - 1) == 'E')) {
              end++;
              continue;
            }
            break;
          }
          if (key.equals(literalKey(text.substring(i, end)))) {
            found.add(new int[]{i, end});
          }
          i = end;
          continue;
        }
        i++;
      }
    }
    return found;
  }

  /** The spans of the string literals whose value is {@code value}, quotes included. */
  private static List<int[]> stringLiteralSpans(String text, List<int[]> spans, String value) {
    List<int[]> found = new ArrayList<>();
    for (int[] span : spans) {
      int i = span[0];
      while (i < span[1]) {
        char c = text.charAt(i);
        char next = i + 1 < text.length() ? text.charAt(i + 1) : '\0';
        if (c == '/' && next == '/') {
          int newline = text.indexOf('\n', i);
          i = newline < 0 ? span[1] : newline;
          continue;
        }
        if (c == '/' && next == '*') {
          int end = text.indexOf("*/", i + 2);
          i = end < 0 ? span[1] : end + 2;
          continue;
        }
        if (c == '"') {
          int end = skipQuoted(text, i, '"');
          if (!text.startsWith("\"\"\"", i) && end - 1 > i) {
            String content = unescape(text.substring(i + 1, end - 1));
            if (value.equals(content)) {
              found.add(new int[]{i, end});
            }
          }
          i = end;
          continue;
        }
        if (c == '\'') {
          i = skipQuoted(text, i, '\'');
          continue;
        }
        i++;
      }
    }
    return found;
  }

  /** A java string literal for this value, with escapes the compiler reads back unchanged. */
  private static String quote(String value) {
    StringBuilder out = new StringBuilder(value.length() + 2).append('"');
    for (int i = 0; i < value.length(); i++) {
      char c = value.charAt(i);
      switch (c) {
        case '\\' -> out.append("\\\\");
        case '"' -> out.append("\\\"");
        case '\n' -> out.append("\\n");
        case '\r' -> out.append("\\r");
        case '\t' -> out.append("\\t");
        case '\b' -> out.append("\\b");
        case '\f' -> out.append("\\f");
        default -> {
          if (c < 0x20 || c == 0x7f) {
            // Not a \\u escape: those are translated before lexing, and a newline one would end
            // the literal. An octal escape is an ordinary string escape.
            String octal = Integer.toOctalString(c);
            out.append('\\').append("0".repeat(3 - octal.length())).append(octal);
          }
          else {
            out.append(c);
          }
        }
      }
    }
    return out.append('"').toString();
  }

  /**
   * An expression naming every owner of the run in order and folding to the target value.
   *
   * <p>In a method body the expression's literals must enter nothing the pair did not have, so
   * {@code pooledBefore} is the value set already in the pool; a null set accepts any literal,
   * which is right in a constant field initializer, where the whole expression is folded at
   * attribution and never reaches the pool.
   */
  private static String chainExpression(FieldConstant target, List<List<SourceConstant>> run,
                                        Set<String> pooledBefore) {
    if (run.size() == 1) {
      for (SourceConstant source : run.get(0)) {
        String expression = constantExpression(target, source.kind(), source.value(), source.name());
        if (expression != null) {
          return expression;
        }
      }
      return null;
    }
    int[] budget = new int[]{200000};
    for (SourceConstant first : run.get(0)) {
      String found = chainCombine(target, run, 1, first.kind(), first.value(), first.name(),
        pooledBefore, budget);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  /** The binary operators a chain may combine constants with, in preference order. */
  private static final List<Op> CHAIN_OPS = List.of(Op.ADD, Op.SUB, Op.OR, Op.XOR, Op.AND,
    Op.MUL, Op.DIV);

  private static String chainCombine(FieldConstant target, List<List<SourceConstant>> run,
                                     int index, VariableType kind, Object value, String text,
                                     Set<String> pooledBefore, int[] budget) {
    if (budget[0]-- <= 0) {
      return null;
    }
    if (index == run.size()) {
      // The expression stands where the literal stood, so its static type must be the literal's
      // own: a chain of int constants inside a float division would otherwise make it integer
      // arithmetic. A cast bridges the kinds, exactly as the original's cast did.
      if (kind == target.kind() && foldsTo(value, kind, target)) {
        return text;
      }
      // A chain of int constants written where a float or double literal stands needs the cast the
      // original wrote: `(float)(Owner.A * Other.B)`. The cast folds away at compile time.
      Object cast = kind == target.kind() ? null : castValue(value, kind, target.kind());
      if (cast != null && foldsTo(cast, target.kind(), target)) {
        return "(" + javaName(target.kind()) + ")(" + text + ")";
      }
      // The chain keeps its own precedence: a compound left operand is parenthesised before the
      // solver appends its literal.
      String literal = binaryExpression(target, kind, value, "(" + text + ")");
      return literal != null && poolFree(literal, pooledBefore) ? literal : null;
    }
    for (SourceConstant term : run.get(index)) {
      VariableType p = promote(kind, term.kind());
      if (p == null) {
        continue;
      }
      Object left = convert(value, kind, p);
      Object right = convert(term.value(), term.kind(), p);
      if (left == null || right == null) {
        continue;
      }
      for (Op op : CHAIN_OPS) {
        Object combined = combineValues(op, left, right, p);
        if (combined == null) {
          continue;
        }
        String next = index == 1 ? text + " " + symbol(op) + " " + term.name()
          : "(" + text + ") " + symbol(op) + " " + term.name();
        String found = chainCombine(target, run, index + 1, p, combined, next, pooledBefore, budget);
        if (found != null) {
          return found;
        }
      }
    }
    return null;
  }

  /** The value of a binary operation over converted operands, or null when it cannot fold. */
  private static Object combineValues(Op op, Object left, Object right, VariableType p) {
    try {
      if (p == VariableType.INT) {
        int a = ((Number) left).intValue();
        int b = ((Number) right).intValue();
        return switch (op) {
          case ADD -> Integer.valueOf(a + b);
          case SUB -> Integer.valueOf(a - b);
          case MUL -> Integer.valueOf(a * b);
          case DIV -> Integer.valueOf(a / b);
          case AND -> Integer.valueOf(a & b);
          case OR -> Integer.valueOf(a | b);
          case XOR -> Integer.valueOf(a ^ b);
          default -> null;
        };
      }
      if (p == VariableType.LONG) {
        long a = ((Number) left).longValue();
        long b = ((Number) right).longValue();
        return switch (op) {
          case ADD -> Long.valueOf(a + b);
          case SUB -> Long.valueOf(a - b);
          case MUL -> Long.valueOf(a * b);
          case DIV -> Long.valueOf(a / b);
          case AND -> Long.valueOf(a & b);
          case OR -> Long.valueOf(a | b);
          case XOR -> Long.valueOf(a ^ b);
          default -> null;
        };
      }
      if (p == VariableType.FLOAT) {
        float a = ((Number) left).floatValue();
        float b = ((Number) right).floatValue();
        float result = switch (op) {
          case ADD -> a + b;
          case SUB -> a - b;
          case MUL -> a * b;
          case DIV -> a / b;
          default -> Float.NaN;
        };
        return Float.isFinite(result) ? Float.valueOf(result) : null;
      }
      if (p == VariableType.DOUBLE) {
        double a = ((Number) left).doubleValue();
        double b = ((Number) right).doubleValue();
        double result = switch (op) {
          case ADD -> a + b;
          case SUB -> a - b;
          case MUL -> a * b;
          case DIV -> a / b;
          default -> Double.NaN;
        };
        return Double.isFinite(result) ? Double.valueOf(result) : null;
      }
    }
    catch (ArithmeticException e) {
      return null;
    }
    return null;
  }

  /**
   * Names a constant of the class itself in an instance field initializer the pool records.
   *
   * <p>javac enters the class's own {@code Class} entry and its name when it resolves a constant
   * named in an initializer, before it enters the field reference of the assignment. When the
   * class opens no pool prefix, no instruction uses its {@code Class} entry, and that entry and
   * its name sit immediately before the class's first field reference, the only construct that can
   * have interned them there is such a naming, and the first field reference is the assignment the
   * initializer belongs to. Its printed literal is the folded value, so a constant of the class
   * with exactly that value reproduces the pool.
   *
   * <p>Byte and short constants count here: an initializer is an assignment context, where a
   * narrow constant widens silently, unlike a method argument where naming it would change the
   * expression's type. Small values are not dismissed as coincidence either: the pool proves the
   * naming, and the value only chooses among the class's own constants.
   */
  private static void initializerSites(String text, List<int[]> spans, ClassNode node, List<Site> sites) {
    StructClass own = node == null ? null : node.classStruct;
    if (own == null || (own.getAccessFlags() & CodeConstants.ACC_INTERFACE) != 0) {
      return;
    }
    if (prefixOwners(own).contains(own.qualifiedName)) {
      return; // a constant field initializer already accounts for the class entry
    }
    Integer classIndex = classIndices(own).get(own.qualifiedName);
    if (classIndex == null) {
      return;
    }
    List<PooledConstant> pool = own.getPool().getPool();
    int first = -1;
    for (int i = 1; i < pool.size(); i++) {
      if (pool.get(i) instanceof LinkConstant link && own.qualifiedName.equals(link.classname)) {
        first = i;
        break;
      }
    }
    // The naming interns the class, its name and -- when the folded value is not an immediate and
    // is not already pooled -- the value itself, and then the assignment's field reference follows.
    int foldedIndex = -1;
    boolean pair = first > classIndex && first - classIndex == 2;
    if (!pair && first > classIndex && pool.get(classIndex + 2) instanceof PrimitiveConstant value) {
      int width = value.type == CodeConstants.CONSTANT_Long
        || value.type == CodeConstants.CONSTANT_Double ? 4 : 3;
      boolean numericOrString = value.type == CodeConstants.CONSTANT_Integer
        || value.type == CodeConstants.CONSTANT_Long || value.type == CodeConstants.CONSTANT_Float
        || value.type == CodeConstants.CONSTANT_Double
        || value.type == CodeConstants.CONSTANT_String;
      if (numericOrString && first - classIndex == width) {
        foldedIndex = classIndex + 2;
      }
    }
    if (!pair && foldedIndex < 0) {
      return;
    }
    if (!(pool.get(first) instanceof LinkConstant reference)
        || reference.type != CodeConstants.CONSTANT_Fieldref || reference.elementname == null) {
      return;
    }
    Map<Integer, FirstUse> uses = firstUses(own);
    FirstUse classUse = uses.get(classIndex);
    FirstUse fieldUse = uses.get(first);
    if (classUse != null && (fieldUse == null || compare(classUse, fieldUse) < 0)) {
      // A generated construct uses the Class entry before the field reference exists.
      return;
    }
    StructField target = null;
    for (StructField field : own.getFields()) {
      if (field.getName().equals(reference.elementname)) {
        target = field;
        break;
      }
    }
    if (target == null || (target.getAccessFlags() & CodeConstants.ACC_STATIC) != 0) {
      return;
    }
    String targetKind = target.getDescriptor();
    if (!targetKind.equals("I") && !targetKind.equals("J") && !targetKind.equals("F")
        && !targetKind.equals("D") && !targetKind.equals("C") && !targetKind.equals("Z")
        && !targetKind.equals("Ljava/lang/String;")) {
      return;
    }
    Map<String, List<String>> sources = ownInitializerSources(own, targetKind);
    if (sources.isEmpty()) {
      return;
    }
    int[] range = initializerRange(text, spans, target.getName());
    if (range == null || occupied(sites, range)) {
      return;
    }
    int equals = text.indexOf('=', range[0]);
    if (equals < 0 || equals >= range[1]) {
      return;
    }
    String key = literalKey(text.substring(equals + 1, range[1]).trim());
    if (key == null) {
      return;
    }
    if (foldedIndex > 0 && !canonicalKey(key).equals(
        canonicalKey(valueKey((PrimitiveConstant)pool.get(foldedIndex))))) {
      // The value the naming interned is not this initializer's value, so the pair was created
      // elsewhere and naming a constant here would enter a different value at the same point.
      return;
    }
    List<String> names = sources.get(key);
    if (names == null || names.isEmpty()) {
      return;
    }
    sites.add(new Site(equals + 1, range[1], " " + names.get(0), own.qualifiedName));
  }

  /**
   * The constants of the class that may be named in an initializer of a field of this type,
   * keyed like the literal scanner's values.
   */
  private static Map<String, List<String>> ownInitializerSources(StructClass own, String target) {
    Map<String, List<String>> sources = new HashMap<>();
    for (StructField field : own.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      PrimitiveConstant value = constantValue(own, field);
      if (value == null || value.value == null) {
        continue;
      }
      String descriptor = field.getDescriptor();
      if (!assignmentWidens(target, descriptor)) {
        continue;
      }
      for (String key : valueKeys(descriptor, value.value)) {
        sources.computeIfAbsent(key, k -> new ArrayList<>()).add(field.getName());
      }
    }
    return sources;
  }

  /** Whether a constant of the source type may be assigned to a field of the target type. */
  private static boolean assignmentWidens(String target, String source) {
    return switch (target) {
      case "I" -> source.equals("I") || source.equals("C") || source.equals("B") || source.equals("S");
      case "J" -> source.equals("J") || source.equals("I") || source.equals("C")
        || source.equals("B") || source.equals("S");
      case "F" -> source.equals("F") || source.equals("J") || source.equals("I") || source.equals("C")
        || source.equals("B") || source.equals("S");
      case "D" -> source.equals("D") || source.equals("F") || source.equals("J") || source.equals("I")
        || source.equals("C") || source.equals("B") || source.equals("S");
      case "C" -> source.equals("C");
      default -> target.equals(source);
    };
  }

  /** The literal keys a constant of this descriptor and value answers to. */
  private static List<String> valueKeys(String descriptor, Object value) {
    if (!(value instanceof Number number)) {
      return descriptor.equals("Ljava/lang/String;") && value instanceof String text
        ? List.of(VariableType.STRING.name() + "|" + text) : List.of();
    }
    return switch (descriptor) {
      case "B", "S", "I" -> {
        int v = number.intValue();
        yield List.of(VariableType.INT.name() + "|" + v, VariableType.LONG.name() + "|" + v);
      }
      case "C" -> {
        int v = number.intValue();
        yield List.of(VariableType.CHAR.name() + "|" + v, VariableType.INT.name() + "|" + v);
      }
      case "J" -> List.of(VariableType.LONG.name() + "|" + number.longValue());
      case "F" -> List.of(VariableType.FLOAT.name() + "|" + Float.toString(number.floatValue()));
      case "D" -> List.of(VariableType.DOUBLE.name() + "|" + Double.toString(number.doubleValue()));
      case "Z" -> List.of(VariableType.BOOLEAN.name() + "|" + (number.intValue() != 0));
      default -> List.of();
    };
  }

  /**
   * The text range of a field's declaration initializer, or null when the field is not printed
   * with one. Only a declaration counts: the name must follow a type on its line, and a field
   * assignment in a method body is written with a receiver.
   */
  private static int[] initializerRange(String text, List<int[]> spans, String name) {
    java.util.regex.Matcher matcher = java.util.regex.Pattern
      .compile("\\b" + java.util.regex.Pattern.quote(name) + "\\s*=").matcher(text);
    for (int[] span : spans) {
      matcher.region(span[0], span[1]);
      while (matcher.find()) {
        int start = matcher.start();
        int before = start - 1;
        while (before >= span[0] && (text.charAt(before) == ' ' || text.charAt(before) == '\t')) {
          before--;
        }
        if (before < span[0]) {
          continue;
        }
        char c = text.charAt(before);
        if (!Character.isJavaIdentifierPart(c) && c != '>' && c != ']') {
          continue;
        }
        int i = matcher.end();
        int depth = 0;
        while (i < span[1]) {
          char ch = text.charAt(i);
          if (ch == '(' || ch == '[' || ch == '{') {
            depth++;
          }
          else if (ch == ')' || ch == ']' || ch == '}') {
            if (depth == 0) {
              break;
            }
            depth--;
          }
          else if (ch == ';' && depth == 0) {
            break;
          }
          i++;
        }
        return new int[]{start, i};
      }
    }
    return null;
  }

  /** The literal key of an initializer that is one literal, or null for anything else. */
  private static String literalKey(String literal) {
    if (literal.isEmpty()) {
      return null;
    }
    if (literal.charAt(0) == '"') {
      int end = skipQuoted(literal, 0, '"');
      String value = end == literal.length() ? unescape(literal.substring(1, end - 1)) : null;
      return value == null ? null : VariableType.STRING.name() + "|" + value;
    }
    if (literal.charAt(0) == '\'') {
      int end = skipQuoted(literal, 0, '\'');
      Integer value = end == literal.length() ? charValue(literal.substring(1, end - 1)) : null;
      return value == null ? null : VariableType.CHAR.name() + "|" + value;
    }
    if (literal.equals("true") || literal.equals("false")) {
      return VariableType.BOOLEAN.name() + "|" + literal;
    }
    boolean negative = literal.charAt(0) == '-';
    String body = negative ? literal.substring(1) : literal;
    if (body.isEmpty()) {
      return null;
    }
    char suffix = body.charAt(body.length() - 1);
    char last = Character.toLowerCase(suffix);
    if (last == 'f' || last == 'd' || last == 'l') {
      body = body.substring(0, body.length() - 1);
    }
    else {
      suffix = '\0';
    }
    boolean hex = body.startsWith("0x") || body.startsWith("0X") || body.startsWith("0b") || body.startsWith("0B");
    if (!hex) {
      for (int i = 0; i < body.length(); i++) {
        char c = body.charAt(i);
        if (!Character.isDigit(c) && c != '.' && c != 'e' && c != 'E' && c != '+' && c != '-' && c != '_') {
          return null;
        }
      }
    }
    else {
      for (int i = 2; i < body.length(); i++) {
        char c = body.charAt(i);
        if (Character.digit(c, 16) < 0 && c != '_') {
          return null;
        }
      }
    }
    String digits = body.replace("_", "");
    try {
      if (last == 'f') {
        float v = Float.parseFloat(digits);
        return VariableType.FLOAT.name() + "|" + Float.toString(negative ? -v : v);
      }
      if (last == 'd') {
        double v = Double.parseDouble(digits);
        return VariableType.DOUBLE.name() + "|" + Double.toString(negative ? -v : v);
      }
      if (last == 'l') {
        Long v = parseLong(digits);
        return v == null ? null : VariableType.LONG.name() + "|" + (negative ? -v : v);
      }
      if (digits.indexOf('.') >= 0 || digits.indexOf('e') >= 0 || digits.indexOf('E') >= 0) {
        double v = Double.parseDouble(digits);
        return VariableType.DOUBLE.name() + "|" + Double.toString(negative ? -v : v);
      }
      Long v = parseLong(digits);
      return v == null ? null : VariableType.INT.name() + "|" + (negative ? -v : v);
    }
    catch (NumberFormatException e) {
      return null;
    }
  }

  /**
   * The classes whose {@code Class} entries open the constant pool, in first-naming order.
   *
   * <p>javac attributes the constant field initializers before it generates any code, and naming
   * {@code Owner.NAME} interns the owner's {@code Class} entry and its name right there. The pool
   * therefore opens with those entries as consecutive {@code Class}+name pairs, in the order the
   * source first named each owner; whatever is generated later (a super call, a {@code new})
   * follows them. A pair that some generated code produced still sits at the boundary, so naming
   * it again at a constant initializer cannot move it when the earlier pairs keep their order.
   */
  private static List<String> prefixOwners(StructClass cls) {
    List<String> owners = new ArrayList<>();
    List<PooledConstant> pool = cls.getPool().getPool();
    int i = 1;
    while (i + 1 < pool.size()) {
      if (!(pool.get(i) instanceof PrimitiveConstant entry) || entry.type != CodeConstants.CONSTANT_Class
          || entry.index != i + 1 || entry.getString() == null) {
        break;
      }
      if (!(pool.get(i + 1) instanceof PrimitiveConstant name)
          || name.type != CodeConstants.CONSTANT_Utf8 || !entry.getString().equals(name.getString())) {
        break;
      }
      owners.add(entry.getString());
      i += 2;
    }
    return owners;
  }

  /** A foreign owner's constant, written with a qualifier that resolves inside this class. */
  private record SourceConstant(String name, VariableType kind, Object value) {
  }

  /** The accessible constant fields of a prefix owner, printed for this class's scope. */
  private static List<SourceConstant> sourceConstants(String owner, StructClass site,
                                                     List<String> imports, String packageName) {
    return sourceConstants(owner, site, imports, packageName, null);
  }

  /**
   * The same, with a root class whose simple name must qualify the owner.
   *
   * <p>{@code Own.Nested.CONST} interns the own class's {@code Class} entry before the nested
   * owner's, which a fully qualified name does not order the same way; the pool's own pair before
   * the nested pair is the record of that form.
   */
  private static List<SourceConstant> sourceConstants(String owner, StructClass site,
                                                     List<String> imports, String packageName,
                                                     String root) {
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return List.of();
    }
    String qualifier = root != null && owner.startsWith(root + "$")
      ? rootedQualifier(owner, root, site) : qualifier(owner, site, imports, packageName);
    if (qualifier == null) {
      return List.of();
    }
    boolean samePackage = packageName.equals(packageOf(owner));
    boolean sameNest = nestOf(owner).equals(nestOf(site.qualifiedName));
    List<SourceConstant> sources = new ArrayList<>();
    for (StructField field : cls.getFields()) {
      int access = field.getAccessFlags();
      if ((access & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      boolean accessible = (access & CodeConstants.ACC_PUBLIC) != 0
        || ((access & CodeConstants.ACC_PRIVATE) == 0 && samePackage)
        || ((access & CodeConstants.ACC_PRIVATE) != 0 && sameNest);
      if (!accessible) {
        continue;
      }
      PrimitiveConstant value = constantValue(cls, field);
      VariableType kind = value == null ? null : kind(field.getDescriptor());
      if (value == null || kind == null || value.value == null) {
        continue;
      }
      sources.add(new SourceConstant(qualifier + "." + field.getName(), kind, value.value));
    }
    // The same inherited fields addOwnerCandidates reads, written through the owner's name.
    if (anonymous(owner)) {
      return sources; // an anonymous class has no writable name
    }
    for (InheritedConstant inherited : inheritedConstants(cls)) {
      if (inherited.declaring() == cls
          || (inherited.field().getAccessFlags() & CodeConstants.ACC_PUBLIC) == 0) {
        continue;
      }
      sources.add(new SourceConstant(qualifier + "." + inherited.field().getName(),
        inherited.kind(), inherited.value()));
    }
    return sources;
  }

  /** The source-level prefix that names a foreign class's constant here, or null if unnameable. */
  private static String qualifier(String owner, StructClass site, List<String> imports,
                                  String packageName) {
    String simple = simpleName(owner);
    boolean nested = owner.contains("$");
    boolean inScope = nestOf(owner).equals(nestOf(site.qualifiedName))
      || imports.contains(owner.replace('/', '.'))
      || (!nested && packageName.equals(packageOf(owner)));
    if (nested && publiclyNameable(owner, packageName)) {
      // A nested type's simple name can be shadowed in the class whose body holds the site (an
      // inherited `Entry` hides the nested `Outer.Entry` inside Outer's own subclass), and the
      // dotted source name cannot. The pool entry is the same binary name either way.
      String dotted = dottedSourceName(owner);
      if (dotted != null) {
        return dotted;
      }
    }
    if (inScope) {
      return simple;
    }
    if (nested) {
      return anonymous(owner) || !publiclyNameable(owner, packageName) ? null
        : owner.replace('/', '.').replace('$', '.');
    }
    return owner.replace('/', '.');
  }

  /** The name of an owner nested inside {@code root}, written from the root's simple name. */
  private static String rootedQualifier(String owner, String root, StructClass site) {
    String rest = owner.substring(root.length() + 1).replace('$', '.');
    String head = root.equals(site.qualifiedName) ? simpleName(root) : dottedSourceName(root);
    if (head == null || head.isEmpty() || !Character.isJavaIdentifierStart(head.charAt(0))) {
      return null;
    }
    for (String part : rest.split("\\.")) {
      if (part.isEmpty() || !Character.isJavaIdentifierStart(part.charAt(0))) {
        return null;
      }
    }
    return head + "." + rest;
  }

  /** The dotted source name of a nested class, or null when a segment is not an identifier. */
  private static String dottedSourceName(String owner) {
    StringBuilder out = new StringBuilder(owner.length());
    for (int i = 0; i < owner.length(); i++) {
      char c = owner.charAt(i);
      out.append(c == '/' || c == '$' ? '.' : c);
    }
    for (String part : out.toString().split("\\.")) {
      if (part.isEmpty() || !Character.isJavaIdentifierStart(part.charAt(0))) {
        return null; // a local class's numbered segment has no source spelling
      }
      for (int i = 1; i < part.length(); i++) {
        if (!Character.isJavaIdentifierPart(part.charAt(i))) {
          return null;
        }
      }
    }
    return out.toString();
  }

  /** The first site that names this owner inside one of the class's constant initializers, or null. */
  private static Site firstInitializerSite(List<Site> sites, String owner, List<int[]> spans,
                                           Map<String, List<int[]>> initializers) {
    Site first = null;
    for (Site site : sites) {
      if (owner.equals(site.owner()) && inside(spans, site.start())
          && insideInitializer(initializers, site.start())
          && (first == null || site.start() < first.start())) {
        first = site;
      }
    }
    return first;
  }

  /**
   * The earliest initializer site among the prefix owners from {@code from} on, or -1.
   *
   * <p>The owners are named in this order, so a naming placed after an already reproduced later
   * pair would swap the two {@code Class} entries in the pool.
   */
  private static int initializerLimit(List<Site> sites, List<String> owners, int from,
                                      List<int[]> spans, Map<String, List<int[]>> initializers) {
    int limit = -1;
    for (int k = from; k < owners.size(); k++) {
      Site site = firstInitializerSite(sites, owners.get(k), spans, initializers);
      if (site != null && (limit < 0 || site.start() < limit)) {
        limit = site.start();
      }
    }
    return limit;
  }

  /** Whether the text position lies inside one of the constant initializers. */
  private static boolean insideInitializer(Map<String, List<int[]>> initializers, int position) {
    for (List<int[]> ranges : initializers.values()) {
      for (int[] range : ranges) {
        if (position >= range[0] && position < range[1]) {
          return true;
        }
      }
    }
    return false;
  }

  /** Whether a site already rewrites part of this initializer. */
  private static boolean occupied(List<Site> sites, int[] range) {
    for (Site site : sites) {
      if (site.start() < range[1] && site.end() > range[0]) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether another constant of the class itself fits this site just as well.
   *
   * <p>An equal folded value is identical whichever name produced it, so two constants of one class
   * with the same value are interchangeable to the pool, and a foreign owner is the pool's evidence
   * either way. Inside a constant field initializer the pool places no site at all, so naming one of
   * several same-valued constants of the class being printed is a guess that can even close a cycle
   * between initializers the original source never had. The field whose own initializer holds the
   * site is not an alternative: it cannot name itself.
   */
  private static boolean ambiguousInitializer(Constant constant, String key, String own, int start,
                                              Map<String, List<int[]>> ownInitializers) {
    if (!constant.owner().equals(own) || !insideInitializer(ownInitializers, start)) {
      return false;
    }
    int bar = key.indexOf('|');
    StructClass cls = bar < 0 ? null : DecompilerContext.getStructContext().getClass(own);
    if (cls == null) {
      return false;
    }
    int fits = 0;
    for (StructField field : cls.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      PrimitiveConstant value = constantValue(cls, field);
      VariableType kind = value == null ? null : kind(field.getDescriptor());
      if (value == null || kind == null || value.value == null) {
        continue;
      }
      if (holdsInitializer(ownInitializers, field.getName(), start)) {
        continue; // the field this site initializes cannot name itself
      }
      String printed = kind == VariableType.BOOLEAN && value.value instanceof Integer flag
        ? Boolean.toString(flag != 0) : String.valueOf(value.value);
      if (fitsSite(key, kind, printed)) {
        fits++;
      }
    }
    return fits > 1; // the site fits the selected constant and at least one other
  }

  /** Whether a constant of this kind and printed value can stand where the site's literal stands. */
  private static boolean fitsSite(String key, VariableType kind, String printed) {
    int bar = key.indexOf('|');
    if (bar < 0 || !printed.equals(key.substring(bar + 1))) {
      return false;
    }
    VariableType site;
    try {
      site = VariableType.valueOf(key.substring(0, bar));
    }
    catch (IllegalArgumentException e) {
      return false;
    }
    return switch (site) {
      case INT -> kind == VariableType.INT || kind == VariableType.BYTE
        || kind == VariableType.SHORT || kind == VariableType.CHAR;
      case LONG -> kind == VariableType.LONG || kind == VariableType.INT
        || kind == VariableType.BYTE || kind == VariableType.SHORT || kind == VariableType.CHAR;
      case BYTE -> kind == VariableType.BYTE;
      case SHORT -> kind == VariableType.SHORT;
      case CHAR -> kind == VariableType.CHAR;
      default -> kind == site;
    };
  }

  /** Whether the named field's own initializer holds this text position. */
  private static boolean holdsInitializer(Map<String, List<int[]>> initializers, String name,
                                          int position) {
    for (int[] range : initializers.getOrDefault(name, List.of())) {
      if (position >= range[0] && position < range[1]) {
        return true;
      }
    }
    return false;
  }

  /** An expression over a source constant that folds to {@code target}'s exact value, or null. */
  private static String constantExpression(FieldConstant target, VariableType sourceKind,
                                           Object sourceValue, String name) {
    VariableType t = target.kind();
    if (t == VariableType.BOOLEAN || sourceKind == VariableType.BOOLEAN) {
      return booleanExpression(target, sourceKind, sourceValue, name);
    }
    if (!numeric(t) || !numeric(sourceKind)) {
      return t == sourceKind && target.value().equals(sourceValue) ? name : null;
    }
    if (foldsTo(sourceValue, sourceKind, target)) {
      return name;
    }
    VariableType u = sourceKind == VariableType.CHAR ? VariableType.INT : sourceKind;
    if (foldsTo(negate(sourceValue, u), u, target)) {
      return "-" + name;
    }
    if ((sourceKind == VariableType.INT || sourceKind == VariableType.CHAR
        || sourceKind == VariableType.LONG) && foldsTo(complement(sourceValue, u), u, target)) {
      return "~" + name;
    }
    String binary = binaryExpression(target, sourceKind, sourceValue, name);
    if (binary != null) {
      return binary;
    }
    // A constant of a wider kind needs an explicit cast before arithmetic in the target's kind:
    // `(int) Owner.FLOAT_CONST + 1`. A cast of a constant variable is itself a constant
    // expression, and javac folds it exactly as the literal's value.
    return castExpression(target, sourceKind, sourceValue, name);
  }

  /** The boolean literal's source form: the constant itself, or its negation. */
  private static String booleanExpression(FieldConstant target, VariableType sourceKind,
                                          Object sourceValue, String name) {
    if (sourceKind != VariableType.BOOLEAN || !(sourceValue instanceof Integer source)
        || !(target.value() instanceof Boolean value)) {
      return null;
    }
    return (source != 0) == value ? name : "!" + name;
  }

  /** An expression whose source constant is cast to the target's kind before arithmetic. */
  private static String castExpression(FieldConstant target, VariableType sourceKind,
                                       Object sourceValue, String name) {
    VariableType t = target.kind();
    Object cast = castValue(sourceValue, sourceKind, t);
    if (cast == null) {
      return null;
    }
    String castName = "(" + javaName(t) + ") " + name;
    if (foldsTo(cast, t, target)) {
      return castName;
    }
    return binaryExpression(target, t, cast, castName);
  }

  /** The value of {@code (to) value} when javac folds the cast, or null for a widening or lossy pair. */
  private static Object castValue(Object value, VariableType from, VariableType to) {
    if (from == VariableType.CHAR) {
      from = VariableType.INT;
    }
    if (!(value instanceof Number number)) {
      return null;
    }
    return switch (to) {
      case INT -> from == VariableType.LONG ? Integer.valueOf((int) number.longValue())
        : from == VariableType.FLOAT ? Integer.valueOf((int) number.floatValue())
        : from == VariableType.DOUBLE ? Integer.valueOf((int) number.doubleValue()) : null;
      case LONG -> from == VariableType.INT ? Long.valueOf((long) number.intValue())
        : from == VariableType.FLOAT ? Long.valueOf((long) number.floatValue())
        : from == VariableType.DOUBLE ? Long.valueOf((long) number.doubleValue()) : null;
      case FLOAT -> from == VariableType.INT ? Float.valueOf((float) number.intValue())
        : from == VariableType.LONG ? Float.valueOf((float) number.longValue())
        : from == VariableType.DOUBLE ? Float.valueOf((float) number.doubleValue()) : null;
      case DOUBLE -> from == VariableType.INT ? Double.valueOf((double) number.intValue())
        : from == VariableType.LONG ? Double.valueOf((double) number.longValue())
        : from == VariableType.FLOAT ? Double.valueOf((double) number.floatValue()) : null;
      default -> null;
    };
  }

  /** Whether an explicit cast is the only way this source kind reaches the target kind. */
  private static boolean castable(VariableType from, VariableType to) {
    if (from == VariableType.CHAR) {
      from = VariableType.INT;
    }
    return switch (to) {
      case INT -> from == VariableType.LONG || from == VariableType.FLOAT || from == VariableType.DOUBLE;
      case LONG -> from == VariableType.FLOAT || from == VariableType.DOUBLE;
      case FLOAT -> from == VariableType.DOUBLE;
      default -> false;
    };
  }

  private static String javaName(VariableType kind) {
    return switch (kind) {
      case INT -> "int";
      case LONG -> "long";
      case FLOAT -> "float";
      case DOUBLE -> "double";
      case BOOLEAN -> "boolean";
      case CHAR -> "char";
      case BYTE -> "byte";
      case SHORT -> "short";
      case STRING -> "String";
    };
  }

  /**
   * A binary expression over the source constant and a literal solved from the target value.
   *
   * <p>The operand types are promoted as javac promotes them, so a float target multiplied by an
   * int constant is a float expression, and every solved literal is checked by folding the whole
   * expression in that promoted type. A literal that only verifies rounded is preferred integral,
   * which keeps the common {@code 180.0F / PI} shape.
   */
  private static String binaryExpression(FieldConstant target, VariableType sourceKind,
                                         Object sourceValue, String name) {
    VariableType p = promote(sourceKind, target.kind());
    if (p == null || !assignmentAllowed(p, target.kind())) {
      return null;
    }
    Object converted = convert(sourceValue, sourceKind, p);
    if (converted == null) {
      return null;
    }
    if (p == VariableType.INT || p == VariableType.LONG) {
      long g = ((Number) converted).longValue();
      Object expected = convert(target.value(), target.kind(), p);
      if (expected == null) {
        return null;
      }
      long v = ((Number) expected).longValue();
      int width = p == VariableType.LONG ? 64 : 32;
      // The bit-mask idiom first: (1 << BITS) - 1 reads like the field it defines.
      long mask = wrap((1L << ((int) g & (width - 1))) - 1L, p);
      if (mask == v) {
        return p == VariableType.LONG ? "(1L << " + name + ") - 1L" : "(1 << " + name + ") - 1";
      }
      if (g != 0 && holds(Op.MUL, g, wrap(v / g, p), p, target, true)) {
        return name + " * " + integral(wrap(v / g, p), p);
      }
      if (v != 0 && wrap(g / v, p) != 0
          && holds(Op.DIV, g, wrap(g / v, p), p, target, true)) {
        return name + " / " + integral(wrap(g / v, p), p);
      }
      if (g != 0 && holds(Op.DIV, wrap(v * g, p), g, p, target, true)) {
        return integral(wrap(v * g, p), p) + " / " + name;
      }
      for (int shift = 0; shift < width; shift++) {
        if (holds(Op.SHL, g, shift, p, target, true)) {
          return name + " << " + shift;
        }
      }
      if (g >= 0 && g < width) {
        if (holds(Op.SHL, wrap(v >>> g, p), g, p, target, true)) {
          return integral(wrap(v >>> g, p), p) + " << " + name;
        }
        if (holds(Op.SHR, wrap(v << g, p), g, p, target, true)) {
          return integral(wrap(v << g, p), p) + " >> " + name;
        }
      }
      if (holds(Op.ADD, g, wrap(v - g, p), p, target, true)) {
        return name + " + " + integral(wrap(v - g, p), p);
      }
      if (holds(Op.SUB, g, wrap(g - v, p), p, target, true)) {
        return name + " - " + integral(wrap(g - v, p), p);
      }
      if (holds(Op.SUB, wrap(v + g, p), g, p, target, true)) {
        return integral(wrap(v + g, p), p) + " - " + name;
      }
      if (holds(Op.OR, g, v, p, target, true)) {
        return name + " | " + integral(v, p);
      }
      if (holds(Op.AND, g, v | ~g, p, target, true)) {
        return name + " & " + integral(v | ~g, p);
      }
      if (holds(Op.XOR, g, g ^ v, p, target, true)) {
        return name + " ^ " + integral(g ^ v, p);
      }
      return null;
    }
    // A floating-point expression: solve in the target's own precision.
    double g = ((Number) converted).doubleValue();
    Object expected = convert(target.value(), target.kind(), p);
    if (expected == null || !Double.isFinite(g)) {
      return null;
    }
    double v = ((Number) expected).doubleValue();
    if (!Double.isFinite(v)) {
      return null;
    }
    // The value a literal must have for each shape, scored by how round it reads: an integral
    // literal first (180.0F / PI, MAX_FOOD * 1F), then one that only checks out rounded, then
    // the exact quotient. Ties go to the smaller magnitude, then to the earlier shape.
    List<FpCandidate> candidates = new ArrayList<>();
    if (g != 0.0) {
      candidates.add(new FpCandidate(Op.MUL, v / g, false, name));
      candidates.add(new FpCandidate(Op.DIV, v * g, true, name));
    }
    if (v != 0.0) {
      candidates.add(new FpCandidate(Op.DIV, g / v, false, name));
    }
    candidates.add(new FpCandidate(Op.ADD, v - g, false, name));
    candidates.add(new FpCandidate(Op.SUB, g - v, false, name));
    candidates.add(new FpCandidate(Op.SUB, v + g, true, name));
    FpCandidate best = null;
    int bestScore = Integer.MAX_VALUE;
    double bestMagnitude = Double.MAX_VALUE;
    for (FpCandidate candidate : candidates) {
      if (!Double.isFinite(candidate.solved())) {
        continue;
      }
      int score;
      double chosen;
      if (Math.rint(candidate.solved()) == candidate.solved()
          && verifyFp(candidate, g, candidate.solved(), p, target)) {
        score = 0;
        chosen = candidate.solved();
      }
      else if (verifyFp(candidate, g, Math.rint(candidate.solved()), p, target)) {
        score = 1;
        chosen = Math.rint(candidate.solved());
      }
      else if (verifyFp(candidate, g, candidate.solved(), p, target)) {
        score = 2;
        chosen = candidate.solved();
      }
      else {
        continue;
      }
      if (score < bestScore || (score == bestScore && Math.abs(chosen) < bestMagnitude)) {
        best = new FpCandidate(candidate.op(), chosen, candidate.solvedLeft(), name);
        bestScore = score;
        bestMagnitude = Math.abs(chosen);
      }
    }
    if (best == null) {
      return null;
    }
    String text = fp(best.solved(), p);
    return best.solvedLeft() ? text + " " + symbol(best.op()) + " " + name
      : name + " " + symbol(best.op()) + " " + text;
  }

  /** One solved floating-point shape: the constant stands opposite a solved literal. */
  private record FpCandidate(Op op, double solved, boolean solvedLeft, String name) {
  }

  private static boolean verifyFp(FpCandidate candidate, double constant, double solved,
                                  VariableType p, FieldConstant target) {
    return candidate.solvedLeft()
      ? holdsFp(candidate.op(), solved, constant, p, target, true)
      : holdsFp(candidate.op(), constant, solved, p, target, true);
  }

  private static String symbol(Op op) {
    return switch (op) {
      case ADD -> "+";
      case SUB -> "-";
      case MUL -> "*";
      case DIV -> "/";
      case SHL -> "<<";
      case SHR -> ">>";
      case AND -> "&";
      case OR -> "|";
      case XOR -> "^";
    };
  }

  private static boolean holds(Op op, long left, long right, VariableType p,
                               FieldConstant target, boolean usable) {
    if (!usable) {
      return false;
    }
    Object result = evaluate(op, left, right, p);
    return result != null && foldsTo(result, p, target);
  }

  private static boolean holdsFp(Op op, double left, double right, VariableType p,
                                 FieldConstant target, boolean usable) {
    if (!usable) {
      return false;
    }
    double result;
    if (p == VariableType.FLOAT) {
      float a = (float) left;
      float b = (float) right;
      result = switch (op) {
        case ADD -> a + b;
        case SUB -> a - b;
        case MUL -> a * b;
        case DIV -> a / b;
        default -> Double.NaN;
      };
    }
    else {
      result = switch (op) {
        case ADD -> left + right;
        case SUB -> left - right;
        case MUL -> left * right;
        case DIV -> left / right;
        default -> Double.NaN;
      };
    }
    if (!Double.isFinite(result)) {
      return false;
    }
    // The cast keeps the conditional from promoting both branches to double.
    Object boxed = p == VariableType.FLOAT
      ? (Object) Float.valueOf((float) result) : (Object) Double.valueOf(result);
    return foldsTo(boxed, p, target);
  }

  private static Object evaluate(Op op, long left, long right, VariableType p) {
    if (p == VariableType.INT) {
      int a = (int) left;
      int b = (int) right;
      return switch (op) {
        case ADD -> a + b;
        case SUB -> a - b;
        case MUL -> a * b;
        case DIV -> a / b;
        case SHL -> a << b;
        case SHR -> a >> b;
        case AND -> a & b;
        case OR -> a | b;
        case XOR -> a ^ b;
      };
    }
    return switch (op) {
      case ADD -> left + right;
      case SUB -> left - right;
      case MUL -> left * right;
      case DIV -> left / right;
      case SHL -> left << right;
      case SHR -> left >> right;
      case AND -> left & right;
      case OR -> left | right;
      case XOR -> left ^ right;
    };
  }

  /** Whether the value folds, through the assignment conversion, to the target's exact value. */
  private static boolean foldsTo(Object value, VariableType from, FieldConstant target) {
    if (value == null || !assignmentAllowed(from, target.kind())) {
      return false;
    }
    Object converted = convert(value, from, target.kind());
    return converted != null && converted.equals(target.value());
  }

  private static boolean numeric(VariableType kind) {
    return kind == VariableType.INT || kind == VariableType.CHAR || kind == VariableType.LONG
      || kind == VariableType.FLOAT || kind == VariableType.DOUBLE;
  }

  /** Whether naming this constant enters no value into the pool: it compiles to an immediate. */
  private static boolean immediateConstant(SourceConstant source) {
    if (source.kind() == VariableType.BOOLEAN) {
      return true; // a boolean folds to iconst_0/iconst_1
    }
    if (source.value() instanceof Character value) {
      return value <= Short.MAX_VALUE;
    }
    return source.kind() == VariableType.INT && source.value() instanceof Integer value
      && value >= Short.MIN_VALUE && value <= Short.MAX_VALUE;
  }

  /** The pool key a constant's own value would occupy, matching {@link #pooledKeys}. */
  private static String constantKey(SourceConstant source) {
    return source.value() instanceof Character value
      ? VariableType.CHAR.name() + "|" + (int) value
      : source.kind() + "|" + source.value();
  }

  /**
   * Whether naming the constant leaves the pool untouched.
   *
   * <p>A constant whose value javac folds to an immediate enters nothing, and a value the pool
   * already holds below the pair is reused. Any other value would be entered right after the
   * pair, so a naming that would introduce one cannot reproduce the pool.
   */
  private static boolean immediateKey(String key) {
    if (key.startsWith(VariableType.BOOLEAN.name() + "|")) {
      return true;
    }
    if (!key.startsWith(VariableType.INT.name() + "|")
        && !key.startsWith(VariableType.CHAR.name() + "|")) {
      return false;
    }
    try {
      long value = Long.parseLong(key.substring(key.indexOf('|') + 1));
      return value >= Short.MIN_VALUE && value <= Short.MAX_VALUE;
    }
    catch (NumberFormatException e) {
      return false;
    }
  }

  /**
   * Whether every literal of the solved expression enters no pool entry the pair did not have.
   *
   * <p>A null set accepts any literal: a constant field initializer is folded at attribution, so
   * none of its literals reaches the pool.
   */
  private static boolean poolFree(String expression, Set<String> pooledBefore) {
    for (int i = 0; i < expression.length(); i++) {
      char c = expression.charAt(i);
      if (!Character.isDigit(c) || (i > 0 && isIdentifierPart(expression.charAt(i - 1)))) {
        continue;
      }
      int end = i;
      boolean dot = false;
      while (end < expression.length()) {
        char d = expression.charAt(end);
        if (Character.isLetterOrDigit(d) || d == '_') {
          end++;
          continue;
        }
        if (d == '.' && !dot) {
          dot = true;
          end++;
          continue;
        }
        if ((d == '+' || d == '-') && end > i
            && (expression.charAt(end - 1) == 'e' || expression.charAt(end - 1) == 'E')) {
          end++;
          continue;
        }
        break;
      }
      String key = literalKey(expression.substring(i, end));
      if (key != null && !immediateKey(key) && pooledBefore != null && !pooledBefore.contains(key)) {
        return false;
      }
      i = end - 1;
    }
    return true;
  }

  /** Binary numeric promotion: char widens to int, then the wider of the two types wins. */
  private static VariableType promote(VariableType a, VariableType b) {
    if (!numeric(a) || !numeric(b)) {
      return null;
    }
    VariableType left = a == VariableType.CHAR ? VariableType.INT : a;
    VariableType right = b == VariableType.CHAR ? VariableType.INT : b;
    return rank(left) >= rank(right) ? left : right;
  }

  private static int rank(VariableType kind) {
    return switch (kind) {
      case INT -> 0;
      case LONG -> 1;
      case FLOAT -> 2;
      case DOUBLE -> 3;
      default -> -1;
    };
  }

  /** Whether an expression of type {@code from} is assignable to a field of type {@code to}. */
  private static boolean assignmentAllowed(VariableType from, VariableType to) {
    if (from == to) {
      return true;
    }
    return switch (to) {
      case LONG -> from == VariableType.INT || from == VariableType.CHAR;
      case FLOAT -> from == VariableType.INT || from == VariableType.CHAR || from == VariableType.LONG;
      case DOUBLE -> from == VariableType.INT || from == VariableType.CHAR
        || from == VariableType.LONG || from == VariableType.FLOAT;
      case INT -> from == VariableType.CHAR;
      case CHAR -> from == VariableType.INT;
      default -> false;
    };
  }

  /** The value an expression of type {@code from} has after assignment to type {@code to}. */
  private static Object convert(Object value, VariableType from, VariableType to) {
    if (from == to) {
      return value;
    }
    if (from == VariableType.FLOAT) {
      return to == VariableType.DOUBLE ? Double.valueOf(((Float) value).doubleValue()) : null;
    }
    if (from != VariableType.INT && from != VariableType.CHAR && from != VariableType.LONG) {
      return null;
    }
    long integral = ((Number) value).longValue();
    if (to == VariableType.CHAR && (integral < Character.MIN_VALUE || integral > Character.MAX_VALUE)) {
      return null;
    }
    return switch (to) {
      case INT, CHAR -> Integer.valueOf((int) integral);
      case LONG -> Long.valueOf(integral);
      case FLOAT -> Float.valueOf((float) integral);
      case DOUBLE -> Double.valueOf((double) integral);
      default -> null;
    };
  }

  private static Object negate(Object value, VariableType type) {
    return switch (type) {
      case INT -> Integer.valueOf(-((Number) value).intValue());
      case LONG -> Long.valueOf(-((Number) value).longValue());
      case FLOAT -> Float.valueOf(-((Float) value));
      case DOUBLE -> Double.valueOf(-((Double) value));
      default -> null;
    };
  }

  private static Object complement(Object value, VariableType type) {
    return type == VariableType.LONG
      ? Long.valueOf(~((Number) value).longValue())
      : Integer.valueOf(~((Number) value).intValue());
  }

  private static long wrap(long value, VariableType p) {
    return p == VariableType.INT ? (int) value : value;
  }

  private static String integral(long value, VariableType p) {
    return p == VariableType.INT ? Integer.toString((int) value) : value + "L";
  }

  private static String fp(double value, VariableType p) {
    return p == VariableType.FLOAT ? Float.toString((float) value) + "F" : Double.toString(value);
  }

  /**
   * Splits a class's pool into the classes it names and the classes whose entry it explains.
   *
   * <p>A {@code Class} entry is evidence that the source named one of that class's constants only
   * when nothing else in the class file accounts for it. Field and method references, instruction
   * operands, catch and throws clauses, the class's own hierarchy and the nesting attributes all
   * put a {@code Class} entry into the pool without any constant being named, and the jar's own
   * {@code InnerClasses} and {@code NestMembers} entries explain every one of the class's nested
   * types.
   */
  private static void collectPool(StructClass cls, Set<String> present, Set<String> explained,
                                  Set<String> referenced, Map<Integer, FirstUse> uses) {
    if (cls == null) {
      return;
    }
    List<PooledConstant> pool = cls.getPool().getPool();
    for (PooledConstant constant : pool) {
      if (constant instanceof PrimitiveConstant primitive && primitive.type == CodeConstants.CONSTANT_Class
          && primitive.getString() != null) {
        present.add(primitive.getString());
      } else if (constant instanceof LinkConstant link && link.classname != null) {
        explained.add(link.classname);
        referenced.add(link.classname);
      }
    }
    for (Integer index : uses.keySet()) {
      if (index != null && index > 0 && index < pool.size()
          && pool.get(index) instanceof PrimitiveConstant primitive
          && primitive.type == CodeConstants.CONSTANT_Class && primitive.getString() != null) {
        explained.add(primitive.getString());
      }
    }
    if (cls.superClass != null && cls.superClass.getString() != null) {
      explained.add(cls.superClass.getString());
    }
    for (String name : cls.getInterfaceNames()) {
      explained.add(name);
    }
    StructInnerClassesAttribute inner = cls.getAttribute(StructGeneralAttribute.ATTRIBUTE_INNER_CLASSES);
    if (inner != null) {
      Map<String, Integer> classIndices = classIndices(cls);
      for (StructInnerClassesAttribute.Entry entry : inner.getEntries()) {
        // An entry for a nested type of another class exists because this class's source named
        // that type. When our text does not name it as a type, the naming can only have gone
        // through one of its constants, so the attribute must not dismiss the candidate here.
        boolean ownMember = entry.innerName != null && cls.qualifiedName != null
          && cls.qualifiedName.equals(entry.enclosingName);
        if (entry.innerName != null && ownMember) {
          explained.add(entry.innerName);
        }
        // The attribute is written after every field and method, so it interns the inner class
        // before the outer. An outer Class entry that sits below the inner one was interned
        // earlier, by a folded constant naming in the code, and the attribute does not explain it.
        Integer innerIndex = entry.innerName == null ? null : classIndices.get(entry.innerName);
        Integer outerIndex = entry.enclosingName == null ? null : classIndices.get(entry.enclosingName);
        if (entry.enclosingName != null
            && (innerIndex == null || outerIndex == null || outerIndex > innerIndex)) {
          explained.add(entry.enclosingName);
        }
      }
    }
    StructNestHostAttribute host = cls.getAttribute(StructGeneralAttribute.ATTRIBUTE_NEST_HOST);
    if (host != null) {
      explained.add(host.getHostClass(cls.getPool()));
    }
    StructNestMembersAttribute members = cls.getAttribute(StructGeneralAttribute.ATTRIBUTE_NEST_MEMBERS);
    if (members != null) {
      explained.addAll(members.getClasses(cls.getPool()));
    }
    StructEnclosingMethodAttribute enclosing =
      cls.getAttribute(StructGeneralAttribute.ATTRIBUTE_ENCLOSING_METHOD);
    if (enclosing != null) {
      explained.add(enclosing.getClassName());
    }
    for (StructMethod method : cls.getMethods()) {
      StructExceptionsAttribute exceptions =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_EXCEPTIONS);
      if (exceptions != null) {
        for (int i = 0; i < exceptions.getThrowsExceptions().size(); i++) {
          explained.add(exceptions.getExcClassname(i, cls.getPool()));
        }
      }
    }
  }

  private static boolean isBootstrapOwner(String owner) {
    return owner.startsWith("java/lang/invoke/")
      || owner.equals("java/lang/runtime/ObjectMethods")
      || owner.equals("java/lang/runtime/SwitchBootstraps")
      || owner.startsWith("java/lang/constant/");
  }

  private static void candidate(Map<String, List<Constant>> map, String key, Constant constant) {
    map.computeIfAbsent(key, k -> new ArrayList<>()).add(constant);
  }

  /** Every static final field of the class itself that carries a ConstantValue. */
  private static void ownCandidates(Map<String, List<Constant>> candidates, StructClass own) {
    for (StructField field : own.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      PrimitiveConstant value = constantValue(own, field);
      VariableType kind = value == null ? null : kind(field.getDescriptor());
      if (value == null || kind == null || value.value == null) {
        continue;
      }
      String printed = kind == VariableType.BOOLEAN && value.value instanceof Integer flag
        ? Boolean.toString(flag != 0) : String.valueOf(value.value);
      candidate(candidates, kind + "|" + printed, new Constant(own.qualifiedName, field.getName(), kind));
    }
  }

  /**
   * Whether a class is the owner or a subclass of it.
   *
   * <p>A protected member is accessible inside the body of any subclass, and the body of a nested
   * class is part of its enclosing class's body. The nest host is the class whose text is being
   * scanned for a name, so its superclass chain decides whether a protected constant is writable.
   */
  private static boolean extendsClass(String className, String owner) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    for (int depth = 0; depth < 32 && cls != null; depth++) {
      if (cls.qualifiedName.equals(owner)) {
        return true;
      }
      String superName = cls.superClass == null ? null : cls.superClass.getString();
      if (superName == null) {
        return false;
      }
      cls = DecompilerContext.getStructContext().getClass(superName);
    }
    return false;
  }

  /** The accessible static final fields of one missing owner, as candidates for a literal value. */
  private static void addOwnerCandidates(Map<String, List<Constant>> candidates, String owner,
                                         String nest, String packageName, List<String> imports) {
    addOwnerCandidates(candidates, owner, nest, packageName, imports, false);
  }

  /**
   * The same, with whether the owner is one only a constant naming explains.
   *
   * <p>A protected constant is writable through a subclass's body, but that is the one widening
   * only a pool-unexplained owner needs: an owner the text already names has its {@code Class}
   * entry accounted for, and a second naming can only move the entry to a different point.
   */
  private static void addOwnerCandidates(Map<String, List<Constant>> candidates, String owner,
                                         String nest, String packageName, List<String> imports,
                                         boolean missingOwner) {
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return;
    }
    boolean samePackage = packageName.equals(packageOf(owner));
    boolean imported = imports.contains(simpleName(owner));
    if (!samePackage && !imported && owner.contains("$")
        && !(missingOwner && publiclyNameable(owner, packageName))) {
      // A nested class's binary name cannot be written in source, but its dotted source name can
      // whenever every class of the chain is public: the site printer falls back to that form.
      // Only an owner the pool alone explains may use it; an owner the text already names has its
      // Class entry accounted for, and a second naming would only move it.
      return;
    }
    for (StructField field : cls.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      int access = field.getAccessFlags();
      boolean accessible = (access & CodeConstants.ACC_PUBLIC) != 0
        || ((access & CodeConstants.ACC_PRIVATE) == 0 && samePackage)
        || ((access & CodeConstants.ACC_PROTECTED) != 0 && missingOwner && extendsClass(nest, owner))
        || ((access & CodeConstants.ACC_PRIVATE) != 0 && nestOf(owner).equals(nest));
      if (!accessible) {
        continue;
      }
      StructConstantValueAttribute attribute =
        field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
      if (attribute == null) {
        continue;
      }
      PrimitiveConstant value = cls.getPool().getPrimitiveConstant(attribute.getIndex());
      if (value == null || value.value == null) {
        continue;
      }
      VariableType kind = kind(field.getDescriptor());
      if (kind == null) {
        continue;
      }
      String printed = kind == VariableType.BOOLEAN && value.value instanceof Integer flag
        ? Boolean.toString(flag != 0) : String.valueOf(value.value);
      String key = kind + "|" + printed;
      candidate(candidates, key, new Constant(owner, field.getName(), kind));
      // A double constant used where the source needed a float is written `(float) Owner.NAME`;
      // the printed literal is the float whose value only the double constant reproduces.
      if (kind == VariableType.DOUBLE && value.value instanceof Double number) {
        float narrowed = (float) (double) number;
        if ((double) narrowed != (double) number) {
          candidate(candidates, "FLOATCAST|" + Float.toString(narrowed),
            new Constant(owner, field.getName(), VariableType.DOUBLE));
        }
      }
    }
  }

  /**
   * Adds the inherited constants of an owner whose {@code Class} entry only the source can explain.
   *
   * <p>A referenced owner's entry is whatever the reference that makes it a candidate entered, so
   * its inherited constants would just compete with the owner the pool is really asking for at a
   * site. Where the entry exists solely because a constant was named, the name may resolve to an
   * inherited field, and only then does the pool's record include it.
   */
  private static Set<String> addInheritedCandidates(Map<String, List<Constant>> candidates,
                                                    String owner, String packageName,
                                                    List<String> imports) {
    Set<String> keys = new HashSet<>();
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    // An anonymous class has no writable name, so its inherited constants cannot be written
    // through it (naming one inside its own text is the own-constant rule's business).
    if (cls == null || anonymous(owner)) {
      return keys;
    }
    if (!packageName.equals(packageOf(owner)) && !imports.contains(simpleName(owner))
        && owner.contains("$")) {
      return keys;
    }
    for (InheritedConstant inherited : inheritedConstants(cls)) {
      if (inherited.declaring() == cls
          || (inherited.field().getAccessFlags() & CodeConstants.ACC_PUBLIC) == 0) {
        continue;
      }
      String key = inherited.kind() + "|" + inherited.printed();
      if (tooCommon(key)) {
        continue; // a frequent value cannot pick an inherited name; it fits almost every owner
      }
      candidate(candidates, key, new Constant(owner, inherited.field().getName(), inherited.kind()));
      keys.add(owner + "|" + inherited.field().getName());
    }
    return keys;
  }

  /** A constant field an owner's name resolves to, with the class whose pool holds its value. */
  private record InheritedConstant(StructField field, StructClass declaring, VariableType kind,
                                   Object value) {
    String printed() {
      return kind == VariableType.BOOLEAN && value instanceof Integer flag
        ? Boolean.toString(flag != 0) : String.valueOf(value);
    }
  }

  /**
   * The static final constant fields a name resolves to through {@code cls}: its own, then those
   * inherited from superclasses and superinterfaces.
   *
   * <p>A field a subclass redeclares hides the inherited one; a name two declarations of different
   * values answer cannot be written at all and is dropped. Values come from the declaring class's
   * pool, where the ConstantValue attribute points.
   */
  private static List<InheritedConstant> inheritedConstants(StructClass cls) {
    List<InheritedConstant> fields = new ArrayList<>();
    Map<String, InheritedConstant> byName = new LinkedHashMap<>();
    Set<String> ambiguous = new HashSet<>();
    Deque<StructClass> queue = new ArrayDeque<>();
    Set<String> seen = new HashSet<>();
    queue.add(cls);
    while (!queue.isEmpty()) {
      StructClass current = queue.poll();
      if (current == null || !seen.add(current.qualifiedName)) {
        continue;
      }
      for (StructField field : current.getFields()) {
        if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
            != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
          continue;
        }
        PrimitiveConstant value = constantValue(current, field);
        VariableType kind = value == null ? null : kind(field.getDescriptor());
        if (value == null || kind == null || value.value == null) {
          continue;
        }
        InheritedConstant known = byName.get(field.getName());
        if (known == null) {
          byName.put(field.getName(), new InheritedConstant(field, current, kind, value.value));
        }
        else if (!known.value().equals(value.value)) {
          ambiguous.add(field.getName());
        }
      }
      if (current.superClass != null && current.superClass.getString() != null) {
        StructClass sup = DecompilerContext.getStructContext().getClass(current.superClass.getString());
        if (sup != null) {
          queue.add(sup);
        }
      }
      for (String name : current.getInterfaceNames()) {
        StructClass itf = DecompilerContext.getStructContext().getClass(name);
        if (itf != null) {
          queue.add(itf);
        }
      }
    }
    for (InheritedConstant constant : byName.values()) {
      if (!ambiguous.contains(constant.field().getName())) {
        fields.add(constant);
      }
    }
    return fields;
  }

  private static void collectPool(ClassNode node, Set<String> present, Set<String> explained,
                                  Set<String> referenced) {
    if (node == null) {
      return;
    }
    StructClass cls = node.classStruct;
    if (cls != null) {
      collectPool(cls, present, explained, referenced, firstUses(cls));
    }
    for (ClassNode nested : node.nested) {
      collectPool(nested, present, explained, referenced);
    }
  }

  private static PrimitiveConstant constantValue(StructClass cls, StructField field) {
    StructConstantValueAttribute attribute =
      field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
    if (attribute == null) {
      return null;
    }
    PrimitiveConstant value = cls.getPool().getPrimitiveConstant(attribute.getIndex());
    return value == null || value.value == null ? null : value;
  }

  private static VariableType kind(String descriptor) {
    return switch (descriptor) {
      // A byte or short constant folded into an int literal changes the expression's type when it
      // is named (Pair.of(5) infers Integer, Pair.of(BYTE_CONST) infers Byte), so those owners are
      // never candidates for a plain integer literal. They are candidates only where the printed
      // source already casts the literal to that type, and the name replaces the whole cast.
      case "I" -> VariableType.INT;
      case "C" -> VariableType.CHAR;
      case "Z" -> VariableType.BOOLEAN;
      case "J" -> VariableType.LONG;
      case "F" -> VariableType.FLOAT;
      case "D" -> VariableType.DOUBLE;
      case "B" -> VariableType.BYTE;
      case "S" -> VariableType.SHORT;
      case "Ljava/lang/String;" -> VariableType.STRING;
      default -> null;
    };
  }

  /** An anonymous class's binary name ends in a number, so no qualified form can be written. */
  private static boolean anonymous(String owner) {
    int dollar = owner.lastIndexOf('$');
    if (dollar < 0 || dollar + 1 >= owner.length()) {
      return false;
    }
    for (int i = dollar + 1; i < owner.length(); i++) {
      if (!Character.isDigit(owner.charAt(i))) {
        return false;
      }
    }
    return true;
  }

  /** Whether every class of a nested chain may be named from a file in this package. */
  private static boolean publiclyNameable(String owner, String packageName) {
    String name = owner;
    while (true) {
      StructClass cls = DecompilerContext.getStructContext().getClass(name);
      if (cls == null) {
        return false;
      }
      int dollar = name.lastIndexOf('$');
      // A nested class's class-file flags say public while its InnerClasses entry carries the
      // visibility the source declared (a protected or private member class). Naming it from
      // another package is then a compile error, whatever the class file's own flag says.
      int flags = dollar < 0 ? cls.getAccessFlags() : innerAccess(name, cls);
      if ((flags & CodeConstants.ACC_PUBLIC) == 0 && !packageName.equals(packageOf(name))) {
        return false;
      }
      if (dollar < 0) {
        return true;
      }
      name = name.substring(0, dollar);
    }
  }

  /** The InnerClasses entry's flags for a nested class, falling back to the class file's own. */
  private static int innerAccess(String name, StructClass cls) {
    StructClass outer = DecompilerContext.getStructContext().getClass(name.substring(0, name.lastIndexOf('$')));
    StructInnerClassesAttribute inner = outer == null ? null
      : outer.getAttribute(StructGeneralAttribute.ATTRIBUTE_INNER_CLASSES);
    if (inner != null) {
      for (StructInnerClassesAttribute.Entry entry : inner.getEntries()) {
        if (name.equals(entry.innerName)) {
          return entry.accessFlags;
        }
      }
    }
    return cls.getAccessFlags();
  }

  private static String simpleName(String internal) {
    String name = internal.substring(internal.lastIndexOf('/') + 1);
    int dollar = name.lastIndexOf('$');
    return dollar < 0 ? name : name.substring(dollar + 1);
  }

  /** The top-level class a nest belongs to; private members are shared inside one nest only. */
  private static String nestOf(String internal) {
    int dollar = internal.indexOf('$');
    return dollar < 0 ? internal : internal.substring(0, dollar);
  }

  /** Every class that lexically encloses this one, innermost first. */
  private static List<String> enclosings(String internal) {
    List<String> names = new ArrayList<>();
    String current = internal;
    while (true) {
      int dollar = current.lastIndexOf('$');
      if (dollar < 0) {
        return names;
      }
      current = current.substring(0, dollar);
      names.add(current);
    }
  }

  /** Whether a text position lies in one of the class's own text ranges. */
  private static boolean inside(List<int[]> spans, int position) {
    if (spans == null) {
      return false;
    }
    for (int[] span : spans) {
      if (position >= span[0] && position < span[1]) {
        return true;
      }
    }
    return false;
  }

  /** Whether a simple name in this class's body resolves to the enclosing owner's constant. */
  private static boolean resolvesTo(StructClass site, String owner, String name) {
    StructContext context = DecompilerContext.getStructContext();
    String current = site.qualifiedName;
    while (current != null && !current.equals(owner)) {
      if (declaresField(context.getClass(current), context, name)) {
        return false; // a field of this class or an enclosing one shadows the name
      }
      int dollar = current.lastIndexOf('$');
      if (dollar < 0) {
        return false;
      }
      current = current.substring(0, dollar);
    }
    if (owner.equals(current) && declaresLocal(site, name)) {
      return false; // a local variable of one of this class's bodies shadows the name
    }
    return owner.equals(current);
  }

  /** Whether any method body of the class declares a local or parameter with this name. */
  private static boolean declaresLocal(StructClass cls, String name) {
    for (StructMethod method : cls.getMethods()) {
      StructLocalVariableTableAttribute table =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
      if (table != null && table.getVariables().anyMatch(variable -> name.equals(variable.getName()))) {
        return true;
      }
    }
    return false;
  }

  private static boolean declaresField(StructClass cls, StructContext context, String name) {
    while (cls != null) {
      for (StructField field : cls.getFields()) {
        if (field.getName().equals(name)) {
          return true;
        }
      }
      String superName = cls.superClass == null ? null : cls.superClass.getString();
      cls = superName == null ? null : context.getClass(superName);
    }
    return false;
  }

  private static String packageOf(String internal) {
    int slash = internal.lastIndexOf('/');
    return slash < 0 ? "" : internal.substring(0, slash).replace('/', '.');
  }

  private static List<String> imports(String text) {
    List<String> imports = new ArrayList<>();
    for (String line : text.split("\n")) {
      String trimmed = line.trim();
      if (trimmed.startsWith("import ") && trimmed.endsWith(";")) {
        String name = trimmed.substring("import ".length(), trimmed.length() - 1).trim();
        if (name.startsWith("static ")) {
          name = name.substring("static ".length()).trim();
        }
        int dot = name.lastIndexOf('.');
        imports.add(dot < 0 ? name : name.substring(dot + 1));
        if (dot >= 0) {
          imports.add(name); // the dotted form proves which class a simple name denotes
        }
      }
    }
    return imports;
  }

  private static String packageName(String text) {
    for (String line : text.split("\n")) {
      String trimmed = line.trim();
      if (trimmed.startsWith("package ") && trimmed.endsWith(";")) {
        return trimmed.substring("package ".length(), trimmed.length() - 1).trim();
      }
    }
    return "";
  }

  // ------------------------------------------------------------------ literal scanning

  /** The text ranges of a class's own constant declarations; a constant cannot name itself. */
  private static Map<String, List<int[]>> ownInitializers(String text, StructClass own) {
    return ownInitializers(text, List.of(new int[]{0, text.length()}), own);
  }

  private static Map<String, List<int[]>> ownInitializers(String text, List<int[]> spans, StructClass own) {
    Map<String, List<int[]>> ranges = new HashMap<>();
    for (StructField field : own.getFields()) {
      if (constantValue(own, field) == null) {
        continue;
      }
      List<int[]> found = initializerRanges(text, spans, field.getName());
      if (!found.isEmpty()) {
        ranges.computeIfAbsent(field.getName(), k -> new ArrayList<>()).addAll(found);
      }
    }
    return ranges;
  }

  /**
   * Where the source assigns this field, from its name through the closing semicolon.
   *
   * <p>The printer records a field initializer's offsets under a {@code <field-init NAME>} key, so
   * the text its recorded position falls in is that field's initializer. The range is read from
   * the printed declaration, not from the pool: an initializer of any field, constant or not, is
   * found the same way.
   */
  private static List<int[]> initializerRanges(String text, List<int[]> spans, String name) {
    List<int[]> ranges = new ArrayList<>();
    java.util.regex.Matcher matcher = java.util.regex.Pattern
      .compile("\\b" + java.util.regex.Pattern.quote(name) + "\\s*=")
      .matcher(text);
    for (int[] span : spans) {
      matcher.region(span[0], span[1]);
      while (matcher.find()) {
        int depth = 0;
        int i = matcher.end();
        while (i < span[1]) {
          char c = text.charAt(i);
          if (c == '(' || c == '[' || c == '{') depth++;
          else if (c == ')' || c == ']' || c == '}') { if (depth == 0) break; depth--; }
          else if (c == ';' && depth == 0) break;
          i++;
        }
        ranges.add(new int[]{matcher.start(), i});
      }
    }
    return ranges;
  }

  /**
   * Whether a value successor's printed point and a site lie in one field's initializer.
   *
   * <p>A value successor is the folded value the naming itself entered, so the instruction that
   * uses it is the naming site. When the printer prints that use at a field declaration, its
   * position lies in the {@code <field-init NAME>} buffer, and a literal inside the same printed
   * initializer is the site the value was created at.
   */
  private static boolean pairedInitializer(String text, List<SiteSpace> spaces, List<int[]> spans,
                                           int site, int successorAt) {
    if (spaces == null || successorAt < 0) {
      return false;
    }
    for (SiteSpace space : spaces) {
      if (!space.key().startsWith("<field-init ") || successorAt < space.min()
          || successorAt > space.max()) {
        continue;
      }
      String name = space.key().substring("<field-init ".length(), space.key().length() - 1);
      for (int[] range : initializerRanges(text, spans, name)) {
        if (site >= range[0] && site < range[1]) {
          return true;
        }
      }
    }
    return false;
  }

  private static void scan(String text, Map<String, List<Constant>> candidates, List<String> imports,
                           String packageName, List<Site> sites, String own,
                           Map<String, List<int[]>> ownInitializers) {
    scan(text, 0, text.length(), candidates, imports, packageName, sites, own, ownInitializers,
      NO_PLACEMENT, null, null, null);
  }

  private static void scan(String text, int from, int to, Map<String, List<Constant>> candidates,
                           List<String> imports, String packageName, List<Site> sites, String own,
                           Map<String, List<int[]>> ownInitializers, Placement placement,
                           Map<String, List<Site>> deferred, Set<String> inWindow,
                           Map<String, List<Site>> invented) {
    int i = from;
    while (i < to) {
      char c = text.charAt(i);
      char next = i + 1 < text.length() ? text.charAt(i + 1) : '\0';
      if (c == '/' && next == '/') {
        i = text.indexOf('\n', i);
        if (i < 0) {
          break;
        }
        continue;
      }
      if (c == '/' && next == '*') {
        int end = text.indexOf("*/", i + 2);
        i = end < 0 ? text.length() : end + 2;
        continue;
      }
      if (c == '"') {
        int end = skipQuoted(text, i, '"');
        if (!text.startsWith("\"\"\"", i) && end - 1 > i) {
          String value = unescape(text.substring(i + 1, end - 1));
          if (value != null) {
            // The empty string is a value a string constant can hold and a naming can fold to.
            addSite(sites, i, end, VariableType.STRING + "|" + value, "", candidates, imports, packageName, own, ownInitializers,
              placement, deferred, inWindow, invented);
          }
        }
        i = end;
        continue;
      }
      if (c == '\'') {
        int end = skipQuoted(text, i, '\'');
        if (end - 1 > i) {
          Integer value = charValue(text.substring(i + 1, end - 1));
          if (value != null) {
            addSite(sites, i, end, VariableType.CHAR + "|" + value, "", candidates, imports, packageName, own, ownInitializers,
              placement, deferred, inWindow, invented);
          }
        }
        i = end;
        continue;
      }
      if (Character.isLetter(c) && (i == 0 || !isIdentifierPart(text.charAt(i - 1)))) {
        int end = i;
        while (end < text.length() && isIdentifierPart(text.charAt(end))) {
          end++;
        }
        String word = text.substring(i, end);
        if (word.equals("true") || word.equals("false")) {
          addSite(sites, i, end, VariableType.BOOLEAN + "|" + word, "", candidates, imports, packageName, own, ownInitializers,
            placement, deferred, inWindow, invented);
        }
        i = end;
        continue;
      }
      if (Character.isDigit(c) && (i == 0 || !isIdentifierPart(text.charAt(i - 1)))) {
        i = scanNumber(text, i, sites, candidates, imports, packageName, own, ownInitializers,
          placement, deferred, inWindow, invented);
        continue;
      }
      i++;
    }
  }

  /** The '-' of a unary minus directly before this literal, or -1 for a binary minus. */
  /** Keywords that end a statement or precede an expression, so a minus after one is unary. */
  private static final java.util.Set<String> KEYWORDS = java.util.Set.of(
    "return", "case", "throw", "yield", "else", "assert", "default", "do", "in");

  private static int unaryMinusAt(String text, int start) {
    int i = start - 1;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    if (i < 0 || text.charAt(i) != '-') {
      return -1;
    }
    int before = i - 1;
    while (before >= 0 && Character.isWhitespace(text.charAt(before))) {
      before--;
    }
    if (before < 0) {
      return i;
    }
    char c = text.charAt(before);
    if (Character.isLetter(c) || c == '_') {
      // A keyword cannot end an expression, so a minus after one is unary: `return -1;`.
      int wordStart = before;
      while (wordStart > 0 && (Character.isLetterOrDigit(text.charAt(wordStart - 1))
          || text.charAt(wordStart - 1) == '_')) {
        wordStart--;
      }
      String word = text.substring(wordStart, before + 1);
      return KEYWORDS.contains(word) ? i : -1;
    }
    return Character.isDigit(c) || c == 41 || c == 93 || c == 34 || c == 39 ? -1 : i;
  }

  /**
   * Whether the literal is an operand of a comparison, on either side of the operator.
   *
   * <p>A byte, short or char constant named in a comparison keeps the comparison's type: binary
   * numeric promotion widens it exactly as it widens the literal, so the compiled comparison is
   * identical. An argument position has no such guarantee, which is why the narrower kinds are
   * offered only here. An assignment ({@code x = 8}) is not a comparison: its right-hand side is
   * the literal, and a narrower name there would change the assigned expression's type and can
   * even close a cycle between constant initializers.
   */
  private static boolean comparisonSite(String text, int start, int end) {
    int i = start - 1;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    if (i >= 0) {
      char c = text.charAt(i);
      if (c == '<' || c == '>') {
        return true;
      }
      if (c == '=') {
        // `x == 8`, `x != 8`, `x <= 8`, `x >= 8`: the '=' ends a two-character comparison
        // operator. A lone '=' after an identifier or a value is an assignment, not a comparison.
        char before = i > 0 ? text.charAt(i - 1) : '\0';
        if (before == '=' || before == '!' || before == '<' || before == '>') {
          return true;
        }
      }
    }
    int j = end;
    while (j < text.length() && Character.isWhitespace(text.charAt(j))) {
      j++;
    }
    if (j < text.length()) {
      char d = text.charAt(j);
      if (d == '=' || d == '<' || d == '>') {
        return true;
      }
      if (d == '!' && j + 1 < text.length() && text.charAt(j + 1) == '=') {
        return true;
      }
    }
    return false;
  }

  /** The primitive type of a cast written immediately before an integer literal, or null. */
  private static VariableType primitiveCastKind(String text, int start) {
    int i = start - 1;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    if (i < 0 || text.charAt(i) != ')') {
      return null;
    }
    i--;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    int nameEnd = i + 1;
    while (i >= 0 && Character.isLetter(text.charAt(i))) {
      i--;
    }
    VariableType kind = switch (text.substring(i + 1, nameEnd)) {
      case "byte" -> VariableType.BYTE;
      case "short" -> VariableType.SHORT;
      default -> null;
    };
    if (kind == null) {
      return null;
    }
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    return i >= 0 && text.charAt(i) == '(' ? kind : null;
  }

  /** The position of the opening parenthesis of the cast {@link #primitiveCastKind} found. */
  private static int primitiveCastStart(String text, int start) {
    int i = start - 1;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    if (i < 0 || text.charAt(i) != ')') {
      return start;
    }
    i--;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    while (i >= 0 && Character.isLetter(text.charAt(i))) {
      i--;
    }
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    return i >= 0 && text.charAt(i) == '(' ? i : start;
  }

  private static int scanNumber(String text, int start, List<Site> sites,
                                Map<String, List<Constant>> candidates, List<String> imports,
                                String packageName, String own, Map<String, List<int[]>> ownInitializers,
                                Placement placement, Map<String, List<Site>> deferred,
                                Set<String> inWindow, Map<String, List<Site>> invented) {
    int i = start;
    char c = text.charAt(i);
    boolean hex = c == '0' && i + 1 < text.length()
      && (text.charAt(i + 1) == 'x' || text.charAt(i + 1) == 'X'
          || text.charAt(i + 1) == 'b' || text.charAt(i + 1) == 'B');
    if (hex) {
      i += 2;
      while (i < text.length() && (Character.digit(text.charAt(i), 16) >= 0 || text.charAt(i) == '_')) {
        i++;
      }
    } else {
      boolean dot = false;
      boolean exponent = false;
      while (i < text.length()) {
        char digit = text.charAt(i);
        if (Character.isDigit(digit) || digit == '_') {
          i++;
          continue;
        }
        if (digit == '.' && !dot && !exponent) {
          dot = true;
          i++;
          continue;
        }
        if ((digit == 'e' || digit == 'E') && !exponent) {
          exponent = true;
          i++;
          if (i < text.length() && (text.charAt(i) == '+' || text.charAt(i) == '-')) {
            i++;
          }
          continue;
        }
        break;
      }
    }
    int negativeAt = unaryMinusAt(text, start);
    boolean negative = negativeAt >= 0;
    String digits = text.substring(start, i).replace("_", "");
    char suffix = hex || i >= text.length() ? '\0' : text.charAt(i);
    String kind;
    String value;
    try {
      if (suffix == 'f' || suffix == 'F') {
        i++;
        kind = VariableType.FLOAT.name();
        float parsedFloat = Float.parseFloat(digits);
        value = Float.toString(negative ? -parsedFloat : parsedFloat);
      } else if (suffix == 'd' || suffix == 'D') {
        i++;
        kind = VariableType.DOUBLE.name();
        double parsedDouble = Double.parseDouble(digits);
        value = Double.toString(negative ? -parsedDouble : parsedDouble);
      } else if (suffix == 'l' || suffix == 'L') {
        i++;
        Long parsed = parseLong(digits);
        if (parsed == null) {
          return i;
        }
        long number = negative ? -parsed : parsed;
        kind = VariableType.LONG.name();
        value = Long.toString(number);
        // An int constant used where a long is wanted widens at compile time, so the source can
        // read `Integer.MAX_VALUE` where the pool holds a long constant. When no long constant
        // explains the literal, try the int constant of the same value -- but never where the
        // literal itself decides the expression's type: a long operation whose sibling the class
        // file widens with i2l would have been int arithmetic with an int constant there, so no
        // source that compiled this class wrote one.
        List<Constant> asLong = candidates.get(kind + "|" + value);
        if ((asLong == null || asLong.size() != 1)
            && number >= Integer.MIN_VALUE && number <= Integer.MAX_VALUE
            && !drivesLongType(placement, start, number)) {
          addSite(sites, negative ? negativeAt : start, i, VariableType.INT.name() + "|" + number, "",
            candidates, imports, packageName, own, ownInitializers, placement, deferred, inWindow, invented, false);
        }
      } else if (digits.indexOf('.') >= 0 || digits.indexOf('e') >= 0 || digits.indexOf('E') >= 0) {
        kind = VariableType.DOUBLE.name();
        double parsedDouble = Double.parseDouble(digits);
        value = Double.toString(negative ? -parsedDouble : parsedDouble);
      } else {
        Long parsed = parseLong(digits);
        if (parsed == null) {
          return i;
        }
        kind = VariableType.INT.name();
        value = Long.toString(negative ? -parsed : parsed);
      }
    } catch (NumberFormatException e) {
      return i;
    }
    int siteStart = negative ? negativeAt : start;
    // A byte or short constant can only be named where the printed source casts the literal to
    // that type: the name then replaces the whole cast and the expression keeps its type. The
    // plain integer site is not offered in that case, since an int constant would leave the cast
    // and intern a different owner.
    VariableType castKind = kind.equals(VariableType.INT.name()) ? primitiveCastKind(text, start) : null;
    if (castKind != null) {
      int before = sites.size();
      addSite(sites, primitiveCastStart(text, start), i, castKind.name() + "|" + value, "", candidates, imports,
        packageName, own, ownInitializers, placement, deferred, inWindow, invented);
      if (sites.size() > before) {
        return i;
      }
    }
    addSite(sites, siteStart, i, kind + "|" + value, "", candidates, imports, packageName, own, ownInitializers,
      placement, deferred, inWindow, invented);
    if (kind.equals(VariableType.INT.name()) && comparisonSite(text, siteStart, i)) {
      // A narrower constant keeps a comparison's type under binary numeric promotion, so the pool's
      // proof of a naming there can be honoured without the cast an argument position would need.
      addSite(sites, siteStart, i, VariableType.BYTE.name() + "|" + value, "", candidates, imports,
        packageName, own, ownInitializers, placement, deferred, inWindow, invented);
      addSite(sites, siteStart, i, VariableType.SHORT.name() + "|" + value, "", candidates, imports,
        packageName, own, ownInitializers, placement, deferred, inWindow, invented);
    }
    if (kind.equals(VariableType.FLOAT.name())) {
      addSite(sites, siteStart, i, "FLOATCAST|" + value, "", candidates, imports, packageName, own, ownInitializers,
        placement, deferred, inWindow, invented);
    }
    if (!negative && (kind.equals(VariableType.FLOAT.name()) || kind.equals(VariableType.DOUBLE.name()))) {
      addIntegralSite(start, i, value, kind.equals(VariableType.FLOAT.name()), sites, candidates, imports,
        packageName, own, ownInitializers, placement, deferred, inWindow, invented);
    }
    if (kind.equals(VariableType.DOUBLE.name())) {
      addWidenedFloatSite(siteStart, i, value, negative, sites, candidates, imports, packageName, own,
        ownInitializers, placement, deferred, inWindow, invented);
    }
    if (negative && value.startsWith("-")) {
      // The source can write a positive constant behind a unary minus; the literal is then the
      // negation of the constant, not a negative constant of its own.
      String magnitude = value.substring(1);
      addSite(sites, siteStart, i, kind + "|" + magnitude, "-", candidates, imports, packageName, own,
        ownInitializers, placement, deferred, inWindow, invented);
      if (kind.equals(VariableType.INT.name()) && comparisonSite(text, siteStart, i)) {
        addSite(sites, siteStart, i, VariableType.BYTE.name() + "|" + magnitude, "-", candidates,
          imports, packageName, own, ownInitializers, placement, deferred, inWindow, invented);
        addSite(sites, siteStart, i, VariableType.SHORT.name() + "|" + magnitude, "-", candidates,
          imports, packageName, own, ownInitializers, placement, deferred, inWindow, invented);
      }
      if (kind.equals(VariableType.FLOAT.name())) {
        addSite(sites, siteStart, i, "FLOATCAST|" + magnitude, "-", candidates, imports, packageName, own,
          ownInitializers, placement, deferred, inWindow, invented);
      }
      if (kind.equals(VariableType.LONG.name())) {
        try {
          long mag = Long.parseLong(magnitude);
          List<Constant> asLong = candidates.get(kind + "|" + magnitude);
          if ((asLong == null || asLong.size() != 1) && mag <= Integer.MAX_VALUE) {
            addSite(sites, siteStart, i, VariableType.INT.name() + "|" + mag, "-", candidates, imports,
              packageName, own, ownInitializers, placement, deferred, inWindow, invented);
          }
        } catch (NumberFormatException ignored) {
          // a magnitude too large for a positive long has no constant to name
        }
      }
    }
    return i;
  }

  private static void addSite(List<Site> sites, int start, int end, String key, String prefix,
                              Map<String, List<Constant>> candidates, List<String> imports,
                              String packageName, String own, Map<String, List<int[]>> ownInitializers,
                              Placement placement, Map<String, List<Site>> deferred,
                              Set<String> inWindow, Map<String, List<Site>> invented) {
    addSite(sites, start, end, key, prefix, candidates, imports, packageName, own, ownInitializers,
      placement, deferred, inWindow, invented, true);
  }

  /**
   * Adds one site for a literal, with or without the expression solver.
   *
   * <p>A long literal is offered to the int constants too, because an int constant used where a
   * long is wanted widens at compile time. Only a bare constant name widens, though: a solved
   * expression over int constants is int-typed and would change the surrounding arithmetic, so
   * that fallback takes candidates only.
   */
  private static void addSite(List<Site> sites, int start, int end, String key, String prefix,
                              Map<String, List<Constant>> candidates, List<String> imports,
                              String packageName, String own, Map<String, List<int[]>> ownInitializers,
                              Placement placement, Map<String, List<Site>> deferred,
                              Set<String> inWindow, Map<String, List<Site>> invented,
                              boolean allowSolved) {
    List<Constant> constants = candidates.get(key);
    // A pool pair records an owner named immediately before a reference the generation placed at
    // one instruction. That is the strongest evidence a site can have, and it also settles a
    // literal another owner's constant could explain: the pair says which owner was named here.
    // The class's own constant keeps its long-standing precedence: its Class entry is in the pool
    // regardless, so no pair can say more about it than the own-constant rule already does.
    Constant firstOwn = null;
    boolean ownShared = false;
    List<Constant> ownValue = new ArrayList<>();
    if (constants != null) {
      for (Constant constant : constants) {
        if (constant.owner().equals(own)) {
          ownValue.add(constant);
          if (firstOwn != null) {
            ownShared = true; // two own constants share the value; only a proof may choose
          }
          else {
            firstOwn = constant;
          }
        }
      }
    }
    Constant ownConstant = ownShared ? null : firstOwn;
    if (ownValue.isEmpty() && key.startsWith(VariableType.INT.name() + "|")) {
      // A byte, short or char constant selected where the source prints an int literal folds to
      // that int, so it is the class's own constant for this value too. The int constants stay
      // first: a narrower one could change an overload choice the int literal did not make.
      int bar = key.indexOf('|');
      for (VariableType kind : List.of(VariableType.BYTE, VariableType.SHORT, VariableType.CHAR)) {
        List<Constant> narrower = candidates.get(kind.name() + key.substring(bar));
        if (narrower == null) {
          continue;
        }
        for (Constant constant : narrower) {
          if (constant.owner().equals(own)) {
            ownValue.add(constant);
          }
        }
      }
    }
    Constant excluded = null;
    if (ownConstant != null && insideInitializer(ownInitializers, start)) {
      for (int[] range : ownInitializers.getOrDefault(ownConstant.name(), List.of())) {
        if (start >= range[0] && start < range[1]) {
          // The field's own initializer cannot name it. It stays out of the selection entirely,
          // so another owner's constant of the same value is no longer ambiguous with it.
          excluded = ownConstant;
          ownConstant = null;
          break;
        }
      }
    }
    boolean ownCandidate = ownConstant != null;
    // [0] a value successor is the exact folded value, [1] the solution is the constant's own
    // name (not an expression the solver built from one of its constants).
    boolean[] exactProof = new boolean[2];
    Site solved = allowSolved && placement != null && placement.pairs() != null
      && !placement.pairs().isEmpty() && prefix.isEmpty()
      ? solvedSite(key, start, end, own, imports, packageName, placement, exactProof) : null;
    // The class's own constant keeps precedence over a naming placed by the generation gap: its
    // Class entry is in the pool regardless, so the gap proves less about it. A value successor
    // is the exact folded value, though, and settles which owner the source named. The same holds
    // where the own name is unusable at this site anyway (a frequent value with no pool evidence
    // for the own entry's position): the foreign pair is the only evidence left, so it decides.
    boolean ownUnusable = ownCandidate && tooCommon(key) && placement != null
      && !placement.ownEarly() && !placement.ownProven();
    if (solved != null && (exactProof[0] || exactProof[1] || !ownCandidate
        || ownUnusable)) {
      // A reference successor's pair records only that some naming entered the owner before the
      // reference: an invented expression is admitted at any literal of the pair's generation gap,
      // so that literal alone does not prove it is where the pool's one naming stood. A direct
      // naming found at a later generation point does: it is the constant's own value written as
      // the literal, and the pair's naming is the last pool-entering event before the reference,
      // so the earlier guess is withdrawn.
      if (exactProof[0] || exactProof[1]) {
        List<Site> guessed = invented == null ? null : invented.remove(solved.owner());
        if (guessed != null) {
          for (Site site : guessed) {
            if (before(site, solved, placement)) {
              sites.remove(site);
            }
          }
        }
      }
      else if (invented != null) {
        invented.computeIfAbsent(solved.owner(), k -> new ArrayList<>()).add(solved);
      }
      addSiteOnce(sites, solved);
      return;
    }
    if (constants == null || constants.isEmpty()) {
      if (ownValue.isEmpty()) {
        return; // no candidate at all; a narrower own constant alone needs the proof below
      }
      constants = List.of();
    }
    // A quoted literal is printed by enclosing a buffer whose mapping sits at its content start,
    // so the recorded position of the instruction is one past the opening quote.
    int anchor = key.startsWith(VariableType.STRING.name() + "|")
      || key.startsWith(VariableType.CHAR.name() + "|") ? start + 1 : start;
    List<Constant> usable = constants;
    if (excluded != null) {
      usable = new ArrayList<>(constants);
      usable.remove(excluded);
    }
    Constant provenOwn = ownProvenConstant(ownValue, key, own, anchor, placement);
    // A pair whose generation gap admits this site is the pool's record that its owner was named
    // here. That record is stronger than a same-valued own constant, which interns no new entry:
    // keeping the own name would leave the pair owner's Class entry missing from the pool.
    Constant paired = pairOwner(usable, anchor, placement);
    Constant constant = paired != null && provenOwn == null ? paired
      : ownCandidate ? ownConstant
      : paired != null ? paired
      : usable.size() == 1 ? usable.get(0) : selectProvable(usable, anchor, placement, own);
    if (constant == null) {
      // Nothing the existing rules place explains this literal; the own Class entry still says
      // the original named one of its constants at this point, and the pool admitted the site.
      constant = provenOwn;
    }
    if (constant == null) {
      return;
    }
    if (ambiguousInitializer(constant, key, own, start, ownInitializers)) {
      // Equal folded values make two of the class's own constants interchangeable to the pool, and
      // inside a constant initializer the pool places no site to choose between them.
      return;
    }
    boolean provenSite = constant == provenOwn;
    boolean foreign = !constant.owner().equals(own);
    boolean lexical = foreign && placement != null && placement.lexical() != null
      && placement.lexical().contains(constant.owner());
    if (foreign && !lexical && placement != null && placement.prefix() != null
        && !placement.prefix().contains(constant.owner())
        && insideInitializer(ownInitializers, anchor)) {
      // A naming in a constant field initializer is resolved before any code is generated, so the
      // owner's Class entry and its name would open the pool, right after the earlier namings. A
      // pool without that pair means the source did not name a constant here; the window only
      // found a literal on a line the owner happens to touch.
      return;
    }
    if (lexical) {
      // Names are resolved in source order, so a simple name printed earlier in this class would
      // enter its Class entry first. Only another name resolved while the class's names were
      // resolved competes for the pool's opening slot: a naming the code generation enters later
      // cannot move the prefix pair.
      for (Site earlier : sites) {
        if (earlier.start() < start && inside(placement.spans(), earlier.start())
            && placement.lexical() != null && placement.lexical().contains(earlier.owner())) {
          return;
        }
      }
    }
    int[] window = placement == null || placement.windows() == null || !foreign
      ? null : placement.windows().get(constant.owner());
    // The pool order in generation order is exact: the site must fall after every lower entry's
    // first use and before every higher entry's first use. A text window only approximates it; the
    // coordinate check places the site by the positions the printer recorded for its method, which
    // also covers a static field initializer generated in <clinit> but printed at its declaration.
    boolean placed = foreign && placement != null && placement.proves(constant.owner(), anchor);
    // The pool enters the owner's Class at its first field or method reference and at its first
    // constant naming; a site printed before those points would move the entry earlier.
    if (foreign && placement != null && !placement.existsAt(constant.owner(), anchor)) {
      return;
    }
    if (foreign && placement != null && placement.inherited() != null
        && placement.inherited().contains(constant.owner() + "|" + constant.name())) {
      // An inherited constant has no pool entry of its own: the value alone can sit on a line the
      // owner happens to touch. Only the generation order's exact point proves the naming.
      if (!placement.provesExactly(constant.owner(), anchor)) {
        return;
      }
      placed = true;
    }
    // A frequent value is only weak evidence where there is no better one. A window means the pool
    // proves this owner was named somewhere, and the value only has to pick among its constants;
    // the site itself is still placed by the window or its fallback below.
    boolean recorded = placement != null
      && ((placement.pairs() != null && placement.pairs().containsKey(constant.owner()))
          || (placement.values() != null && placement.values().containsKey(constant.owner())));
    if (window == null && !placed && !recorded && !provenSite && !ownCandidate
        && tooCommon(key)) {
      // The class's own constant is unambiguous here: the value is common, but the name can only
      // be this class's own field, and naming it is the only way its Class entry moves forward.
      return;
    }
    if (window == null && !placed && !recorded && !provenSite && ownCandidate && tooCommon(key)
        && !placement.ownEarly()) {
      // The own name is only worth printing where the pool shows the class's own Class entry was
      // entered early; otherwise the literal is what the original wrote.
      return;
    }
    if (constant.owner().equals(own)) {
      for (int[] range : ownInitializers.getOrDefault(constant.name(), List.of())) {
        if (start >= range[0] && start < range[1]) {
          return; // a constant cannot be named inside its own initializer
        }
      }
      if (!provenSite && placement != null && placement.cls() != null && !placement.ownEarly()) {
        // Naming an own constant interns the class's own Class entry at the naming site. The
        // original's entry sits where the pool has it: if that is a generated point, a site
        // before it would move the entry; if it is only this_class, no naming existed at all.
        // A naming in a constant field initializer is generated before every body, so only a
        // pool whose own pair opens the prefix can have come from one.
        if (insideInitializer(ownInitializers, anchor)) {
          return;
        }
        if (!placement.existsAt(own, anchor)) {
          return;
        }
      }
    }
    String name = simpleName(constant.owner());
    String printed;
    if (placement != null && placement.lexical() != null
        && placement.lexical().contains(constant.owner())) {
      // The pool proves the enclosing class was named in a field initializer, and javac enters
      // the enclosing Class only for the simple name there. The name must resolve to that owner
      // and not to a field declared closer to the site.
      StructClass site = DecompilerContext.getStructContext().getClass(own);
      if (site == null || !resolvesTo(site, constant.owner(), constant.name())) {
        return;
      }
      printed = prefix + constant.name();
      if (key.startsWith("FLOATCAST|")) {
        printed = "(float) " + printed;
      }
    }
    else if (placement != null && placement.windows() != null && constant.owner().equals(own)
        && anonymous(constant.owner())) {
      // Inside its own class the constant needs no qualifier, and an anonymous class has no
      // writable simple name at all (its binary suffix is a number).
      printed = prefix + constant.name();
      if (key.startsWith("FLOATCAST|")) {
        printed = "(float) " + printed;
      }
    }
    else {
      boolean nested = constant.owner().contains("$");
      // A nested class's simple name is in scope only inside its own nest or through an explicit
      // import; elsewhere it needs its outer class, which a same-package check alone would miss.
      boolean inScope = nestOf(constant.owner()).equals(nestOf(own))
        || imports.contains(constant.owner().replace('/', '.'))
        || (!nested && packageName.equals(packageOf(constant.owner())));
      String qualifier;
      if (inScope) {
        qualifier = name;
      }
      else if (nested) {
        if (anonymous(constant.owner()) || !publiclyNameable(constant.owner(), packageName)) {
          return;
        }
        qualifier = constant.owner().replace('/', '.').replace('$', '.');
      }
      else {
        qualifier = constant.owner().replace('/', '.');
      }
      printed = prefix + qualifier + "." + constant.name();
      if (key.startsWith("FLOATCAST|")) {
        printed = "(float) " + printed;
      }
    }
    if (provenSite && !key.startsWith(constant.kind().name() + "|")) {
      // The literal is an int and the name is a byte, short or char constant. The cast keeps the
      // expression's type int, so an overload choice the literal made cannot change; a cast of a
      // constant variable is still a constant expression and folds to the same value.
      printed = "(int) " + printed;
    }
    // A pair owner's site is the argument generation of the reference the pair precedes. The
    // literal must not carry a pool value of its own unless one already sits below the pair, and
    // the latest matching literal before the reference is the one whose naming keeps the pool
    // order (nothing is entered between it and the reference).
    ValueSite valueSite = placement == null || placement.values() == null
      ? null : placement.values().get(constant.owner());
    if (!lexical && valueSite != null && window == null && !placed) {
      // The value the pool entered at the naming is this literal's: only a literal that folds to
      // it (and hence names a constant of that value) reproduces the entry.
      if (valueSite.accepts(key) && deferred != null) {
        deferred.computeIfAbsent(constant.owner(), k -> new ArrayList<>())
          .add(new Site(start, end, printed, constant.owner()));
      }
      return;
    }
    PairSite pair = placement == null || placement.pairs() == null
      ? null : placement.pairs().get(constant.owner());
    if (!lexical && pair != null && window == null && !placed) {
      if (pair.valueAvailable(key) && deferred != null) {
        deferred.computeIfAbsent(constant.owner(), k -> new ArrayList<>())
          .add(new Site(start, end, printed, constant.owner()));
      }
      return;
    }
    // A foreign owner's naming site is bounded by where the original interned the owner's Class
    // entry. The class's own constants are exempt: its Class entry is in the pool regardless, so
    // the pool order says nothing about when the source named one of them.
    if (window != null) {
      if (!placed) {
        if (deferred != null) {
          deferred.computeIfAbsent(constant.owner(), k -> new ArrayList<>())
            .add(new Site(start, end, printed, constant.owner()));
        }
        return;
      }
      if (inWindow != null) {
        inWindow.add(constant.owner());
      }
    }
    addSiteOnce(sites, new Site(start, end, printed, constant.owner()));
  }

  /**
   * Names an integral int or long constant at a float or double literal whose value is exactly
   * that integer.
   *
   * <p>javac widens an integral constant to float or double at the constant expression, so a source
   * that wrote {@code Owner.NAME} prints as a float or double literal here. The rewrite is only
   * evidence-backed when the owner's Class entry is otherwise unexplained (it is in the pool only
   * because the source named the constant), the pool order places this very site where that owner
   * was named, the value is not a common one, and it selects exactly one of its constants. An int
   * constant is tried first, as the literal scanned; a long constant is used only when no int
   * constant has the value.
   */
  private static void addIntegralSite(int start, int end, String printed, boolean single,
                                      List<Site> sites, Map<String, List<Constant>> candidates,
                                      List<String> imports, String packageName, String own,
                                      Map<String, List<int[]>> ownInitializers, Placement placement,
                                      Map<String, List<Site>> deferred, Set<String> inWindow,
                                      Map<String, List<Site>> invented) {
    if (placement == null || placement.windows() == null) {
      return;
    }
    String key;
    List<Constant> constants;
    Integer asInt = integralInt(printed, single);
    if (asInt != null) {
      key = VariableType.INT.name() + "|" + asInt;
      constants = candidates.get(key);
      if (constants == null) {
        Long asLong = integralLong(printed, single);
        if (asLong == null) {
          return;
        }
        key = VariableType.LONG.name() + "|" + asLong;
        constants = candidates.get(key);
      }
    }
    else {
      Long asLong = integralLong(printed, single);
      if (asLong == null) {
        return;
      }
      key = VariableType.LONG.name() + "|" + asLong;
      constants = candidates.get(key);
    }
    if (constants == null || constants.isEmpty()) {
      return;
    }
    Constant chosen = selectProvable(constants, start, placement, own);
    if (chosen == null) {
      return;
    }
    String owner = chosen.owner();
    // An owner whose Class entry the class file already explains is no evidence that a constant
    // was named; a referenced owner's window marks its field or method use, not a constant site.
    // The site itself must lie in the proven placement: unlike a literal of the constant's own
    // kind, an int named where a float was printed cannot fall back to a loose window, because a
    // wrong site here both mistypes the expression and moves the owner's Class entry.
    // A small value is coincidence evidence even inside a window.
    if (owner.equals(own) || placement.strict().contains(owner)
        || !placement.windows().containsKey(owner) || !placement.provesExactly(owner, start)
        || tooCommon(key)) {
      return;
    }
    // The constant javac interned beside the owner's Class entry is the pool's own record of the
    // value the source named there; a literal of another value did not come from this constant.
    // The constant javac interned beside the owner's Class entry is the pool's own record of the
    // value the source named there; a literal of another value did not come from this constant.
    // A bare pair holds no such value (the constant folded to an immediate), so the literal's own
    // value, which the name must reproduce, is the only evidence and the pair's position places it.
    Double folded = placement.folded().get(owner);
    double literal = single ? (double) Float.parseFloat(printed) : Double.parseDouble(printed);
    if (folded != null) {
      if (Double.compare(folded, literal) != 0) {
        return;
      }
    }
    else if (!placement.bares().contains(owner)) {
      return;
    }
    // The literal was a float or double, and an integral constant is not: a bare name would turn
    // `intExpr / NAME` into an integer division. The cast keeps the literal's type, and a cast of a
    // constant variable is itself a constant expression, so the compiled value is unchanged.
    addSite(sites, start, end, key, single ? "(float) " : "(double) ", candidates, imports,
      packageName, own, ownInitializers, placement, deferred, inWindow, invented);
  }

  /**
   * Names a float constant at a double literal whose value is exactly that float widened.
   *
   * <p>javac widens a float constant used in a double context at the constant expression, so a
   * source that wrote {@code Owner.NAME} prints as a double literal here while the pool holds the
   * widened value beside the owner's Class entry. The evidence gates are the integral site's: the
   * owner's Class entry must be otherwise unexplained, the pool order must place this very site,
   * and the value interned beside the entry must be this literal. The rewrite casts to double so
   * the expression keeps the literal's type; a cast of a constant variable folds away.
   */
  private static void addWidenedFloatSite(int start, int end, String printed, boolean negative,
                                          List<Site> sites, Map<String, List<Constant>> candidates,
                                          List<String> imports, String packageName, String own,
                                          Map<String, List<int[]>> ownInitializers, Placement placement,
                                          Map<String, List<Site>> deferred, Set<String> inWindow,
                                          Map<String, List<Site>> invented) {
    if (placement == null || placement.windows() == null) {
      return;
    }
    double magnitude;
    try {
      magnitude = Double.parseDouble(negative && printed.startsWith("-") ? printed.substring(1) : printed);
    }
    catch (NumberFormatException e) {
      return;
    }
    float narrowed = (float) magnitude;
    if ((double) narrowed != magnitude || magnitude == 0.0) {
      return; // not a value a float constant widens to
    }
    String key = VariableType.FLOAT.name() + "|" + Float.toString(narrowed);
    List<Constant> constants = candidates.get(key);
    if (constants == null || constants.isEmpty()) {
      return;
    }
    Constant chosen = selectProvable(constants, start, placement, own);
    if (chosen == null) {
      return;
    }
    String owner = chosen.owner();
    if (owner.equals(own) || placement.strict().contains(owner)
        || !placement.windows().containsKey(owner) || !placement.provesExactly(owner, start)) {
      return;
    }
    // A bare pair holds no folded value (the constant folded to an immediate, e.g. a value the
    // bytecode pushes directly); the literal's own value, which the name must reproduce, is then
    // the only evidence, and the pair's position still places the site.
    Double folded = placement.folded().get(owner);
    double literal = negative ? -magnitude : magnitude;
    if (folded != null) {
      if (Double.compare(folded, literal) != 0) {
        return;
      }
    }
    else if (!placement.bares().contains(owner)) {
      return;
    }
    addSite(sites, start, end, key, negative ? "-(double) " : "(double) ", candidates, imports,
      packageName, own, ownInitializers, placement, deferred, inWindow, invented);
  }

  /**
   * The int a float or double literal equals exactly, or null when its value is not an exact,
   * non-negative int. A value the literal cannot reproduce would name a different constant.
   */
  private static Integer integralInt(String printed, boolean single) {
    try {
      double value = single ? Float.parseFloat(printed) : Double.parseDouble(printed);
      if (value < 0 || value > Integer.MAX_VALUE || value != Math.rint(value)) {
        return null;
      }
      int integral = (int) value;
      return (single ? (float) integral == value : (double) integral == value) ? integral : null;
    } catch (NumberFormatException e) {
      return null;
    }
  }

  /** The long a float or double literal equals exactly, or null when its value is not one. */
  private static Long integralLong(String printed, boolean single) {
    try {
      double value = single ? Float.parseFloat(printed) : Double.parseDouble(printed);
      if (value < 0 || value >= 9.223372036854775808E18 || value != Math.rint(value)) {
        return null;
      }
      long integral = (long) value;
      return (double) integral == value ? integral : null;
    } catch (NumberFormatException e) {
      return null;
    }
  }

  /**
   * The class's own constant whose folded value this literal is, when the pool places the naming.
   *
   * <p>Naming any own constant of the value interns the same {@code Class} entry and folds to the
   * same literal, so several constants of one value are interchangeable and the first declaration
   * is the deterministic pick; one whose declared kind is the literal's is preferred, since a
   * narrower name could change an overload choice. The site itself is not interchangeable: an own
   * constant named anywhere else enters the Class entry at that other point, so only the pool's
   * generation-order bracket admits it.
   */
  private static Constant ownProvenConstant(List<Constant> ownValue, String key, String own,
                                            int anchor, Placement placement) {
    if (ownValue.isEmpty() || placement == null || !placement.ownProven()) {
      return null;
    }
    if (!placement.provesExactly(own, anchor)) {
      return null;
    }
    // A local class's binary suffix carries its number ("Outer$1Name"), so the simple name the
    // printed form would qualify with is not an identifier; an anonymous class prints unqualified.
    String simple = simpleName(own);
    if (!anonymous(own) && (simple.isEmpty() || !Character.isJavaIdentifierStart(simple.charAt(0)))) {
      return null;
    }
    for (Constant constant : ownValue) {
      if (key.startsWith(constant.kind().name() + "|")) {
        return constant;
      }
    }
    return ownValue.get(0);
  }

  /**
   * The one candidate the pool order proves for this site when several constants share the value.
   *
   * <p>A value alone cannot choose between owners, and naming the wrong one adds its class to the
   * pool at a position the original never had. A window or an exact generation-order placement is
   * evidence that the owner was named here; two such owners at one site is still a guess.
   */
  private static Constant selectProvable(List<Constant> constants, int position, Placement placement,
                                         String own) {
    if (placement == null) {
      return null;
    }
    // A pair owner's Class entry was entered inside this very argument list, so where its pair
    // covers the site the value belongs to it: another owner sharing the value only touches the
    // line through an unrelated first use.
    if (placement.pairs() != null && !placement.pairs().isEmpty()) {
      for (Constant constant : constants) {
        PairSite pair = placement.pairs().get(constant.owner());
        if (pair != null && position > pair.open() && position < pair.close()) {
          return constant;
        }
      }
    }
    // The pool proves which owner was named, not which of its constants: two constants of one
    // owner with the same value fold to the same pool entry, so either name compiles to the same
    // bytes. Keep one per owner (its first declaration) and let the owners decide. When the owner
    // has several constants of the value, only an exact generation-order placement may choose:
    // the printed-line window admits any literal on the line, frequent values included.
    List<Constant> distinct = new ArrayList<>();
    Set<String> owners = new LinkedHashSet<>();
    Set<String> duplicated = new HashSet<>();
    for (Constant constant : constants) {
      if (!owners.add(constant.owner())) {
        duplicated.add(constant.owner());
      }
      else {
        distinct.add(constant);
      }
    }
    // A referenced owner's Class entry came from the field or method reference that also makes it
    // a candidate; naming one of its constants adds nothing to the pool. A pool-unexplained
    // owner's entry exists only because the source named a constant of it, so when the value alone
    // cannot choose, that owner is the one the pool is asking this site to name.
    List<Constant> necessary = new ArrayList<>();
    for (Constant constant : distinct) {
      if (!constant.owner().equals(own) && !placement.strict().contains(constant.owner())) {
        necessary.add(constant);
      }
    }
    if (necessary.size() == 1 && proven(necessary.get(0), position, placement, duplicated)) {
      return necessary.get(0);
    }
    Constant chosen = null;
    for (Constant constant : distinct) {
      if (!constant.owner().equals(own) && proven(constant, position, placement, duplicated)) {
        if (chosen != null) {
          return null;
        }
        chosen = constant;
      }
    }
    return chosen;
  }

  /** Whether the placement proves this constant's owner at the site, exactly when it must. */
  private static boolean proven(Constant constant, int position, Placement placement,
                                Set<String> duplicated) {
    return duplicated.contains(constant.owner())
      ? placement.provesExactly(constant.owner(), position)
      : placement.proves(constant.owner(), position);
  }

  /**
   * Prints the dead reference a class's own pool proves the original source contained.
   *
   * <p>A {@code Class} entry at the very start of the pool is entered while the class body is
   * resolved, before any code is generated: only a reference to one of that class's compile-time
   * constants, folded away in a constant condition, does that. The decompiler cannot recover the
   * statement that held it, but an initializer block whose condition folds to false leaves the
   * same entry and no instruction. A synthetic switch-map holder numbered above one additionally
   * records anonymous classes that consumed numbers without producing a class file, so the same
   * dead block carries that many unused anonymous declarations.
   */
  private static void deadNamings(String text, List<int[]> spans, Rules rules, StructClass own,
                                  String packageName, List<Site> sites, int anonymous) {
    if (own == null || spans.isEmpty()) {
      return;
    }
    if (own.getRecordComponents() != null
        || (own.getAccessFlags() & (CodeConstants.ACC_INTERFACE | CodeConstants.ACC_ANNOTATION
        | CodeConstants.ACC_ENUM)) != 0) {
      return; // this body has no instance initializer block
    }
    List<Map.Entry<Integer, String>> conditions = new ArrayList<>();
    // A name whose Class entry opens the pool was written while the class body was attributed,
    // before any generated code: either in a constant field initializer or in a constant condition
    // that folded away. A site already reproduces the initializer form; without one, the dead
    // condition is what is left. This holds whether or not the class text mentions the owner
    // elsewhere, so the missing-name rule is not the trigger.
    Map<String, Integer> indices = classIndices(own);
    Set<Integer> prefix = prefixClassIndices(own);
    Set<Integer> added = new HashSet<>();
    Map<String, List<int[]>> constantInitializers = ownInitializers(text, own);
    if (rules != null) {
      for (String owner : rules.missing()) {
        addDeadCondition(indices, prefix, owner, own, packageName, sites, constantInitializers,
          rules.placement(), conditions, added);
      }
    }
    Placement placement = rules == null ? null : rules.placement();
    for (String owner : prefixOwners(own)) {
      addDeadCondition(indices, prefix, owner, own, packageName, sites, constantInitializers,
        placement, conditions, added);
    }
    conditions.sort(Map.Entry.comparingByKey());
    if (conditions.isEmpty() && anonymous <= 0) {
      return;
    }
    int at = classBodyOpen(text, spans.get(0), own);
    if (at < 0) {
      return;
    }
    StringBuilder block = new StringBuilder(" {");
    for (int i = 0; i < conditions.size(); i++) {
      block.append(" if (").append(conditions.get(i).getValue()).append(") {");
      if (i == 0) {
        appendAnonymous(block, anonymous);
      }
      block.append(" }");
    }
    if (conditions.isEmpty()) {
      block.append(" if (false) {");
      appendAnonymous(block, anonymous);
      block.append(" }");
    }
    block.append(" }");
    addSiteOnce(sites, new Site(at, at, block.toString(), "@dead"));
  }

  /**
   * Adds the dead condition for one prefix-pair owner, when the pool and the text make it the
   * only possible source of that pair.
   */
  private static void addDeadCondition(Map<String, Integer> indices, Set<Integer> prefix,
                                       String owner, StructClass own, String packageName,
                                       List<Site> sites, Map<String, List<int[]>> constantInitializers,
                                       Placement placement,
                                       List<Map.Entry<Integer, String>> conditions,
                                       Set<Integer> added) {
    if (own.superClass != null && owner.equals(own.superClass.getString())) {
      return; // the superclass's entry is class setup, not a naming; a dead name would move it
    }
    Integer index = indices.get(owner);
    // Only a naming attributed with a constant field initializer enters the pair before any code
    // was generated; a method-body site or a non-constant initializer is compiled into <clinit>
    // or a constructor and reuses the pair there, not at the pool's front.
    boolean explained = siteInConstantInitializer(sites, owner, constantInitializers);
    // A site the pair's own generation bracket proves is compiled where the pool wants the pair;
    // a dead condition folds earlier and would move it ahead of that code's entries.
    PairSite pair = placement == null || placement.pairs() == null
      ? null : placement.pairs().get(owner);
    if (pair != null && !explained) {
      for (Site site : sites) {
        if (owner.equals(site.owner()) && pairProvesBounds(pair, site.start(), placement)) {
          explained = true;
          break;
        }
      }
    }
    if (index == null || !prefix.contains(index) || !added.add(index) || explained) {
      return;
    }
    String condition = deadCondition(owner, own.qualifiedName, packageName);
    if (condition != null) {
      conditions.add(Map.entry(index, condition));
    }
  }

  /** Whether a site of this owner lies inside one of the class's constant field initializers. */
  private static boolean siteInConstantInitializer(List<Site> sites, String owner,
                                                   Map<String, List<int[]>> initializers) {
    for (Site site : sites) {
      if (!owner.equals(site.owner())) {
        continue;
      }
      for (List<int[]> ranges : initializers.values()) {
        for (int[] range : ranges) {
          if (site.start() >= range[0] && site.start() < range[1]) {
            return true;
          }
        }
      }
    }
    return false;
  }

  private static void appendAnonymous(StringBuilder block, int count) {
    for (int i = 0; i < count; i++) {
      block.append(" java.lang.Runnable drop").append(i)
        .append(" = new java.lang.Runnable() { public void run() { } };");
    }
  }

  /** A condition over one of the owner's constants that is false where javac folds it. */
  private static String deadCondition(String owner, String ownName, String packageName) {
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return null;
    }
    String qualifier = solverQualifier(owner, packageName);
    if (qualifier == null) {
      return null;
    }
    for (StructField field : cls.getFields()) {
      int access = field.getAccessFlags();
      if ((access & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      boolean accessible = (access & CodeConstants.ACC_PUBLIC) != 0
        || ((access & CodeConstants.ACC_PRIVATE) == 0 && packageName.equals(packageOf(owner)))
        || ((access & CodeConstants.ACC_PRIVATE) != 0 && nestOf(owner).equals(nestOf(ownName)));
      if (!accessible) {
        continue;
      }
      StructConstantValueAttribute attribute =
        field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
      if (attribute == null) {
        continue;
      }
      PrimitiveConstant value = cls.getPool().getPrimitiveConstant(attribute.getIndex());
      if (value == null || !(value.value instanceof Number number)) {
        continue;
      }
      VariableType kind = kind(field.getDescriptor());
      if (kind == null) {
        continue;
      }
      // An own constant is written bare: javac resolves an unqualified constant in a constant
      // context through the class's own entry, which is what the pool's front pair records. A
      // qualified own name in a folded condition is not interned at all.
      String name = owner.equals(ownName) ? field.getName() : qualifier + "." + field.getName();
      switch (kind) {
        case BOOLEAN:
          return number.intValue() != 0 ? "!" + name : name;
        case INT:
        case BYTE:
        case SHORT:
        case CHAR: {
          long integral = number.longValue();
          return name + " == " + (integral == Integer.MAX_VALUE ? integral - 1 : integral + 1);
        }
        case LONG: {
          long integral = number.longValue();
          return name + " == " + (integral == Long.MAX_VALUE ? integral - 1 : integral + 1) + "L";
        }
        default:
          break;
      }
    }
    return null;
  }

  /** The pool indices of the leading {@code Class, Utf8} pairs, entered before any code. */
  private static Set<Integer> prefixClassIndices(StructClass cls) {
    List<PooledConstant> pool = cls.getPool().getPool();
    Set<Integer> prefix = new HashSet<>();
    int index = 1;
    while (index + 1 < pool.size()
        && pool.get(index) instanceof PrimitiveConstant entry && entry.type == CodeConstants.CONSTANT_Class
        && pool.get(index + 1) instanceof PrimitiveConstant name && name.type == CodeConstants.CONSTANT_Utf8) {
      prefix.add(index);
      index += 2;
    }
    return prefix;
  }

  private static boolean siteWithin(List<Site> sites, String owner, List<int[]> spans) {
    for (Site site : sites) {
      if (!site.owner().equals(owner)) {
        continue;
      }
      for (int[] span : spans) {
        if (site.start() >= span[0] && site.start() < span[1]) {
          return true;
        }
      }
    }
    return false;
  }

  private static int classBodyOpen(String text, int[] span, StructClass own) {
    String qualified = own.qualifiedName;
    String simple = qualified.substring(qualified.lastIndexOf('/') + 1);
    int dollar = simple.lastIndexOf('$');
    if (dollar >= 0) {
      simple = simple.substring(dollar + 1);
    }
    if (simple.isEmpty() || !Character.isJavaIdentifierStart(simple.charAt(0))) {
      return -1; // an anonymous or local class has no declaration to add a block to
    }
    java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
      "\\b(?:class|interface|enum|record)\\s+" + java.util.regex.Pattern.quote(simple) + "\\b");
    java.util.regex.Matcher matcher = pattern.matcher(text);
    matcher.region(span[0], span[1]);
    if (!matcher.find()) {
      return -1;
    }
    int brace = text.indexOf('{', matcher.end());
    return brace >= 0 && brace < span[1] ? brace + 1 : -1;
  }

  /**
   * How many anonymous classes the original source had that produced no class file.
   *
   * <p>javac numbers a synthetic switch-map holder after every anonymous class entered before it,
   * including classes in compile-time-dead code that are never emitted. When the holder is the
   * only numbered class this class has and its number is above one, the missing numbers were such
   * dead classes.
   */
  private static int anonymousPadding(StructClass own) {
    if (own == null) {
      return 0;
    }
    StructInnerClassesAttribute inner = own.getAttribute(StructGeneralAttribute.ATTRIBUTE_INNER_CLASSES);
    if (inner == null || inner.getEntries() == null) {
      return 0;
    }
    String prefix = own.qualifiedName + "$";
    int holder = -1;
    for (StructInnerClassesAttribute.Entry entry : inner.getEntries()) {
      if (entry.innerName == null || !entry.innerName.startsWith(prefix)) {
        continue;
      }
      String tail = entry.innerName.substring(prefix.length());
      int digits = 0;
      while (digits < tail.length() && Character.isDigit(tail.charAt(digits))) {
        digits++;
      }
      if (digits == 0) {
        continue;
      }
      if (digits < tail.length() || holder >= 0 || !switchMapHolder(entry.innerName)) {
        return 0; // a local class, a second anonymous class, or an ordinary one
      }
      holder = Integer.parseInt(tail);
    }
    return holder >= 2 ? holder - 1 : 0;
  }

  private static boolean switchMapHolder(String name) {
    StructClass holder = DecompilerContext.getStructContext().getClass(name);
    if (holder == null || (holder.getAccessFlags() & CodeConstants.ACC_SYNTHETIC) == 0) {
      return false;
    }
    boolean map = false;
    for (StructField field : holder.getFields()) {
      if (field.getName().startsWith("$SwitchMap$")) {
        map = true;
      }
    }
    for (StructMethod method : holder.getMethods()) {
      if (!"<clinit>".equals(method.getName())) {
        return false;
      }
    }
    return map;
  }

  /**
   * Adds a rewrite unless the same span already has one.
   *
   * <p>A second replacement at one span would run against text the first already changed, and its
   * end offset, computed on the original text, would then cut into unrelated source.
   */
  private static void addSiteOnce(List<Site> sites, Site site) {
    for (int i = sites.size() - 1; i >= 0; i--) {
      Site existing = sites.get(i);
      if (existing.start() == site.start() && existing.end() == site.end()) {
        return;
      }
      if (site.start() < existing.end() && existing.start() < site.end()) {
        // Two replacements over one span cannot both run: the second would rewrite text the
        // first already changed, with offsets computed on the original. The first site placed
        // is the one the earlier evidence chose.
        return;
      }
    }
    sites.add(site);
  }

  /**
   * Small, frequent values have a constant declaration in almost every library; a rewrite at such
   * a site is a coincidence, not evidence, and cannot be checked without compiling.
   */
  private static boolean tooCommon(String key) {
    if (key.startsWith(VariableType.BOOLEAN + "|")) {
      return true;
    }
    if (key.startsWith(VariableType.INT + "|") || key.startsWith(VariableType.LONG + "|")) {
      try {
        long value = Long.parseLong(key.substring(key.indexOf('|') + 1));
        return value >= -3 && value <= 3;
      } catch (NumberFormatException e) {
        return true;
      }
    }
    if (key.startsWith(VariableType.CHAR + "|")) {
      try {
        int value = Integer.parseInt(key.substring(key.indexOf('|') + 1));
        return value < 32 || Character.isLetterOrDigit(value);
      } catch (NumberFormatException e) {
        return true;
      }
    }
    if (key.startsWith(VariableType.STRING + "|")) {
      return key.length() < VariableType.STRING.name().length() + 4;
    }
    return false;
  }

  private static int skipQuoted(String text, int start, char quote) {
    int i = start + 1;
    while (i < text.length()) {
      char c = text.charAt(i);
      if (c == '\\') {
        i += 2;
        continue;
      }
      if (c == quote) {
        return i + 1;
      }
      if (c == '\n') {
        return i;
      }
      i++;
    }
    return text.length();
  }

  private static String unescape(String body) {
    StringBuilder builder = new StringBuilder(body.length());
    for (int i = 0; i < body.length(); i++) {
      char c = body.charAt(i);
      if (c != '\\') {
        builder.append(c);
        continue;
      }
      if (i + 1 >= body.length()) {
        return null;
      }
      char escaped = body.charAt(++i);
      switch (escaped) {
        case 'n' -> builder.append('\n');
        case 't' -> builder.append('\t');
        case 'r' -> builder.append('\r');
        case 'b' -> builder.append('\b');
        case 'f' -> builder.append('\f');
        case '\'' -> builder.append('\'');
        case '\\' -> builder.append('\\');
        case '"' -> builder.append('"');
        case 'u' -> {
          if (i + 4 >= body.length()) {
            return null;
          }
          builder.append((char) Integer.parseInt(body.substring(i + 1, i + 5), 16));
          i += 4;
        }
        default -> {
          return null;
        }
      }
    }
    return builder.toString();
  }

  private static Integer charValue(String body) {
    String unescaped = unescape(body);
    return unescaped != null && unescaped.length() == 1 ? (int) unescaped.charAt(0) : null;
  }

  private static Long parseLong(String digits) {
    try {
      if (digits.startsWith("0x") || digits.startsWith("0X")) {
        return Long.parseLong(digits.substring(2), 16);
      }
      if (digits.startsWith("0b") || digits.startsWith("0B")) {
        return Long.parseLong(digits.substring(2), 2);
      }
      return Long.parseLong(digits);
    } catch (NumberFormatException e) {
      return null;
    }
  }

  private static boolean isIdentifierPart(char c) {
    return Character.isJavaIdentifierPart(c);
  }

  /**
   * Whether the text uses this simple name as an identifier.
   *
   * <p>A name embedded in a longer identifier is a different name: {@code EntityType} and
   * {@code nextSpawnData} say nothing about {@code Entity} or {@code SpawnData}, and a pool entry
   * for the latter is still unexplained evidence that the source named one of its constants.
   */
  private static boolean mentions(String text, String simple) {
    for (int i = text.indexOf(simple); i >= 0; i = text.indexOf(simple, i + 1)) {
      boolean before = i == 0 || !isIdentifierPart(text.charAt(i - 1));
      int end = i + simple.length();
      boolean after = end >= text.length() || !isIdentifierPart(text.charAt(end));
      if (before && after && !insideImport(text, i) && !afterAt(text, i)) {
        return true;
      }
    }
    return false;
  }

  /**
   * An import names a class without interning it, and an annotation names a class through its
   * descriptor: neither puts the class into the pool. A class the text reaches only that way is
   * still evidence that the source named one of its constants.
   */
  private static boolean insideImport(String text, int position) {
    int lineStart = text.lastIndexOf('\n', position) + 1;
    String line = text.substring(lineStart, Math.min(text.length(), position));
    return line.stripLeading().startsWith("import ");
  }

  /** Whether the nearest code character before this occurrence is an annotation's {@code @}. */
  private static boolean afterAt(String text, int position) {
    for (int i = position - 1; i >= 0; i--) {
      char c = text.charAt(i);
      if (c == ' ' || c == '\t') {
        continue;
      }
      return c == '@';
    }
    return false;
  }
}

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
    INT, LONG, FLOAT, DOUBLE, STRING, BOOLEAN, CHAR
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
      addOwnerCandidates(candidates, owner, nest, packageName, imports);
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
                       Set<String> strict, String own, Map<String, List<int[]>> ownInitializers,
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
                           Map<String, PairSite> pairs, Map<String, ValueSite> values) {
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
      List.of(), null, Set.of(), Map.of(), Map.of());

  /** One method's printed positions: bytecode offset to character offset, and the method's rank. */
  private record SiteSpace(int rank, Map<Integer, Integer> positions, int min, int max, String key) {
  }

  /** The first instruction that references a pool entry, in javac's code generation order. */
  private record FirstUse(int order, int offset, String methodKey) {
  }

  private static final long NO_COORDINATE = Long.MIN_VALUE;

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
      if (index != null && opensPool(own, index, setup, firstUses)) {
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
    Map<String, PairSite> pairs = pairSites(own, text, firstUses, catchTypes, setup, early, positions);
    Map<String, PairSite> activePairs = new HashMap<>();
    Map<String, ValueSite> values = valueSites(own, firstUses, catchTypes, setup, early, positions);
    Map<String, ValueSite> activeValues = new HashMap<>();
    for (Map.Entry<String, PairSite> entry : pairs.entrySet()) {
      String owner = entry.getKey();
      if (claimed.contains(owner) || owner.equals(own.qualifiedName) || isBootstrapOwner(owner)) {
        continue;
      }
      if (candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports);
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
        addOwnerCandidates(candidates, owner, nest, packageName, imports);
      }
      activeValues.put(owner, entry.getValue());
    }
    Set<String> inheritedNames = new HashSet<>();
    for (String owner : missing) {
      if (isBootstrapOwner(owner)) {
        continue;
      }
      if (candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports);
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
        continue;
      }
      if (candidateOwners.add(owner)) {
        addOwnerCandidates(candidates, owner, nest, packageName, imports);
      }
      claimed.add(owner);
      windows.put(owner, window);
      coordinates.put(owner, coordinates(firstUses, index, early, -1));
      strict.add(owner);
    }
    if (candidates.isEmpty()) {
      return null;
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
    return new Rules(candidates,
      new Placement(windows, coordinates, spaces(own, positions), strict, folded, internedAt,
        namingAt, lexical, spans, new HashSet<>(prefixOwners(own)), inheritedNames, activePairs,
        activeValues),
      strict, own.qualifiedName, ownInitializers(text, spans, own), imports, packageName);
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
   * <p>javac generates constructors first, then the other methods in class-file order, and
   * {@code <clinit>} last. The rank must come from the class's method list rather than from the
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
      int rank = CodeConstants.INIT_NAME.equals(method.getName()) ? i
        : CodeConstants.CLINIT_NAME.equals(method.getName()) ? 2 * count + i
        : count + i;
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
   * <p>javac generates constructors first, then the other method bodies in class-file order, and
   * {@code <clinit>} last. The instruction's offset orders the uses inside one method.
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
      int rank = CodeConstants.INIT_NAME.equals(method.getName()) ? i
        : CodeConstants.CLINIT_NAME.equals(method.getName()) ? 2 * count + i
        : count + i;
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
   * {@code lower} and {@code successor} to place the site.
   */
  private record PairSite(int classIndex, long successor, long lower, int open, int close,
                          String member, Set<String> pooled) {
    /** Whether naming a constant of this value enters no pool entry the original did not have. */
    boolean valueAvailable(String key) {
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
                                                 Map<Pair<String, String>, Map<Integer, Integer>> positions) {
    Map<String, PairSite> pairs = new HashMap<>();
    List<PooledConstant> pool = cls.getPool().getPool();
    for (int i = 1; i + 2 < pool.size(); i++) {
      if (!(pool.get(i) instanceof PrimitiveConstant entry)
          || entry.type != CodeConstants.CONSTANT_Class
          || entry.getString() == null || entry.index != i + 1) {
        continue;
      }
      String owner = entry.getString();
      if (owner.equals(cls.qualifiedName) || setup.contains(i) || catchTypes.contains(owner)) {
        continue; // the class is entered as itself, a catch type or a class-setup entry
      }
      if (!(pool.get(i + 2) instanceof LinkConstant link)) {
        continue;
      }
      boolean call = link.type == CodeConstants.CONSTANT_Methodref
        || link.type == CodeConstants.CONSTANT_InterfaceMethodref;
      if (!call && link.type != CodeConstants.CONSTANT_Fieldref) {
        continue; // the entry after the pair is neither a call nor a field reference
      }
      if (owner.equals(link.classname)) {
        continue; // the pair is that reference's operand
      }
      FirstUse use = firstUses.get(i + 2);
      if (use == null) {
        continue;
      }
      long point = coordinate(use.order(), use.offset());
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
      long[] bounds = coordinates(firstUses, i, early, -1);
      if (bounds[1] != point) {
        continue; // a higher entry was created before this reference; the pair is not its naming
      }
      int open = -1;
      int close = -1;
      if (call) {
        Integer printed = position(cls, use, positions);
        if (printed == null) {
          continue;
        }
        open = nextOpenParen(text, printed);
        if (open < 0) {
          continue;
        }
        close = matchingParen(text, open);
        if (close < 0) {
          continue;
        }
      }
      pairs.putIfAbsent(owner, new PairSite(i, point, bounds[0], open, close,
        call ? null : link.elementname, pooledKeys(cls, i)));
    }
    return pairs;
  }

  /** The first '(' printed after this position that belongs to a call on the same statement. */
  private static int nextOpenParen(String text, int from) {
    int limit = Math.min(text.length(), Math.max(0, from) + 200);
    for (int i = Math.max(0, from); i < limit; i++) {
      char c = text.charAt(i);
      if (c == '(') {
        return i;
      }
      if (c == ';' || c == '{' || c == '}' || c == '=' || c == '\n') {
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
  private static void scanClass(String text, List<int[]> spans, Rules rules, List<Site> sites) {
    Map<String, List<Site>> deferred = new HashMap<>();
    Set<String> inWindow = new HashSet<>();
    for (int[] span : spans) {
      scan(text, span[0], span[1], rules.candidates(), rules.imports(), rules.packageName(),
        sites, rules.own(), rules.ownInitializers(), rules.placement(), deferred, inWindow);
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
        if (hasSiteFor(sites, entry.getKey())) {
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
          if (pair.open() >= 0 && (site.start() <= pair.open() || site.start() >= pair.close())) {
            continue; // outside the call's argument list
          }
          long coordinate = siteCoordinate(rules.placement().spaces(), site.start());
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
            continue;
          }
          if ((coordinate >>> 32) != (pair.successor() >>> 32)
              || (coordinate & 0xffffffffL) >= (pair.successor() & 0xffffffffL)) {
            continue; // another method, or after the reference was generated
          }
          if (pair.open() < 0 && coordinate <= pair.lower()) {
            continue; // before the previous entry's first use; the naming would move it
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
        if (!rules.strict().contains(entry.getKey())) {
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
    for (int k = 0; k < owners.size(); k++) {
      String owner = owners.get(k);
      Site existing = firstInitializerSite(sites, owner, spans, initializers);
      if (existing != null) {
        last = Math.max(last, existing.start());
        continue;
      }
      // A later pair that already has a site in an initializer fixes the upper end of the field
      // interval this naming may use; a placement after it would reorder the pool.
      int limit = initializerLimit(sites, owners, k + 1, spans, initializers);
      boolean self = owner.equals(own.qualifiedName);
      List<SourceConstant> sources = self ? List.of() : sourceConstants(owner, own, imports, packageName);
      if (!self && sources.isEmpty()) {
        // This owner's naming cannot be written, and a later one would move up into its slot.
        return;
      }
      Site placed = null;
      for (int i = self ? 1 : 0; i < constants.size() && placed == null; i++) {
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
        if (self) {
          for (int j = 0; j < i; j++) {
            FieldConstant source = constants.get(j);
            String expression = constantExpression(target, source.kind(), source.value(),
              source.field().getName());
            if (expression != null) {
              placed = new Site(equals + 1, range[1], " " + expression, owner);
              break;
            }
          }
        }
        else {
          for (SourceConstant source : sources) {
            String expression = constantExpression(target, source.kind(), source.value(), source.name());
            if (expression != null) {
              placed = new Site(equals + 1, range[1], " " + expression, owner);
              break;
            }
          }
        }
      }
      if (placed == null) {
        return;
      }
      addSiteOnce(sites, placed);
      last = placed.start();
    }
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
    if (first < 0 || classIndex != first - 2) {
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
    List<String> names = key == null ? null : sources.get(key);
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
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return List.of();
    }
    String qualifier = qualifier(owner, site, imports, packageName);
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
      || imports.contains(simple)
      || (!nested && packageName.equals(packageOf(owner)));
    if (inScope) {
      return simple;
    }
    if (nested) {
      return anonymous(owner) || !publiclyNameable(owner, packageName) ? null
        : owner.replace('/', '.').replace('$', '.');
    }
    return owner.replace('/', '.');
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

  /** An expression over a source constant that folds to {@code target}'s exact value, or null. */
  private static String constantExpression(FieldConstant target, VariableType sourceKind,
                                           Object sourceValue, String name) {
    VariableType t = target.kind();
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
    return binaryExpression(target, sourceKind, sourceValue, name);
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
      default -> "";
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
      for (StructInnerClassesAttribute.Entry entry : inner.getEntries()) {
        if (entry.innerName != null) {
          explained.add(entry.innerName);
        }
        if (entry.enclosingName != null) {
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

  /** The accessible static final fields of one missing owner, as candidates for a literal value. */
  private static void addOwnerCandidates(Map<String, List<Constant>> candidates, String owner,
                                         String nest, String packageName, List<String> imports) {
    StructClass cls = DecompilerContext.getStructContext().getClass(owner);
    if (cls == null) {
      return;
    }
    boolean samePackage = packageName.equals(packageOf(owner));
    boolean imported = imports.contains(simpleName(owner));
    if (!samePackage && !imported && owner.contains("$")) {
      return; // a nested class's binary name cannot be written in source
    }
    for (StructField field : cls.getFields()) {
      if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
          != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
        continue;
      }
      int access = field.getAccessFlags();
      boolean accessible = (access & CodeConstants.ACC_PUBLIC) != 0
        || ((access & CodeConstants.ACC_PRIVATE) == 0 && samePackage)
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
      // never candidates for a plain integer literal.
      case "I" -> VariableType.INT;
      case "C" -> VariableType.CHAR;
      case "Z" -> VariableType.BOOLEAN;
      case "J" -> VariableType.LONG;
      case "F" -> VariableType.FLOAT;
      case "D" -> VariableType.DOUBLE;
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
      if ((cls.getAccessFlags() & CodeConstants.ACC_PUBLIC) == 0
          && !packageName.equals(packageOf(name))) {
        return false;
      }
      int dollar = name.lastIndexOf('$');
      if (dollar < 0) {
        return true;
      }
      name = name.substring(0, dollar);
    }
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
      java.util.regex.Matcher matcher = java.util.regex.Pattern
        .compile("\\b" + java.util.regex.Pattern.quote(field.getName()) + "\\s*=")
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
          ranges.computeIfAbsent(field.getName(), k -> new ArrayList<>()).add(new int[]{matcher.start(), i});
        }
      }
    }
    return ranges;
  }

  private static void scan(String text, Map<String, List<Constant>> candidates, List<String> imports,
                           String packageName, List<Site> sites, String own,
                           Map<String, List<int[]>> ownInitializers) {
    scan(text, 0, text.length(), candidates, imports, packageName, sites, own, ownInitializers,
      NO_PLACEMENT, null, null);
  }

  private static void scan(String text, int from, int to, Map<String, List<Constant>> candidates,
                           List<String> imports, String packageName, List<Site> sites, String own,
                           Map<String, List<int[]>> ownInitializers, Placement placement,
                           Map<String, List<Site>> deferred, Set<String> inWindow) {
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
          if (value != null && !value.isEmpty()) {
            addSite(sites, i, end, VariableType.STRING + "|" + value, "", candidates, imports, packageName, own, ownInitializers,
              placement, deferred, inWindow);
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
              placement, deferred, inWindow);
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
            placement, deferred, inWindow);
        }
        i = end;
        continue;
      }
      if (Character.isDigit(c) && (i == 0 || !isIdentifierPart(text.charAt(i - 1)))) {
        i = scanNumber(text, i, sites, candidates, imports, packageName, own, ownInitializers,
          placement, deferred, inWindow);
        continue;
      }
      i++;
    }
  }

  /** The '-' of a unary minus directly before this literal, or -1 for a binary minus. */
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
    return Character.isLetterOrDigit(c) || c == '_' || c == ')' || c == ']' || c == '"' || c == '\'' ? -1 : i;
  }

  private static int scanNumber(String text, int start, List<Site> sites,
                                Map<String, List<Constant>> candidates, List<String> imports,
                                String packageName, String own, Map<String, List<int[]>> ownInitializers,
                                Placement placement, Map<String, List<Site>> deferred,
                                Set<String> inWindow) {
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
        // explains the literal, try the int constant of the same value.
        List<Constant> asLong = candidates.get(kind + "|" + value);
        if ((asLong == null || asLong.size() != 1)
            && number >= Integer.MIN_VALUE && number <= Integer.MAX_VALUE) {
          addSite(sites, negative ? negativeAt : start, i, VariableType.INT.name() + "|" + number, "",
            candidates, imports, packageName, own, ownInitializers, placement, deferred, inWindow);
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
    addSite(sites, siteStart, i, kind + "|" + value, "", candidates, imports, packageName, own, ownInitializers,
      placement, deferred, inWindow);
    if (kind.equals(VariableType.FLOAT.name())) {
      addSite(sites, siteStart, i, "FLOATCAST|" + value, "", candidates, imports, packageName, own, ownInitializers,
        placement, deferred, inWindow);
    }
    if (!negative && (kind.equals(VariableType.FLOAT.name()) || kind.equals(VariableType.DOUBLE.name()))) {
      addIntegralSite(start, i, value, kind.equals(VariableType.FLOAT.name()), sites, candidates, imports,
        packageName, own, ownInitializers, placement, deferred, inWindow);
    }
    if (kind.equals(VariableType.DOUBLE.name())) {
      addWidenedFloatSite(siteStart, i, value, negative, sites, candidates, imports, packageName, own,
        ownInitializers, placement, deferred, inWindow);
    }
    if (negative && value.startsWith("-")) {
      // The source can write a positive constant behind a unary minus; the literal is then the
      // negation of the constant, not a negative constant of its own.
      String magnitude = value.substring(1);
      addSite(sites, siteStart, i, kind + "|" + magnitude, "-", candidates, imports, packageName, own,
        ownInitializers, placement, deferred, inWindow);
      if (kind.equals(VariableType.FLOAT.name())) {
        addSite(sites, siteStart, i, "FLOATCAST|" + magnitude, "-", candidates, imports, packageName, own,
          ownInitializers, placement, deferred, inWindow);
      }
      if (kind.equals(VariableType.LONG.name())) {
        try {
          long mag = Long.parseLong(magnitude);
          List<Constant> asLong = candidates.get(kind + "|" + magnitude);
          if ((asLong == null || asLong.size() != 1) && mag <= Integer.MAX_VALUE) {
            addSite(sites, siteStart, i, VariableType.INT.name() + "|" + mag, "-", candidates, imports,
              packageName, own, ownInitializers, placement, deferred, inWindow);
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
                              Set<String> inWindow) {
    List<Constant> constants = candidates.get(key);
    if (constants == null || constants.isEmpty()) {
      return;
    }
    // A quoted literal is printed by enclosing a buffer whose mapping sits at its content start,
    // so the recorded position of the instruction is one past the opening quote.
    int anchor = key.startsWith(VariableType.STRING.name() + "|")
      || key.startsWith(VariableType.CHAR.name() + "|") ? start + 1 : start;
    Constant constant = constants.size() == 1
      ? constants.get(0) : selectProvable(constants, anchor, placement, own);
    if (constant == null) {
      return;
    }
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
    if (window == null && !placed && !recorded && tooCommon(key)) {
      return;
    }
    if (constant.owner().equals(own)) {
      for (int[] range : ownInitializers.getOrDefault(constant.name(), List.of())) {
        if (start >= range[0] && start < range[1]) {
          return; // a constant cannot be named inside its own initializer
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
        || imports.contains(name)
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
                                      Map<String, List<Site>> deferred, Set<String> inWindow) {
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
        || !placement.windows().containsKey(owner) || !placement.proves(owner, start)
        || tooCommon(key)) {
      return;
    }
    // The constant javac interned beside the owner's Class entry is the pool's own record of the
    // value the source named there; a literal of another value did not come from this constant.
    Double folded = placement.folded().get(owner);
    double literal = single ? (double) Float.parseFloat(printed) : Double.parseDouble(printed);
    if (folded == null || Double.compare(folded, literal) != 0) {
      return;
    }
    // The literal was a float or double, and an integral constant is not: a bare name would turn
    // `intExpr / NAME` into an integer division. The cast keeps the literal's type, and a cast of a
    // constant variable is itself a constant expression, so the compiled value is unchanged.
    addSite(sites, start, end, key, single ? "(float) " : "(double) ", candidates, imports,
      packageName, own, ownInitializers, placement, deferred, inWindow);
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
                                          Map<String, List<Site>> deferred, Set<String> inWindow) {
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
        || !placement.windows().containsKey(owner) || !placement.proves(owner, start)) {
      return;
    }
    Double folded = placement.folded().get(owner);
    double literal = negative ? -magnitude : magnitude;
    if (folded == null || Double.compare(folded, literal) != 0) {
      return;
    }
    addSite(sites, start, end, key, negative ? "-(double) " : "(double) ", candidates, imports,
      packageName, own, ownInitializers, placement, deferred, inWindow);
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
      if (before && after) {
        return true;
      }
    }
    return false;
  }
}

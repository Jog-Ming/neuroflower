// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructConstantValueAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructEnclosingMethodAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructExceptionsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructInnerClassesAttribute;
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

  private record Site(int start, int end, String replacement) {
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
      if (!simple.isEmpty() && !text.contains(simple) && !explained.contains(owner)) {
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
    for (Map.Entry<String, List<int[]>> entry : spansByClass.entrySet()) {
      ClassNode node = byName.get(entry.getKey());
      if (node == null) {
        continue; // text attributed to a class we have no pool for; leave it alone
      }
      Rules classRules = rules(text, entry.getValue(), node, positions, imports, packageName);
      if (classRules != null) {
        scanClass(text, entry.getValue(), classRules, sites);
      }
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
                           List<SiteSpace> spaces) {
    /** Whether this text position lies where the pool order proves the owner was named. */
    boolean proves(String owner, int start) {
      int[] window = windows == null ? null : windows.get(owner);
      if (window != null && start >= window[0] && start < window[1]) {
        return true;
      }
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
  }

  private static final Placement NO_PLACEMENT = new Placement(null, null, List.of());

  /** One method's printed positions: bytecode offset to character offset, and the method's rank. */
  private record SiteSpace(int rank, Map<Integer, Integer> positions, int min, int max) {
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
    for (SiteSpace space : spaces) {
      if (position < space.min || position > space.max) {
        continue;
      }
      int offset = -1;
      for (Map.Entry<Integer, Integer> entry : space.positions.entrySet()) {
        if (entry.getValue() <= position && entry.getKey() > offset) {
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
   * the pool order and it is never used as a bound.
   */
  private static long[] coordinates(Map<Integer, FirstUse> firstUses, int index, Set<Integer> early) {
    long pred = Long.MIN_VALUE;
    long succ = Long.MAX_VALUE;
    for (Map.Entry<Integer, FirstUse> entry : firstUses.entrySet()) {
      int key = entry.getKey();
      if (key == index || early.contains(key)) {
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

    Map<Integer, FirstUse> firstUses = firstUses(own);
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
      if (!simple.isEmpty() && !selfText.contains(simple) && !explained.contains(owner)) {
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
    String nest = nestOf(own.qualifiedName);
    for (String owner : missing) {
      if (isBootstrapOwner(owner)) {
        continue;
      }
      addOwnerCandidates(candidates, owner, nest, packageName, imports);
      Integer index = classIndices.get(owner);
      if (index != null) {
        int[] window = window(text, own, index, orderedUses, positions, false);
        if (window != null) {
          windows.put(owner, window);
        }
        coordinates.put(owner, coordinates(firstUses, index, early));
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
      if (window == null) {
        continue;
      }
      addOwnerCandidates(candidates, owner, nest, packageName, imports);
      windows.put(owner, window);
      coordinates.put(owner, coordinates(firstUses, index, early));
      strict.add(owner);
    }
    if (candidates.isEmpty()) {
      return null;
    }
    return new Rules(candidates, new Placement(windows, coordinates, spaces(own, positions, firstUses)),
      strict, own.qualifiedName, ownInitializers(text, spans, own), imports, packageName);
  }

  /**
   * The printed positions of this class's method bodies and static initializers, each tagged with
   * its generation rank. Instance field initializers are printed under a {@code <field-init>} key
   * that does not name the constructor their offsets belong to, so they are left out.
   */
  private static List<SiteSpace> spaces(StructClass own,
                                        Map<Pair<String, String>, Map<Integer, Integer>> positions,
                                        Map<Integer, FirstUse> firstUses) {
    Map<String, Integer> ranks = new HashMap<>();
    for (FirstUse use : firstUses.values()) {
      ranks.putIfAbsent(use.methodKey(), use.order());
    }
    List<SiteSpace> spaces = new ArrayList<>();
    for (Map.Entry<Pair<String, String>, Map<Integer, Integer>> entry : positions.entrySet()) {
      if (!own.qualifiedName.equals(entry.getKey().a) || entry.getValue().isEmpty()) {
        continue;
      }
      Integer rank = ranks.get(entry.getKey().b);
      if (rank == null) {
        continue;
      }
      int min = Integer.MAX_VALUE;
      int max = Integer.MIN_VALUE;
      for (int position : entry.getValue().values()) {
        min = Math.min(min, position);
        max = Math.max(max, position);
      }
      spaces.add(new SiteSpace(rank, entry.getValue(), min, max));
    }
    return spaces;
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
   * Where each pool entry an instruction references is first used.
   *
   * <p>javac generates constructors first, then the other method bodies in class-file order, and
   * {@code <clinit>} last. The instruction's offset orders the uses inside one method.
   */
  private static Map<Integer, FirstUse> firstUses(StructClass cls) {
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
    // A static field initializer is printed at its declaration but generated inside <clinit>, and
    // the printer records its positions under a field-initializer key rather than <clinit>.
    if (use.methodKey().startsWith(CodeConstants.CLINIT_NAME)) {
      for (Map.Entry<Pair<String, String>, Map<Integer, Integer>> entry : positions.entrySet()) {
        if (cls.qualifiedName.equals(entry.getKey().a)
            && entry.getKey().b.startsWith("<field-init ")
            && entry.getValue().containsKey(use.offset())) {
          return entry.getValue().get(use.offset());
        }
      }
    }
    return method == null ? null : method.get(use.offset());
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
   * may have been placed in the wrong text order) and all of that owner's sites are allowed again.
   */
  private static void scanClass(String text, List<int[]> spans, Rules rules, List<Site> sites) {
    Map<String, List<Site>> deferred = new HashMap<>();
    Set<String> inWindow = new HashSet<>();
    for (int[] span : spans) {
      scan(text, span[0], span[1], rules.candidates(), rules.imports(), rules.packageName(),
        sites, rules.own(), rules.ownInitializers(), rules.placement(), deferred, inWindow);
    }
    for (Map.Entry<String, List<Site>> entry : deferred.entrySet()) {
      if (!inWindow.contains(entry.getKey())) {
        // A referenced owner's window is the only evidence of where the original named it; without
        // a site inside the window there is nothing to place the name against.
        if (!rules.strict().contains(entry.getKey())) {
          for (Site site : entry.getValue()) {
            addSiteOnce(sites, site);
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
    Constant constant = constants.size() == 1
      ? constants.get(0) : selectProvable(constants, start, placement, own);
    if (constant == null) {
      return;
    }
    boolean foreign = !constant.owner().equals(own);
    int[] window = placement == null || placement.windows() == null || !foreign
      ? null : placement.windows().get(constant.owner());
    // The pool order in generation order is exact: the site must fall after every lower entry's
    // first use and before every higher entry's first use. A text window only approximates it; the
    // coordinate check places the site by the positions the printer recorded for its method, which
    // also covers a static field initializer generated in <clinit> but printed at its declaration.
    boolean placed = foreign && placement != null && placement.proves(constant.owner(), start);
    // A frequent value is only weak evidence where there is no better one. A window means the pool
    // proves this owner was named somewhere, and the value only has to pick among its constants;
    // the site itself is still placed by the window or its fallback below.
    if (window == null && !placed && tooCommon(key)) {
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
    if (placement != null && placement.windows() != null && constant.owner().equals(own)
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
    // A foreign owner's naming site is bounded by where the original interned the owner's Class
    // entry. The class's own constants are exempt: its Class entry is in the pool regardless, so
    // the pool order says nothing about when the source named one of them.
    if (window != null) {
      if (!placed) {
        if (deferred != null) {
          deferred.computeIfAbsent(constant.owner(), k -> new ArrayList<>()).add(new Site(start, end, printed));
        }
        return;
      }
      if (inWindow != null) {
        inWindow.add(constant.owner());
      }
    }
    addSiteOnce(sites, new Site(start, end, printed));
  }

  /**
   * The one candidate the pool order proves for this site when several constants share the value.
   *
   * <p>A value alone cannot choose between owners, and naming the wrong one adds its class to the
   * pool at a position the original never had. A window or an exact generation-order placement is
   * evidence that the owner was named here; two such owners at one site is still a guess.
   */
  private static Constant selectProvable(List<Constant> constants, int start, Placement placement,
                                         String own) {
    if (placement == null) {
      return null;
    }
    Constant chosen = null;
    for (Constant constant : constants) {
      if (!constant.owner().equals(own) && placement.proves(constant.owner(), start)) {
        if (chosen != null) {
          return null;
        }
        chosen = constant;
      }
    }
    return chosen;
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
}

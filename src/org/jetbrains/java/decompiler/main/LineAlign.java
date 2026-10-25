// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.collectors.BytecodeMappingTracer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLineNumberTableAttribute;
import org.jetbrains.java.decompiler.util.Pair;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Moves the printed source onto the original's line numbers without compiling.
 *
 * <p>The printer already records, for every bytecode offset, the line it printed that instruction
 * on, and the class being decompiled carries the original LineNumberTable. Comparing the two gives
 * one constraint per entry: this printed line must move to that original line. Blank padding lines
 * shift the following text down; blank or padding lines that carry no entry at all can be deleted or
 * joined onto the line above, shifting the text up. A line whose two entries want different shifts
 * is left alone, and a shift that cannot be paid in full is paid in part, so one stubborn method
 * does not cost the file every other alignment.
 */
public final class LineAlign {
  /**
   * A blank line. Padding must not invent a comment: the source's own comments are unknown, and a
   * comment line is a claim about text the class file does not record. A blank line shifts the
   * following lines exactly the same way.
   */
  static final String PADDING = "";
  private static final String[][] RECORD_MEMBERS = {
    {"hashCode", "()I"},
    {"equals", "(Ljava/lang/Object;)Z"},
    {"toString", "()Ljava/lang/String;"},
  };
  private static final boolean debug = System.getenv("NEUROFLOWER_LINEALIGN_DEBUG") != null;

  private LineAlign() {
  }

  /** The aligned text, or null when the buffer cannot be aligned and must be left as printed. */
  public static String align(TextBuffer buffer, ClassesProcessor.ClassNode root) {
    String text = buffer.convertToStringAndAllowDataDiscard();
    if (DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_CONSTANT_SITES)) {
      try {
        // Runs on the printed text before any line edit, so the bytecode positions the buffer
        // recorded still describe this string. The switch replaces the whole-file constant pass.
        text = ConstantNames.restore(text, root, buffer.getBytecodePositions(),
          buffer.getClassRegions());
      }
      catch (RuntimeException e) {
        // A class must not be lost because its constant sites could not be classified.
      }
    }
    String separator = DecompilerContext.getNewLineSeparator();
    String[] lines = text.split(java.util.regex.Pattern.quote(separator), -1);

    Map<Pair<String, String>, BytecodeMappingTracer> tracers;
    try {
      tracers = buffer.getTracers();
    } catch (RuntimeException e) {
      return null;
    }

    if (DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_SAME_LINE_JOIN)) {
      String joined = joinSameTargetLines(text, separator, lines, tracers);
      if (joined != null) {
        text = joined;
        lines = text.split(java.util.regex.Pattern.quote(separator), -1);
      }
    }

    boolean gapAlign = DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_GAP_ALIGN);
    TreeMap<Integer, Integer> shifts = new TreeMap<>();
    Set<Integer> conflicted = new HashSet<>();
    Set<Integer> entryLines = new HashSet<>();
    Map<Integer, List<int[]>> candidates = new TreeMap<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> tracerEntry : tracers.entrySet()) {
      String className = tracerEntry.getKey().a;
      String methodKey = tracerEntry.getKey().b;
      Map<Integer, Integer> mapping = tracerEntry.getValue().getMapping();
      if (methodKey.startsWith("<field-init ")) {
        // The initializer's own offsets say which constructor generated it; that constructor's
        // table places each declaration separately, so a block of fields is not stuck on one line.
        StructLineNumberTableAttribute owner = initializerTable(className, mapping.keySet());
        if (owner != null && gapAlign) {
          addMethodConstraints(owner, mapping, lines, candidates, entryLines);
          continue;
        }
        Integer target = fieldInitLine(className, mapping.keySet());
        if (target == null) {
          continue;
        }
        for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
          int ours = entry.getValue() + 1;
          if (ours < 1 || ours > lines.length) {
            continue;
          }
          entryLines.add(ours);
          add(shifts, conflicted, ours, target - ours);
        }
        continue;
      }
      StructLineNumberTableAttribute table = lineTable(className, methodKey);
      if (table == null) {
        continue;
      }
      if (gapAlign) {
        addMethodConstraints(table, mapping, lines, candidates, entryLines);
        continue;
      }
      for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
        int ours = entry.getValue() + 1; // one based line in this file
        int target = table.findLineNumber(entry.getKey());
        if (target < 0 || ours < 1 || ours > lines.length) {
          continue;
        }
        entryLines.add(ours);
        add(shifts, conflicted, ours, target - ours);
      }
    }
    // An implicit constructor has no source text to map, yet javac places its one entry on the
    // class declaration's line. Without this constraint the declaration never moves, and every
    // class with a default constructor stays shifted by however far the original header was.
    addImplicitConstructorConstraints(tracers, lines, shifts, conflicted, entryLines, root);
    resolveCandidates(candidates, shifts, conflicted);

    if (DecompilerContext.getOption(IFernflowerPreferences.ML_BREAKS)
        || System.getenv("NEUROFLOWER_ML_BREAKS") != null) {
      logModelAgreement(tracers);
    }

    for (int line : conflicted) {
      shifts.remove(line);
    }
    if (shifts.isEmpty()) {
      return text;
    }

    List<int[]> inserts = new ArrayList<>();
    List<Integer> removals = new ArrayList<>();
    List<Integer> joins = new ArrayList<>();

    if (gapAlign) {
      if (!walkGaps(lines, shifts, entryLines, inserts, removals, joins)) {
        return text;
      }
    }
    else {
      int previous = 0;
      int previousIndex = -1;
      for (Map.Entry<Integer, Integer> entry : shifts.entrySet()) {
        int index = entry.getKey() - 1;
        int target = entry.getValue();
        if (index < 0 || index > lines.length) {
          return text;
        }
        if (target > previous) {
          if (insideTextBlock(lines, index)) {
            return text;
          }
          inserts.add(new int[]{index, target - previous});
        } else if (target < previous) {
          int want = previous - target;
          int need = want;
          int lowest = previousIndex;
          for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
            if (removable(lines, i)) {
              removals.add(i);
              need--;
            }
          }
          for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
            // A join moves line i onto line i-1, so neither may be a line another edit deletes.
            if (joinable(lines, i, entryLines) && !removals.contains(i) && !removals.contains(i - 1)
                && !joins.contains(i)) {
              joins.add(i);
              need--;
            }
          }
          target = previous - (want - need);
          if (debug && need > 0) {
            System.err.println("underpaid line " + entry.getKey() + " want " + want + " unpaid " + need
              + " from " + lowest + " to " + index);
          }
        }
        previous = target;
        previousIndex = index;
      }
    }
    if (debug) {
      System.err.println("align " + text.hashCode() + " shifts " + shifts.size()
        + " conflicts " + conflicted.size()
        + " inserts " + inserts.stream().map(a -> a[0] + "+" + a[1]).toList()
        + " removals " + removals.size() + " joins " + joins.size());
      String dump = System.getenv("NEUROFLOWER_LINEALIGN_DUMP");
      if (dump != null) {
        String[] range = dump.split(",");
        int from = range.length > 0 ? Integer.parseInt(range[0].trim()) : 205;
        int to = range.length > 1 ? Integer.parseInt(range[1].trim()) : from + 35;
        for (int i = Math.max(1, from); i <= Math.min(to, lines.length); i++) {
          System.err.println("L" + i + " shift=" + shifts.get(i) + " | " + lines[i - 1]);
        }
      }
    }
    if (inserts.isEmpty() && removals.isEmpty() && joins.isEmpty()) {
      return text;
    }

    List<int[]> edits = new ArrayList<>();
    for (int[] insert : inserts) {
      edits.add(new int[]{insert[0], 0, insert[1]});
    }
    for (int removal : removals) {
      edits.add(new int[]{removal, 1, 0});
    }
    for (int join : joins) {
      edits.add(new int[]{join, 2, 0});
    }
    edits.sort((a, b) -> Integer.compare(b[0], a[0]));
    List<String> edited = new ArrayList<>(List.of(lines));
    for (int[] edit : edits) {
      if (edit[1] == 0) {
        for (int k = 0; k < edit[2]; k++) {
          edited.add(edit[0], PADDING);
        }
      } else if (edit[1] == 1) {
        edited.remove(edit[0]);
      } else {
        edited.set(edit[0] - 1, edited.get(edit[0] - 1) + " " + edited.get(edit[0]).trim());
        edited.remove(edit[0]);
      }
    }
    String aligned = String.join(separator, edited);
    // Alignment may only move lines and whitespace. If the token text changed at all, the layout
    // was wrong: keep the unaligned text rather than ship a source that may not compile.
    if (!normalized(aligned, separator).equals(normalized(text, separator))) {
      return text;
    }
    return aligned;
  }

  /**
   * Joins two printed lines that the original's table puts on the same source line.
   *
   * <p>Each line carries the bytecode offsets the printer wrote its statements from, and the
   * original's table gives each offset its source line. Two adjacent lines whose offsets all map to
   * one and the same line can only mean the original wrote those statements on one line; the join
   * is proven by the table rather than guessed from a missing entry. Only offsets of one method are
   * joined, so two lambdas that happen to share a target line stay apart.
   */
  private static String joinSameTargetLines(String text, String separator, String[] lines,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers) {
    Map<Integer, Integer> target = new java.util.HashMap<>();
    Map<Integer, String> owner = new java.util.HashMap<>();
    Set<Integer> mixed = new HashSet<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> tracerEntry : tracers.entrySet()) {
      String methodKey = tracerEntry.getKey().b;
      if (methodKey.startsWith("<field-init ")) {
        continue;
      }
      StructLineNumberTableAttribute table = lineTable(tracerEntry.getKey().a, methodKey);
      if (table == null) {
        continue;
      }
      for (Map.Entry<Integer, Integer> entry : tracerEntry.getValue().getMapping().entrySet()) {
        int line = entry.getValue() + 1;
        int source = table.findLineNumber(entry.getKey());
        if (source < 0 || line < 1 || line > lines.length) {
          continue;
        }
        Integer previous = target.putIfAbsent(line, source);
        if (previous != null && previous != source) {
          mixed.add(line);
        }
        String method = owner.putIfAbsent(line, methodKey);
        if (method != null && !method.equals(methodKey)) {
          mixed.add(line);
        }
      }
    }
    java.util.TreeSet<Integer> joins = new java.util.TreeSet<>();
    for (int line = 2; line <= lines.length; line++) {
      Integer here = target.get(line);
      Integer above = target.get(line - 1);
      if (here == null || above == null || !here.equals(above)
          || mixed.contains(line) || mixed.contains(line - 1)
          || !owner.get(line).equals(owner.get(line - 1))) {
        continue;
      }
      if (mergeableWithEvidence(lines, line)) {
        joins.add(line);
      }
    }
    if (joins.isEmpty()) {
      return null;
    }
    List<String> edited = new ArrayList<>(List.of(lines));
    for (int line : joins.descendingSet()) {
      edited.set(line - 2, edited.get(line - 2) + " " + edited.get(line - 1).trim());
      edited.remove(line - 1);
    }
    for (BytecodeMappingTracer tracer : tracers.values()) {
      for (Map.Entry<Integer, Integer> entry : tracer.getMapping().entrySet()) {
        int line = entry.getValue() + 1;
        int removed = joins.headSet(line, true).size();
        entry.setValue(line - removed - 1);
      }
    }
    if (debug) {
      System.err.println("same-target joins " + joins.size());
    }
    return String.join(separator, edited);
  }

  /** A line that may be joined onto the one above: no comment, no blank, not in a text block. */
  private static boolean mergeableWithEvidence(String[] lines, int lineNumber) {
    int index = lineNumber - 1;
    if (index <= 0 || index >= lines.length) {
      return false;
    }
    if (insideTextBlock(lines, index) || insideTextBlock(lines, index - 1)) {
      return false;
    }
    if (lines[index - 1].contains("//") || lines[index - 1].contains("/*") || lines[index].contains("*/")) {
      return false;
    }
    return !lines[index].trim().isEmpty();
  }

  private static String normalized(String text, String separator) {
    StringBuilder builder = new StringBuilder(text.length());
    for (String line : text.split(java.util.regex.Pattern.quote(separator), -1)) {
      String trimmed = line.trim();
      if (trimmed.equals(PADDING)) {
        continue;
      }
      for (int i = 0; i < line.length(); i++) {
        char c = line.charAt(i);
        if (!Character.isWhitespace(c)) {
          builder.append(c);
        }
      }
    }
    return builder.toString();
  }

  /**
   * The original source line of an instance field initializer. Its offsets belong to one of the
   * constructors, and in that constructor the whole initializer maps to the field's line; other
   * constructors map those offsets to unrelated lines, so the line every offset agrees on is the
   * field's.
   */
  /**
   * The line table of the constructor a lifted field initializer was generated into, or null when
   * several constructors contain its offsets or none does. The printer records the initializer
   * once, at its declaration, while javac emitted it into every constructor that reaches it; the
   * copy whose code covers every recorded offset is the one whose table places the declarations.
   */
  private static StructLineNumberTableAttribute initializerTable(String className,
      java.util.Set<Integer> offsets) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null || offsets.isEmpty()) {
      return null;
    }
    StructLineNumberTableAttribute found = null;
    for (StructMethod method : cls.getMethods()) {
      if (!"<init>".equals(method.getName())) {
        continue;
      }
      if (method.getInstructionSequence() == null) {
        try {
          method.expandData(cls);
        }
        catch (Exception e) {
          continue;
        }
      }
      FullInstructionSequence code = method.getInstructionSequence();
      if (code == null || !coversOffsets(code, offsets)) {
        continue;
      }
      if (found != null) {
        return null;
      }
      found = method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    }
    return found;
  }

  private static boolean coversOffsets(
      FullInstructionSequence code, java.util.Set<Integer> offsets) {
    java.util.Set<Integer> remaining = new HashSet<>(offsets);
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

  private static Integer fieldInitLine(String className, java.util.Set<Integer> offsets) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null) {
      return null;
    }
    Integer found = null;
    for (StructMethod method : cls.getMethods()) {
      if (!"<init>".equals(method.getName())) {
        continue;
      }
      StructLineNumberTableAttribute table =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (table == null) {
        continue;
      }
      Set<Integer> distinct = new HashSet<>();
      for (int offset : offsets) {
        int line = table.findLineNumber(offset);
        if (line >= 0) {
          distinct.add(line);
        }
      }
      if (distinct.size() == 1) {
        int line = distinct.iterator().next();
        if (found != null && found != line) {
          return null;
        }
        found = line;
      }
    }
    return found;
  }

  /** How often the model's line-start prediction matches the target's own line table. */
  private static void logModelAgreement(
      Map<Pair<String, String>, BytecodeMappingTracer> tracers) {
    LineBreakModel model = LineBreakModel.current();
    if (model == null) {
      System.err.println("ml-breaks: no weights loaded");
      return;
    }
    long agree = 0;
    long total = 0;
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> entry : tracers.entrySet()) {
      String className = entry.getKey().a;
      String methodKey = entry.getKey().b;
      StructClass cls = DecompilerContext.getStructContext().getClass(className);
      StructMethod method = cls == null ? null : cls.getMethod(methodKey);
      StructLineNumberTableAttribute table = method == null ? null
        : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (method != null && method.getInstructionSequence() == null) {
        try {
          method.expandData(cls); // released after decompilation; reparse for inference
        } catch (java.io.IOException e) {
          // leave the method out
        }
      }
      org.jetbrains.java.decompiler.code.FullInstructionSequence code =
        method == null ? null : method.getInstructionSequence();
      if (table == null || code == null) {
        if (System.getenv("NEUROFLOWER_ML_DEBUG") != null) {
          System.err.println("ml-skip " + methodKey + " table " + (table != null) + " code " + (code != null)
            + " method " + (method != null));
        }
        continue;
      }
      Map<Integer, Integer> mapping = entry.getValue().getMapping();
      Integer previousTarget = null;
      String previousOp = null;
      int lastLine = -1;
      int run = -1;
      int index = 0;
      for (Instruction instruction : code) {
        Integer printed = mapping.get(instruction.startOffset);
        int target = table.findLineNumber(instruction.startOffset);
        if (System.getenv("NEUROFLOWER_ML_DEBUG") != null && index < 3) {
          System.err.println("ml-instr " + methodKey + " off " + instruction.startOffset
            + " printed " + printed + " target " + target);
        }
        if (printed != null && target >= 0) {
          if (printed == lastLine) {
            run++;
          } else {
            run = 0;
            lastLine = printed;
          }
          String op = "op:" + instruction.opcode;
          if (previousTarget != null) {
            boolean truth = target != previousTarget;
            boolean predicted = model.startsLine(previousOp, op, index, code.length(), run);
            if (truth == predicted) {
              agree++;
            }
            total++;
          }
          previousTarget = target;
          previousOp = op;
        }
        index++;
      }
    }
    System.err.println("ml-breaks tracers " + tracers.size());
    System.err.println("ml-breaks agreement " + agree + "/" + total
      + " (" + (total == 0 ? 0 : (100.0 * agree / total)) + "%)");
  }

  private static void addImplicitConstructorConstraints(
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines,
      ClassesProcessor.ClassNode root) {
    if (root != null) {
      anchorClassLines(root, 0, tracers, lines, shifts, conflicted, entryLines);
    }
  }

  private static void anchorClassLines(ClassesProcessor.ClassNode node, int enclosingLine,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines) {
    String className = node.classStruct == null ? null : node.classStruct.qualifiedName;
    int declaration = -1;
    if (className != null) {
      String simple = className.substring(className.lastIndexOf('/') + 1);
      int dollar = simple.lastIndexOf('$');
      if (dollar >= 0) {
        simple = simple.substring(dollar + 1);
      }
      if (!simple.isEmpty() && Character.isJavaIdentifierStart(simple.charAt(0))) {
        declaration = classDeclarationLine(lines, simple, enclosingLine,
          firstMemberLine(className, tracers, lines), declarationHint(node.classStruct, className, tracers));
        if (declaration >= 0) {
          anchorOne(node.classStruct, className, declaration, tracers, lines, shifts, conflicted, entryLines);
        }
      }
    }
    int childEnclosing = declaration >= 0 ? declaration : enclosingLine;
    for (ClassesProcessor.ClassNode nested : node.nested) {
      anchorClassLines(nested, childEnclosing, tracers, lines, shifts, conflicted, entryLines);
    }
  }

  private static int firstMemberLine(String className,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines) {
    int first = lines.length + 1;
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> entry : tracers.entrySet()) {
      if (!className.equals(entry.getKey().a)) {
        continue;
      }
      for (int line : entry.getValue().getMapping().values()) {
        first = Math.min(first, line + 1);
      }
    }
    return first;
  }

  private static void anchorOne(StructClass cls, String className, int declaration,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines) {
    {
      // A record's generated members (hashCode, equals, toString, accessors) are all attributed to
      // the record declaration line, which no printed construct maps.
      if (cls.getRecordComponents() != null) {
        for (String[] generated : RECORD_MEMBERS) {
          String key = org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
            generated[0], generated[1]);
          if (tracers.containsKey(Pair.of(className, key))) {
            continue; // an explicit declaration carries its own line
          }
          StructMethod method = cls.getMethod(generated[0], generated[1]);
          StructLineNumberTableAttribute table = method == null ? null
            : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
          int target = table == null ? -1 : table.findLineNumber(0);
          if (target >= 0) {
            entryLines.add(declaration);
            add(shifts, conflicted, declaration, target - declaration);
            break;
          }
        }
      }
      // An enum's values() and $values() are anchored to the enum declaration line, which no
      // printed construct maps; without it the declaration drifts by however many header lines the
      // original had.
      if ((cls.getAccessFlags()
          & org.jetbrains.java.decompiler.code.CodeConstants.ACC_ENUM) != 0) {
        StructMethod values = cls.getMethod("values", "()[L" + className + ";");
        StructLineNumberTableAttribute table = values == null ? null
          : values.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        int target = table == null ? -1 : table.findLineNumber(0);
        if (target >= 0) {
          entryLines.add(declaration);
          add(shifts, conflicted, declaration, target - declaration);
        }
      }
      for (StructMethod method : cls.getMethods()) {
        boolean bridge = (method.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_BRIDGE) != 0;
        boolean accessor = isSyntheticAccessor(method);
        if (!"<init>".equals(method.getName()) && !bridge && !accessor) {
          continue;
        }
        BytecodeMappingTracer tracer = tracers.get(
          Pair.of(className, org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
            method.getName(), method.getDescriptor())));
        if (tracer != null && !tracer.getMapping().isEmpty()) {
          continue; // an explicit member carries its own constraints
        }
        StructLineNumberTableAttribute table =
          method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        if (table == null) {
          continue;
        }
        int target = table.findLineNumber(0);
        if (target < 0) {
          continue;
        }
        if ((bridge || accessor) && !singleLine(table)) {
          continue; // a bridge spanning several lines is not anchored to the declaration
        }
        int anchor = bridge || accessor
          ? classDeclarationTop(lines, declaration, 0)
          : declaration;
        entryLines.add(anchor);
        add(shifts, conflicted, anchor, target - anchor);
      }
    }
  }

  /**
   * A compiler-generated access method for a private member read from a nested class.
   *
   * <p>It is not printed, and javac gives its single line entry the class declaration's line, so
   * it anchors the declaration exactly like a bridge.
   */
  private static boolean isSyntheticAccessor(StructMethod method) {
    return method.getName().startsWith("access$")
      && (method.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_SYNTHETIC) != 0;
  }

  private static void collectNodes(ClassesProcessor.ClassNode node, List<ClassesProcessor.ClassNode> out) {
    if (node == null) {
      return;
    }
    out.add(node);
    for (ClassesProcessor.ClassNode nested : node.nested) {
      collectNodes(nested, out);
    }
  }

  private static boolean singleLine(StructLineNumberTableAttribute table) {
    int[] raw = table.getRawData();
    int first = raw.length < 2 ? -1 : raw[1];
    for (int i = 3; i < raw.length; i += 2) {
      if (raw[i] != first) {
        return false;
      }
    }
    return first >= 0;
  }

  /**
   * The line of this class's declaration in the printed file.
   *
   * <p>Several nested classes may share a simple name, so a file can hold more than one matching
   * declaration. The last one before the class's first member used to be taken, which fails for a
   * class with no members at all: the search then covers the rest of the file and lands on a
   * sibling's declaration. The target's own line for the class's anchor -- its hidden constructor,
   * its generated record members, or its enum's values() -- is where the declaration was, so the
   * candidate closest to it is the right one whenever such a line exists.
   */
  private static int classDeclarationLine(String[] lines, String simple, int enclosing, int beforeMember,
      int hint) {
    java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
      "\\b(?:class|record|enum|interface)\\s+" + java.util.regex.Pattern.quote(simple) + "\\b");
    int found = -1;
    int end = Math.min(lines.length, beforeMember - 1);
    int closest = Integer.MAX_VALUE;
    for (int i = Math.max(0, enclosing); i < end; i++) {
      if (!pattern.matcher(lines[i]).find()) {
        continue;
      }
      if (hint >= 0) {
        int distance = Math.abs((i + 1) - hint);
        if (distance < closest) {
          closest = distance;
          found = i + 1;
        }
      }
      else {
        found = i + 1;
      }
    }
    return found;
  }

  /** The line the target attributes this class's declaration to, or minus one when it says nothing. */
  private static int declarationHint(StructClass cls, String className,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers) {
    if (cls == null) {
      return -1;
    }
    if (cls.getRecordComponents() != null) {
      for (String[] generated : RECORD_MEMBERS) {
        String key = org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
          generated[0], generated[1]);
        if (tracers.containsKey(Pair.of(className, key))) {
          continue;
        }
        StructMethod method = cls.getMethod(generated[0], generated[1]);
        StructLineNumberTableAttribute table = method == null ? null
          : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        int target = table == null ? -1 : table.findLineNumber(0);
        if (target >= 0) {
          return target;
        }
      }
    }
    if ((cls.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_ENUM) != 0) {
      StructMethod values = cls.getMethod("values", "()[L" + className + ";");
      StructLineNumberTableAttribute table = values == null ? null
        : values.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      int target = table == null ? -1 : table.findLineNumber(0);
      if (target >= 0) {
        return target;
      }
    }
    for (StructMethod method : cls.getMethods()) {
      boolean bridge = (method.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_BRIDGE) != 0;
      boolean accessor = isSyntheticAccessor(method);
      if (!"<init>".equals(method.getName()) && !bridge && !accessor) {
        continue;
      }
      BytecodeMappingTracer tracer = tracers.get(
        Pair.of(className, org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
          method.getName(), method.getDescriptor())));
      if (tracer != null && !tracer.getMapping().isEmpty()) {
        continue;
      }
      StructLineNumberTableAttribute table =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (table == null) {
        continue;
      }
      int target = table.findLineNumber(0);
      if (target >= 0) {
        return target;
      }
    }
    return -1;
  }

  /** The first line of the declaration block, annotations included; javac anchors bridges there. */
  private static int classDeclarationTop(String[] lines, int declaration, int enclosing) {
    if (declaration < 0) {
      return -1;
    }
    int top = declaration;
    for (int i = declaration - 2; i >= enclosing; i--) {
      String text = lines[i].trim();
      if (text.isEmpty() || text.equals(PADDING)) {
        continue;
      }
      if (text.startsWith("@")) {
        top = i + 1;
        continue;
      }
      break;
    }
    return top;
  }

  private static StructLineNumberTableAttribute lineTable(String className, String methodKey) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null) {
      return null;
    }
    StructMethod method = cls.getMethod(methodKey);
    return method == null ? null : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
  }

  private static void add(TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, int line, int shift) {
    if (conflicted.contains(line)) {
      return;
    }
    Integer known = shifts.putIfAbsent(line, shift);
    if (known != null && known != shift) {
      shifts.remove(line);
      conflicted.add(line);
    }
  }

  /**
   * Builds the anchors one method at a time, in bytecode order.
   *
   * <p>An instruction can be recorded on a line earlier than the entry before it only when the
   * printer mapped it at a statement boundary rather than where its text sits: a lifted
   * initializer maps its last instruction to the declaration's line, and the store a switch
   * merges out of its arms maps to the header's. The instruction's text is then on the line the
   * previous entry closes, and the original's line continues that entry's by at most one. Such
   * a record moves its target there. A target that moves back belongs to an invocation printed
   * before its own arguments, and one that jumps ahead belongs to a synthetic closing-brace
   * mapping; both keep their own line, as any other entry does.
   */
  private static void addMethodConstraints(StructLineNumberTableAttribute table,
      Map<Integer, Integer> mapping, String[] lines, Map<Integer, List<int[]>> candidates,
      Set<Integer> entryLines) {
    int[] raw = table.getRawData();
    Set<Integer> exact = new HashSet<>();
    for (int i = 0; i + 1 < raw.length; i += 2) {
      exact.add(raw[i]);
    }
    List<int[]> entries = new ArrayList<>(mapping.size());
    for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
      int ours = entry.getValue() + 1; // one based line in this file
      int target = table.findLineNumber(entry.getKey());
      if (target < 0 || ours < 1 || ours > lines.length) {
        continue;
      }
      entries.add(new int[]{entry.getKey(), ours, target, exact.contains(entry.getKey()) ? 1 : 0});
    }
    entries.sort((a, b) -> Integer.compare(a[0], b[0]));
    int previousLine = -1;
    int highest = -1;
    for (int[] entry : entries) {
      if (entry[1] < previousLine && entry[2] >= highest && entry[2] <= highest + 1) {
        highest = entry[2];
        entryLines.add(previousLine);
        candidate(candidates, previousLine, entry[2] - previousLine, entry[3]);
        continue;
      }
      previousLine = entry[1];
      highest = Math.max(highest, entry[2]);
      entryLines.add(entry[1]);
      candidate(candidates, entry[1], entry[2] - entry[1], entry[3]);
    }
  }

  private static void candidate(Map<Integer, List<int[]>> candidates, int line, int shift, int exact) {
    candidates.computeIfAbsent(line, k -> new ArrayList<>()).add(new int[]{shift, exact});
  }

  /**
   * Settles every line the method walk produced a constraint for.
   *
   * <p>A line whose instructions all agree keeps that shift. When they do not, the disagreement is
   * usually one instruction that inherited its line from an earlier LineNumberTable entry and is
   * printed on another line than the entry's own instruction: a chain link's receiver, or the store
   * of an expression spanning several lines. Such an inherited line describes the entry it came
   * from, not the text printed beside it. The instructions that have an entry of their own are the
   * ones whose text this printed line actually holds; a line still starts where the earliest of
   * them does, which is the statement's own line rather than an operand's continuation.
   */
  private static void resolveCandidates(Map<Integer, List<int[]>> candidates,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted) {
    for (Map.Entry<Integer, List<int[]>> line : candidates.entrySet()) {
      Set<Integer> all = new java.util.TreeSet<>();
      Set<Integer> exact = new java.util.TreeSet<>();
      for (int[] candidate : line.getValue()) {
        all.add(candidate[0]);
        if (candidate[1] != 0) {
          exact.add(candidate[0]);
        }
      }
      if (all.size() == 1) {
        add(shifts, conflicted, line.getKey(), all.iterator().next());
      }
      else if (!exact.isEmpty()) {
        // The line's first token is the statement's start, and the instructions printed before
        // the operands that continue it carry the earliest original line among its own entries.
        add(shifts, conflicted, line.getKey(), exact.iterator().next());
      }
      else {
        shifts.remove(line.getKey());
        conflicted.add(line.getKey());
      }
    }
  }

  /**
   * Places the anchors one gap at a time: two consecutive anchors must be as many lines apart
   * as they are in the original. A gap that is too short gets padding before the later anchor;
   * one that is too long loses blank or joinable lines between them. Only when a method's own
   * anchors cannot pay a gap does the walk reclaim padding parked in an earlier gap.
   *
   * <p>Returns false when an insertion would fall inside a text block, in which case the buffer
   * must stay as printed.
   */
  private static boolean walkGaps(String[] lines, TreeMap<Integer, Integer> shifts,
      Set<Integer> entryLines, List<int[]> inserts, List<Integer> removals, List<Integer> joins) {
    List<int[]> placed = new ArrayList<>(); // {index, paid shift, required shift}
    int previous = 0;
    int previousIndex = -1;
    for (Map.Entry<Integer, Integer> entry : shifts.entrySet()) {
      int index = entry.getKey() - 1;
      int desired = entry.getValue();
      if (index < 0 || index > lines.length) {
        return false;
      }
      int paid = desired;
      if (desired > previous) {
        if (insideTextBlock(lines, index)) {
          return false;
        }
        inserts.add(new int[]{index, desired - previous});
      }
      else if (desired < previous) {
        int want = previous - desired;
        int need = want;
        int lowest = previousIndex;
        for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
          if (removable(lines, i) && !removals.contains(i)) {
            removals.add(i);
            need--;
          }
        }
        for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
          // A join moves line i onto line i-1, so neither may be a line another edit deletes.
          if (joinable(lines, i, entryLines) && !removals.contains(i) && !removals.contains(i - 1)
              && !joins.contains(i)) {
            joins.add(i);
            need--;
          }
        }
        if (need > 0) {
          need -= reclaim(lines, need, previousIndex, placed, removals, joins);
        }
        paid = previous - (want - need);
        if (debug && need > 0) {
          System.err.println("gap underpaid line " + entry.getKey() + " want " + want + " unpaid " + need
            + " from " + lowest + " to " + index);
        }
      }
      placed.add(new int[]{index, paid, desired});
      previous = paid;
      previousIndex = index;
    }
    return true;
  }

  /**
   * Deletes blank or padding lines from gaps before the previous anchor to pay a gap that has
   * nothing left of its own. Every anchor that follows a deleted line is lifted one line, so a
   * line may only be taken while all of them are still above their own targets: the lift then
   * moves them closer instead of past them. Returns how many lines were taken.
   */
  private static int reclaim(String[] lines, int need, int previousIndex, List<int[]> placed,
      List<Integer> removals, List<Integer> joins) {
    int found = 0;
    int anchor = placed.size() - 1;
    int limit = Integer.MAX_VALUE;
    for (int i = previousIndex - 1; i >= 0 && need > 0; i--) {
      while (anchor >= 0 && placed.get(anchor)[0] > i) {
        int[] entry = placed.get(anchor--);
        limit = Math.min(limit, entry[1] - entry[2]); // paid minus required: how far it can rise
      }
      if (limit <= 0) {
        break;
      }
      // A join planned on line i or i-1 claims this one; deleting it would take text with it.
      if (removable(lines, i) && !removals.contains(i)
          && !joins.contains(i) && !joins.contains(i + 1)) {
        removals.add(i);
        found++;
        need--;
        limit--;
        for (int k = anchor + 1; k < placed.size(); k++) {
          placed.get(k)[1]--;
        }
      }
    }
    return found;
  }

  private static boolean joinable(String[] lines, int index, Set<Integer> entryLines) {
    if (index <= 0 || index >= lines.length) {
      return false;
    }
    if (entryLines.contains(index + 1)) {
      return false;
    }
    if (index == lines.length - 1 && lines[index].isEmpty()) {
      return false;
    }
    if (insideTextBlock(lines, index) || insideTextBlock(lines, index - 1)) {
      return false;
    }
    if (lines[index - 1].contains("//") || lines[index - 1].contains("/*") || lines[index].contains("*/")) {
      return false;
    }
    return !lines[index].trim().isEmpty();
  }

  private static boolean removable(String[] lines, int index) {
    if (index < 0 || index >= lines.length) {
      return false;
    }
    if (index == lines.length - 1 && lines[index].isEmpty()) {
      return false;
    }
    String trimmed = lines[index].trim();
    return (trimmed.isEmpty() || trimmed.equals(PADDING)) && !insideTextBlock(lines, index);
  }

  private static boolean insideTextBlock(String[] lines, int index) {
    int delimiters = 0;
    for (int i = 0; i < index && i < lines.length; i++) {
      int from = 0;
      while (true) {
        int at = lines[i].indexOf("\"\"\"", from);
        if (at < 0) {
          break;
        }
        delimiters++;
        from = at + 3;
      }
    }
    return delimiters % 2 == 1;
  }
}

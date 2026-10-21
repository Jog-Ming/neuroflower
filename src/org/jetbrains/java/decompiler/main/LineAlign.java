// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.main.collectors.BytecodeMappingTracer;
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
  static final String PADDING = "// line-number padding: restores the original LineNumberTable";
  private static final String[][] RECORD_MEMBERS = {
    {"hashCode", "()I"},
    {"equals", "(Ljava/lang/Object;)Z"},
    {"toString", "()Ljava/lang/String;"},
  };
  private static final boolean debug = System.getenv("NEUROFLOWER_LINEALIGN_DEBUG") != null;

  private LineAlign() {
  }

  /** The aligned text, or null when the buffer cannot be aligned and must be left as printed. */
  public static String align(TextBuffer buffer) {
    String text = buffer.convertToStringAndAllowDataDiscard();
    String separator = DecompilerContext.getNewLineSeparator();
    String[] lines = text.split(java.util.regex.Pattern.quote(separator), -1);

    Map<Pair<String, String>, BytecodeMappingTracer> tracers;
    try {
      tracers = buffer.getTracers();
    } catch (RuntimeException e) {
      return null;
    }

    TreeMap<Integer, Integer> shifts = new TreeMap<>();
    Set<Integer> conflicted = new HashSet<>();
    Set<Integer> entryLines = new HashSet<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> tracerEntry : tracers.entrySet()) {
      String className = tracerEntry.getKey().a;
      String methodKey = tracerEntry.getKey().b;
      Map<Integer, Integer> mapping = tracerEntry.getValue().getMapping();
      if (methodKey.startsWith("<field-init ")) {
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
    addImplicitConstructorConstraints(tracers, lines, shifts, conflicted, entryLines);

    for (int line : conflicted) {
      shifts.remove(line);
    }
    if (shifts.isEmpty()) {
      return text;
    }

    List<int[]> inserts = new ArrayList<>();
    List<Integer> removals = new ArrayList<>();
    List<Integer> joins = new ArrayList<>();
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
          if (joinable(lines, i, entryLines) && !removals.contains(i) && !removals.contains(i - 1)) {
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
    if (debug) {
      System.err.println("align " + text.hashCode() + " shifts " + shifts.size()
        + " conflicts " + conflicted.size()
        + " inserts " + inserts.stream().map(a -> a[0] + "+" + a[1]).toList()
        + " removals " + removals.size() + " joins " + joins.size());
      if (System.getenv("NEUROFLOWER_LINEALIGN_DUMP") != null) {
        for (int i = 205; i <= Math.min(240, lines.length); i++) {
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

  private static void addImplicitConstructorConstraints(
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines) {
    Set<String> seen = new HashSet<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> entry : tracers.entrySet()) {
      String className = entry.getKey().a;
      if (!seen.add(className)) {
        continue;
      }
      StructClass cls = DecompilerContext.getStructContext().getClass(className);
      if (cls == null) {
        continue;
      }
      String simple = className.substring(className.lastIndexOf('/') + 1);
      int dollar = simple.lastIndexOf('$');
      if (dollar >= 0) {
        simple = simple.substring(dollar + 1);
      }
      if (simple.isEmpty() || !Character.isJavaIdentifierStart(simple.charAt(0))) {
        continue;
      }
      int declaration = classDeclarationLine(lines, simple);
      if (declaration < 0) {
        continue;
      }
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
        if (!"<init>".equals(method.getName())) {
          continue;
        }
        BytecodeMappingTracer tracer = tracers.get(
          Pair.of(className, org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
            method.getName(), method.getDescriptor())));
        if (tracer != null && !tracer.getMapping().isEmpty()) {
          continue; // an explicit constructor carries its own constraints
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
        entryLines.add(declaration);
        add(shifts, conflicted, declaration, target - declaration);
      }
    }
  }

  private static int classDeclarationLine(String[] lines, String simple) {
    java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
      "\\b(?:class|record|enum|interface)\\s+" + java.util.regex.Pattern.quote(simple) + "\\b");
    for (int i = 0; i < lines.length; i++) {
      if (pattern.matcher(lines[i]).find()) {
        return i + 1;
      }
    }
    return -1;
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

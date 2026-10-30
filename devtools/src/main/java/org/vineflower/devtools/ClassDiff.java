package org.vineflower.devtools;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.AnnotationNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InnerClassNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.LocalVariableAnnotationNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.ParameterNode;
import org.objectweb.asm.tree.RecordComponentNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Compares one compiled class file with the jar's original and reports which attributes match.
 *
 * The comparison is structural, not textual: ASM resolves constant-pool indices to symbolic
 * references, so {@code code} says whether the instruction streams are the same even when the pool
 * is permuted, while {@code bytes} stays the strictest check. Reading only -- nothing is written.
 */
public final class ClassDiff {
  public static final List<String> ATTRIBUTES = List.of(
    "bytes", "members", "code", "lnt", "lvt", "params", "annotations", "signature", "inner", "frames");
  /** Not an attribute table column: byte equality after every LineNumberTable is stripped. */
  public static final String NOLNT = "nolnt";

  public final String name;
  public final Map<String, Boolean> matches = new LinkedHashMap<>();
  public final List<String> details = new ArrayList<>();
  /** True when the two class files are identical after every LineNumberTable is removed. */
  public boolean noLnt = true;

  private ClassDiff(String name) {
    this.name = name;
    for (String attribute : ATTRIBUTES) {
      matches.put(attribute, true);
    }
    matches.put(NOLNT, true);
  }

  public boolean all() {
    return ATTRIBUTES.stream().allMatch(attribute -> matches.getOrDefault(attribute, true));
  }

  public static ClassDiff compare(byte[] originalBytes, byte[] recompiledBytes) {
    ClassDiff diff = new ClassDiff(className(originalBytes));
    if (!diff.name.equals(className(recompiledBytes))) {
      diff.fail("members", "class name differs: " + className(recompiledBytes));
      return diff;
    }
    if (java.util.Arrays.equals(originalBytes, recompiledBytes)) {
      return diff;
    }
    diff.fail("bytes", "raw bytes differ");
    byte[] originalNoLnt = stripLineNumbers(originalBytes);
    byte[] recompiledNoLnt = stripLineNumbers(recompiledBytes);
    diff.noLnt = java.util.Arrays.equals(originalNoLnt, recompiledNoLnt);
    diff.matches.put(NOLNT, diff.noLnt);
    if (!diff.noLnt) {
      int at = 0;
      int limit = Math.min(originalNoLnt.length, recompiledNoLnt.length);
      while (at < limit && originalNoLnt[at] == recompiledNoLnt[at]) {
        at++;
      }
      diff.details.add("nolnt: first difference at byte " + at
        + " (lengths " + originalNoLnt.length + " vs " + recompiledNoLnt.length + ")");
    }

    ClassNode original = parse(originalBytes);
    ClassNode recompiled = parse(recompiledBytes);

    if (original.access != recompiled.access) {
      diff.fail("members", "access " + original.access + " vs " + recompiled.access);
    }
    if (!Objects.equals(original.superName, recompiled.superName)) {
      diff.fail("members", "super " + original.superName + " vs " + recompiled.superName);
    }
    if (!Objects.equals(original.interfaces, recompiled.interfaces)) {
      diff.fail("members", "interfaces " + original.interfaces + " vs " + recompiled.interfaces);
    }
    if (!Objects.equals(original.signature, recompiled.signature)
      || !signatures(original.fields).equals(signatures(recompiled.fields))
      || !methodSignatures(original.methods).equals(methodSignatures(recompiled.methods))) {
      diff.fail("signature", "signature attributes differ");
    }
    if (!annotations(original.visibleAnnotations, original.invisibleAnnotations)
      .equals(annotations(recompiled.visibleAnnotations, recompiled.invisibleAnnotations))
      || !fieldAnnotations(original.fields).equals(fieldAnnotations(recompiled.fields))
      || !methodAnnotations(original.methods).equals(methodAnnotations(recompiled.methods))) {
      diff.fail("annotations", "annotations differ");
    }
    if (!members(original).equals(members(recompiled))) {
      diff.fail("members", "field/method list differs");
    }
    if (!inner(original).equals(inner(recompiled))) {
      diff.fail("inner", "inner/enclosing/nest/record metadata differs");
    }

    Map<String, MethodNode> originalMethods = byKey(original.methods);
    Map<String, MethodNode> recompiledMethods = byKey(recompiled.methods);
    for (Map.Entry<String, MethodNode> entry : originalMethods.entrySet()) {
      MethodNode ours = recompiledMethods.get(entry.getKey());
      if (ours == null) {
        continue; // reported by members
      }
      MethodNode theirs = entry.getValue();
      if (!code(theirs).equals(code(ours))) {
        diff.fail("code", entry.getKey() + " " + firstInstructionDifference(theirs, ours));
      }
      List<String> originalLines = lnt(theirs);
      List<String> ourLines = lnt(ours);
      if (!originalLines.equals(ourLines)) {
        diff.fail("lnt", entry.getKey() + " " + lntSummary(originalLines, ourLines));
      }
      if (!lvt(theirs).equals(lvt(ours))) {
        diff.fail("lvt", entry.getKey());
        if (System.getenv("NEUROFLOWER_DIFF_DUMP") != null) {
          System.err.println("LVT " + entry.getKey());
          System.err.println("LVT jar " + localRows(theirs));
          System.err.println("LVT our " + localRows(ours));
        }
      }
      if (!parameters(theirs).equals(parameters(ours))) {
        diff.fail("params", entry.getKey());
      }
      if (!frames(theirs).equals(frames(ours))) {
        diff.fail("frames", entry.getKey());
      }
    }
    return diff;
  }

  /**
   * The class file with every LineNumberTable removed and every other byte -- the constant pool
   * and its order included -- copied verbatim. Comparison only: nothing here is ever written back
   * as a class; it exists so "identical except for the line table" is a measurable statement.
   */
  static byte[] stripLineNumbers(byte[] bytes) {
    Reader in = new Reader(bytes);
    Writer out = new Writer(bytes.length);
    in.copy(4, out);                                   // magic
    in.copy(4, out);                                   // minor, major
    int poolCount = in.u2();
    out.u2(poolCount);
    String[] utf8 = new String[poolCount];
    for (int i = 1; i < poolCount; i++) {
      int tag = in.u1();
      out.u1(tag);
      switch (tag) {
        case 1 -> {
          int length = in.u2();
          out.u2(length);
          byte[] text = in.copy(length, out);
          utf8[i] = new String(text, java.nio.charset.StandardCharsets.UTF_8);
        }
        case 7, 8, 16, 19, 20 -> in.copy(2, out);
        case 15 -> in.copy(3, out);
        case 3, 4, 9, 10, 11, 12, 17, 18 -> in.copy(4, out);
        case 5, 6 -> {
          in.copy(8, out);
          i++;
        }
        default -> throw new IllegalStateException("constant pool tag " + tag);
      }
    }
    in.copy(6, out);                                   // access, this, super
    int interfaces = in.u2();
    out.u2(interfaces);
    in.copy(interfaces * 2, out);
    int fields = in.u2();
    out.u2(fields);
    for (int i = 0; i < fields; i++) {
      copyMember(in, out, utf8, false);
    }
    int methods = in.u2();
    out.u2(methods);
    for (int i = 0; i < methods; i++) {
      copyMember(in, out, utf8, true);
    }
    int attributes = in.u2();
    out.u2(attributes);
    for (int i = 0; i < attributes; i++) {
      copyAttribute(in, out);
    }
    return out.toByteArray();
  }

  private static void copyMember(Reader in, Writer out, String[] utf8, boolean method) {
    in.copy(6, out);                                   // access, name, descriptor
    int attributes = in.u2();
    out.u2(attributes);
    for (int i = 0; i < attributes; i++) {
      int nameIndex = in.peekU2();
      if (method && "Code".equals(utf8[nameIndex])) {
        in.u2();
        in.u4();
        byte[] body = stripCode(in, utf8);
        out.u2(nameIndex);
        out.u4(body.length);
        out.copy(body, null);
      } else {
        copyAttribute(in, out);
      }
    }
  }

  private static byte[] stripCode(Reader in, String[] utf8) {
    Writer body = new Writer(256);
    int maxStack = in.u2();
    int maxLocals = in.u2();
    body.u2(maxStack);
    body.u2(maxLocals);
    int codeLength = in.u4();
    body.u4(codeLength);
    in.copy(codeLength, body);
    int handlers = in.u2();
    body.u2(handlers);
    in.copy(handlers * 8, body);
    int attributes = in.u2();
    Writer kept = new Writer(64);
    int keptCount = 0;
    for (int i = 0; i < attributes; i++) {
      int nameIndex = in.u2();
      int length = in.u4();
      byte[] content = in.copy(length, null);
      if ("LineNumberTable".equals(utf8[nameIndex])) {
        continue;
      }
      keptCount++;
      kept.u2(nameIndex);
      kept.u4(length);
      kept.copy(content, null);
    }
    body.u2(keptCount);
    byte[] keptBytes = kept.toByteArray();
    body.copy(keptBytes, null);
    return body.toByteArray();
  }

  private static void copyAttribute(Reader in, Writer out) {
    int nameIndex = in.u2();
    int length = in.u4();
    out.u2(nameIndex);
    out.u4(length);
    in.copy(length, out);
  }

  private static final class Reader {
    private final byte[] bytes;
    private int at;

    Reader(byte[] bytes) {
      this.bytes = bytes;
    }

    int u1() {
      return bytes[at++] & 0xff;
    }

    int u2() {
      return (bytes[at++] & 0xff) << 8 | (bytes[at++] & 0xff);
    }

    int u4() {
      return (bytes[at++] & 0xff) << 24 | (bytes[at++] & 0xff) << 16
        | (bytes[at++] & 0xff) << 8 | (bytes[at++] & 0xff);
    }

    int peekU2() {
      return (bytes[at] & 0xff) << 8 | (bytes[at + 1] & 0xff);
    }

    byte[] copy(int length, Writer out) {
      byte[] slice = java.util.Arrays.copyOfRange(bytes, at, at + length);
      at += length;
      if (out != null) {
        out.copy(slice, null);
      }
      return slice;
    }
  }

  private static final class Writer {
    private final java.io.ByteArrayOutputStream bytes;

    Writer(int hint) {
      this.bytes = new java.io.ByteArrayOutputStream(hint);
    }

    void u1(int value) {
      bytes.write(value & 0xff);
    }

    void u2(int value) {
      bytes.write(value >>> 8 & 0xff);
      bytes.write(value & 0xff);
    }

    void u4(int value) {
      bytes.write(value >>> 24 & 0xff);
      bytes.write(value >>> 16 & 0xff);
      bytes.write(value >>> 8 & 0xff);
      bytes.write(value & 0xff);
    }

    void copy(byte[] slice, Writer ignored) {
      bytes.writeBytes(slice);
    }

    byte[] toByteArray() {
      return bytes.toByteArray();
    }
  }

  private void fail(String attribute, String detail) {
    matches.put(attribute, false);
    if (details.size() < 16) {
      details.add(attribute + ": " + detail);
    }
  }

  private static String className(byte[] bytes) {
    return new ClassReader(bytes).getClassName();
  }

  static ClassNode parse(byte[] bytes) {
    ClassNode node = new ClassNode(Opcodes.ASM9);
    new ClassReader(bytes).accept(node, ClassReader.EXPAND_FRAMES);
    return node;
  }

  private static Map<String, MethodNode> byKey(List<MethodNode> methods) {
    Map<String, MethodNode> map = new LinkedHashMap<>();
    for (MethodNode method : methods) {
      map.put(method.name + method.desc, method);
    }
    return map;
  }

  // ------------------------------------------------------------------ members and metadata

  private static List<String> members(ClassNode node) {
    List<String> list = new ArrayList<>();
    for (FieldNode field : node.fields) {
      list.add("F " + field.name + " " + field.desc + " " + field.access);
    }
    for (MethodNode method : node.methods) {
      list.add("M " + method.name + method.desc + " " + method.access);
    }
    return list;
  }

  private static List<String> signatures(List<FieldNode> fields) {
    List<String> list = new ArrayList<>();
    for (FieldNode field : fields) {
      list.add(field.name + " " + field.signature);
    }
    return list;
  }

  private static List<String> methodSignatures(List<MethodNode> methods) {
    List<String> list = new ArrayList<>();
    for (MethodNode method : methods) {
      list.add(method.name + method.desc + " " + method.signature);
    }
    return list;
  }

  private static String annotations(List<AnnotationNode> visible, List<AnnotationNode> invisible) {
    return renderAnnotations(visible) + "|" + renderAnnotations(invisible);
  }

  private static List<String> fieldAnnotations(List<FieldNode> fields) {
    List<String> list = new ArrayList<>();
    for (FieldNode field : fields) {
      list.add(field.name + annotations(field.visibleAnnotations, field.invisibleAnnotations));
    }
    return list;
  }

  private static List<String> methodAnnotations(List<MethodNode> methods) {
    List<String> list = new ArrayList<>();
    for (MethodNode method : methods) {
      list.add(method.name + method.desc + annotations(method.visibleAnnotations, method.invisibleAnnotations)
        + annotations(method.visibleParameterAnnotations, method.invisibleParameterAnnotations));
    }
    return list;
  }

  private static String annotations(List<AnnotationNode>[] visible, List<AnnotationNode>[] invisible) {
    StringBuilder builder = new StringBuilder("[");
    builder.append(renderAnnotationArray(visible)).append('|').append(renderAnnotationArray(invisible));
    return builder.append(']').toString();
  }

  private static String renderAnnotationArray(List<AnnotationNode>[] arrays) {
    if (arrays == null) {
      return "-";
    }
    StringBuilder builder = new StringBuilder();
    for (List<AnnotationNode> list : arrays) {
      builder.append(renderAnnotations(list)).append(';');
    }
    return builder.toString();
  }

  private static String renderAnnotations(List<AnnotationNode> nodes) {
    if (nodes == null || nodes.isEmpty()) {
      return "";
    }
    List<String> rendered = new ArrayList<>();
    for (AnnotationNode node : nodes) {
      rendered.add(node.desc + renderValues(node.values));
    }
    rendered.sort(String::compareTo);
    return rendered.toString();
  }

  private static String renderValues(List<Object> values) {
    if (values == null || values.isEmpty()) {
      return "()";
    }
    List<String> pairs = new ArrayList<>();
    for (int i = 0; i + 1 < values.size(); i += 2) {
      pairs.add(values.get(i) + "=" + renderValue(values.get(i + 1)));
    }
    pairs.sort(String::compareTo);
    return "(" + String.join(",", pairs) + ")";
  }

  private static String renderValue(Object value) {
    if (value instanceof AnnotationNode node) {
      return "@" + node.desc + renderValues(node.values);
    }
    if (value instanceof List<?> list) {
      return list.stream().map(ClassDiff::renderValue).toList().toString();
    }
    if (value instanceof Type type) {
      return type.toString();
    }
    return String.valueOf(value);
  }

  private static String inner(ClassNode node) {
    StringBuilder builder = new StringBuilder();
    if (node.innerClasses != null) {
      for (InnerClassNode inner : node.innerClasses) {
        builder.append(inner.name).append(' ').append(inner.outerName).append(' ')
          .append(inner.innerName).append(' ').append(inner.access).append(';');
      }
    }
    builder.append('|').append(node.outerClass).append(' ').append(node.outerMethod)
      .append(node.outerMethodDesc).append('|').append(node.nestHostClass).append(' ')
      .append(node.nestMembers).append('|').append(node.permittedSubclasses).append('|');
    if (node.recordComponents != null) {
      for (RecordComponentNode component : node.recordComponents) {
        builder.append(component.name).append(' ').append(component.descriptor).append(' ')
          .append(component.signature).append(';');
      }
    }
    return builder.toString();
  }

  // ------------------------------------------------------------------ method bodies

  static String code(MethodNode method) {
    StringBuilder builder = new StringBuilder();
    builder.append(method.maxStack).append('/').append(method.maxLocals).append(':');
    InsnList instructions = method.instructions;
    // Number a label by the position of the next real instruction, not by label order: the debug
    // table and stack-map frames add labels, and their count must not make equal code unequal.
    Map<LabelNode, Integer> labels = new HashMap<>();
    int position = 0;
    for (AbstractInsnNode insn = instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LabelNode label) {
        labels.putIfAbsent(label, position);
      } else if (!(insn instanceof LineNumberNode) && !(insn instanceof FrameNode)) {
        position++;
      }
    }
    for (AbstractInsnNode insn = instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LineNumberNode || insn instanceof FrameNode || insn instanceof LabelNode) {
        continue;
      }
      builder.append(render(insn, labels)).append(';');
    }
    if (method.tryCatchBlocks != null) for (TryCatchBlockNode block : method.tryCatchBlocks) {
      builder.append("tc ").append(label(block.start, labels)).append(' ')
        .append(label(block.end, labels)).append(' ').append(label(block.handler, labels)).append(' ')
        .append(block.type).append(';');
    }
    return builder.toString();
  }

  /** The first instruction where two equal-length sequences diverge, rendered compactly. */
  private static String firstInstructionDifference(MethodNode original, MethodNode recompiled) {
    List<String> a = renderedInstructions(original);
    List<String> b = renderedInstructions(recompiled);
    if (System.getenv("NEUROFLOWER_DIFF_DUMP") != null) {
      int limit = Math.min(a.size(), b.size());
      int at = -1;
      for (int i = 0; i < limit; i++) {
        if (!a.get(i).equals(b.get(i))) {
          at = i;
          break;
        }
      }
      int from = Math.max(0, at - 25);
      int to = Math.min(limit, at + 25);
      System.err.println("DUMP " + original.name + original.desc + " first=" + at);
      for (int i = from; i < to; i++) {
        boolean same = a.get(i).equals(b.get(i));
        System.err.println("DUMP " + i + (same ? "  " : " *") + " " + a.get(i) + (same ? "" : "   ||   " + b.get(i)));
      }
    }
    int limit = Math.min(a.size(), b.size());
    for (int i = 0; i < limit; i++) {
      if (!a.get(i).equals(b.get(i))) {
        return "at " + i + ": " + clip(a.get(i)) + " vs " + clip(b.get(i));
      }
    }
    if (a.size() != b.size()) {
      return "length " + a.size() + " vs " + b.size();
    }
    return "max stack/locals differ";
  }

  private static List<String> renderedInstructions(MethodNode method) {
    List<String> out = new ArrayList<>();
    Map<LabelNode, Integer> labels = new HashMap<>();
    int position = 0;
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LabelNode label) {
        labels.putIfAbsent(label, position);
      } else if (!(insn instanceof LineNumberNode) && !(insn instanceof FrameNode)) {
        position++;
      }
    }
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (!(insn instanceof LineNumberNode) && !(insn instanceof FrameNode)
          && !(insn instanceof LabelNode)) {
        out.add(render(insn, labels));
      }
    }
    return out;
  }

  private static String clip(String text) {
    return text.length() > 60 ? text.substring(0, 60) + "…" : text;
  }

  private static int label(LabelNode label, Map<LabelNode, Integer> labels) {
    return labels.getOrDefault(label, -1);
  }

  private static String render(AbstractInsnNode insn, Map<LabelNode, Integer> labels) {
    if (insn instanceof VarInsnNode node) {
      return "var" + node.getOpcode() + " " + node.var;
    }
    if (insn instanceof IntInsnNode node) {
      return "int" + node.getOpcode() + " " + node.operand;
    }
    if (insn instanceof TypeInsnNode node) {
      return "type" + node.getOpcode() + " " + node.desc;
    }
    if (insn instanceof FieldInsnNode node) {
      return "field" + node.getOpcode() + " " + node.owner + "." + node.name + " " + node.desc;
    }
    if (insn instanceof MethodInsnNode node) {
      return "call" + node.getOpcode() + " " + node.owner + "." + node.name + node.desc + (node.itf ? " itf" : "");
    }
    if (insn instanceof InvokeDynamicInsnNode node) {
      return "indy " + node.name + node.desc + " " + node.bsm.getOwner() + "." + node.bsm.getName()
        + node.bsm.getDesc() + " " + renderValue(node.bsmArgs);
    }
    if (insn instanceof JumpInsnNode node) {
      return "jump" + node.getOpcode() + " L" + label(node.label, labels);
    }
    if (insn instanceof LdcInsnNode node) {
      return "ldc " + renderValue(node.cst);
    }
    if (insn instanceof IincInsnNode node) {
      return "iinc " + node.var + " " + node.incr;
    }
    if (insn instanceof TableSwitchInsnNode node) {
      StringBuilder builder = new StringBuilder("tswitch " + label(node.dflt, labels) + " ");
      builder.append(node.min).append(' ').append(node.max);
      for (LabelNode label : node.labels) {
        builder.append(" L").append(label(label, labels));
      }
      return builder.toString();
    }
    if (insn instanceof LookupSwitchInsnNode node) {
      StringBuilder builder = new StringBuilder("lswitch " + label(node.dflt, labels));
      for (int i = 0; i < node.keys.size(); i++) {
        builder.append(' ').append(node.keys.get(i)).append(":L").append(label(node.labels.get(i), labels));
      }
      return builder.toString();
    }
    if (insn instanceof MultiANewArrayInsnNode node) {
      return "multianewarray " + node.desc + " " + node.dims;
    }
    return "op" + insn.getOpcode();
  }

  private static String renderValue(org.objectweb.asm.Handle handle) {
    return handle.getOwner() + "." + handle.getName() + handle.getDesc() + " " + handle.getTag();
  }

  private static String renderValue(Object[] values) {
    StringBuilder builder = new StringBuilder();
    for (Object value : values) {
      builder.append(renderValue(value)).append(',');
    }
    return builder.toString();
  }

  /**
   * The line table as {@code instruction position:line} pairs. The position is what the target's
   * bytecode actually anchors the line at, so an entry with the right line number but a different
   * anchor still differs: the two class files are not the same file.
   */
  static List<String> lnt(MethodNode method) {
    Map<LabelNode, Integer> positions = new HashMap<>();
    int position = 0;
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LabelNode label) {
        positions.putIfAbsent(label, position);
      } else if (!(insn instanceof LineNumberNode) && !(insn instanceof FrameNode)) {
        position++;
      }
    }
    List<String> lines = new ArrayList<>();
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LineNumberNode line) {
        lines.add(positions.getOrDefault(line.start, -1) + ":" + line.line);
      }
    }
    return lines;
  }

  /** Whether the divergence is one offset for the whole method, which a padding pass can solve. */
  private static String lntSummary(List<String> original, List<String> ours) {
    if (original.size() != ours.size()) {
      return "entries " + original.size() + " vs " + ours.size();
    }
    if (original.isEmpty()) {
      return "entries differ";
    }
    int first = lineOf(original, 0) - lineOf(ours, 0);
    boolean constant = true;
    int min = Integer.MAX_VALUE;
    int max = Integer.MIN_VALUE;
    java.util.Set<Integer> distinct = new java.util.TreeSet<>();
    for (int i = 0; i < original.size(); i++) {
      int delta = lineOf(original, i) - lineOf(ours, i);
      distinct.add(delta);
      min = Math.min(min, delta);
      max = Math.max(max, delta);
      if (delta != first) {
        constant = false;
      }
    }
    if (constant) {
      return "constant shift " + first;
    }
    return "deltas " + min + ".." + max + " (" + distinct.size() + " distinct)";
  }

  private static int lineOf(List<String> entries, int index) {
    String entry = entries.get(index);
    return Integer.parseInt(entry.substring(entry.indexOf(':') + 1));
  }

  private static String localRows(MethodNode method) {
    if (method.localVariables == null) {
      return "";
    }
    List<String> entries = new ArrayList<>();
    for (LocalVariableNode local : method.localVariables) {
      entries.add(local.name + "@" + local.index + "[" + local.start.getLabel() + "+" + local.end.getLabel() + "]");
    }
    return entries.toString();
  }

  private static String lvt(MethodNode method) {
    if (method.localVariables == null) {
      return "";
    }
    List<String> entries = new ArrayList<>();
    for (LocalVariableNode local : method.localVariables) {
      entries.add(local.name + " " + local.desc + " " + local.signature + " " + local.index);
    }
    return entries.toString();
  }

  private static String parameters(MethodNode method) {
    if (method.parameters == null) {
      return "";
    }
    List<String> entries = new ArrayList<>();
    for (ParameterNode parameter : method.parameters) {
      entries.add(parameter.name + " " + parameter.access);
    }
    return entries.toString();
  }

  private static String frames(MethodNode method) {
    StringBuilder builder = new StringBuilder();
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof FrameNode frame) {
        builder.append(frame.type).append(' ').append(renderFrame(frame.local)).append('|')
          .append(renderFrame(frame.stack)).append(';');
      }
    }
    return builder.toString();
  }

  private static String renderFrame(List<Object> values) {
    if (values == null) {
      return "-";
    }
    List<String> rendered = new ArrayList<>();
    for (Object value : values) {
      if (value instanceof String text) {
        rendered.add(text);
      } else if (value instanceof Integer tag) {
        rendered.add(tag.toString());
      } else if (value instanceof LabelNode) {
        rendered.add("L");
      } else {
        rendered.add(String.valueOf(value));
      }
    }
    return rendered.toString();
  }
}

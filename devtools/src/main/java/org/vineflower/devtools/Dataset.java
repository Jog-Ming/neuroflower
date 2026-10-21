package org.vineflower.devtools;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;

import java.io.BufferedWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * Exports per-instruction alignment data for the line-break model. For every method whose
 * instructions match the original, one JSON line records each instruction's operand and the source
 * line both sides attribute to it. The model learns which instruction should start a new source line;
 * at repair time only the target's line numbers are available, never the target source.
 */
public final class Dataset {
  public record Result(int files, long methods, int millis) {
  }

  private Dataset() {
  }

  public static Result write(Path tree, Path originalClasses, List<Path> classpath, int release,
                             String only, int threads, Path out) throws Exception {
    Files.createDirectories(out.getParent());
    List<Path> sources = Verifier.sources(tree, only);
    ExecutorService pool = Executors.newFixedThreadPool(Math.max(1, threads));
    List<Callable<List<JsonObject>>> tasks = new ArrayList<>();
    for (Path source : sources) {
      tasks.add(() -> entries(tree, source, originalClasses, classpath, release));
    }
    long started = System.nanoTime();
    long methods = 0;
    try (BufferedWriter writer = Files.newBufferedWriter(out, StandardCharsets.UTF_8)) {
      for (Future<List<JsonObject>> future : pool.invokeAll(tasks)) {
        for (JsonObject entry : future.get()) {
          writer.write(Workspace.COMPACT.toJson(entry));
          writer.write('\n');
          methods++;
        }
      }
    } finally {
      pool.shutdown();
    }
    return new Result(sources.size(), methods, (int) ((System.nanoTime() - started) / 1_000_000));
  }

  private static List<JsonObject> entries(Path tree, Path source, Path originalClasses,
                                          List<Path> classpath, int release) throws Exception {
    List<JsonObject> entries = new ArrayList<>();
    Verifier.Compiled compiled = Verifier.compile(source, classpath, release);
    if (!compiled.ok()) {
      return entries;
    }
    String relative = tree.toAbsolutePath().normalize()
      .relativize(source.toAbsolutePath().normalize()).toString().replace('\\', '/');
    for (Map.Entry<String, byte[]> entry : compiled.outputs().entrySet()) {
      Path original = originalClasses.resolve(entry.getKey().replace('.', '/') + ".class");
      if (!Files.exists(original)) {
        continue;
      }
      byte[] originalBytes = Files.readAllBytes(original);
      ClassDiff diff = ClassDiff.compare(originalBytes, entry.getValue());
      if (!diff.matches.get("code")) {
        continue;
      }
      ClassNode theirs = ClassDiff.parse(originalBytes);
      ClassNode ours = ClassDiff.parse(entry.getValue());
      Map<String, MethodNode> theirMethods = byKey(theirs.methods);
      Map<String, MethodNode> ourMethods = byKey(ours.methods);
      for (Map.Entry<String, MethodNode> method : theirMethods.entrySet()) {
        MethodNode ourMethod = ourMethods.get(method.getKey());
        if (ourMethod == null) {
          continue;
        }
        List<Integer> theirLines = lines(method.getValue());
        List<Integer> ourLines = lines(ourMethod);
        List<String> operands = operands(ourMethod);
        if (theirLines.size() != ourLines.size() || operands.size() != ourLines.size()) {
          continue;
        }
        JsonObject json = new JsonObject();
        json.addProperty("class", diff.name);
        json.addProperty("method", method.getKey());
        json.addProperty("source", relative);
        addInts(json, "ours", ourLines);
        addInts(json, "target", theirLines);
        JsonArray ops = new JsonArray();
        operands.forEach(ops::add);
        json.add("ops", ops);
        entries.add(json);
      }
    }
    return entries;
  }

  private static void addInts(JsonObject json, String key, List<Integer> values) {
    JsonArray array = new JsonArray();
    values.forEach(array::add);
    json.add(key, array);
  }

  private static Map<String, MethodNode> byKey(List<MethodNode> methods) {
    Map<String, MethodNode> map = new LinkedHashMap<>();
    for (MethodNode method : methods) {
      map.put(method.name + method.desc, method);
    }
    return map;
  }

  /** The target line in force at each real instruction. */
  private static List<Integer> lines(MethodNode method) {
    List<Integer> lines = new ArrayList<>();
    int current = -1;
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LineNumberNode line) {
        current = line.line;
      } else if (!(insn instanceof LabelNode) && !(insn instanceof FrameNode)) {
        lines.add(current);
      }
    }
    return lines;
  }

  private static List<String> operands(MethodNode method) {
    List<String> operands = new ArrayList<>();
    for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn = insn.getNext()) {
      if (insn instanceof LabelNode || insn instanceof LineNumberNode || insn instanceof FrameNode) {
        continue;
      }
      operands.add(operand(insn));
    }
    return operands;
  }

  private static String operand(AbstractInsnNode insn) {
    if (insn instanceof MethodInsnNode method) {
      return method.name;
    }
    if (insn instanceof FieldInsnNode field) {
      return field.name;
    }
    if (insn instanceof TypeInsnNode type) {
      String value = type.desc;
      int slash = value.lastIndexOf('/');
      return "type:" + (slash < 0 ? value : value.substring(slash + 1));
    }
    if (insn instanceof LdcInsnNode ldc) {
      return "const:" + ldc.cst;
    }
    if (insn instanceof InvokeDynamicInsnNode indy) {
      return "indy:" + indy.name;
    }
    return "op:" + insn.getOpcode();
  }
}

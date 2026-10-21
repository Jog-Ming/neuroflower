package org.vineflower.devtools;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

/**
 * Runs the decompiler over a version's jar, or over one class and its nested classes.
 *
 * A tree is cached by the hash of the input jar, the hash of the decompiler jar and the option
 * string: rebuild the fork and the next run decompiles again, change nothing and it is reused. The
 * newest few trees are kept and the rest pruned automatically.
 */
public final class Decompiler {
  private final Workspace workspace;
  private final Minecraft minecraft;

  public Decompiler(Workspace workspace, Minecraft minecraft) {
    this.workspace = workspace;
    this.minecraft = minecraft;
  }

  /** Trees kept per version; older ones are pruned after each decompile. */
  private static final int KEEP = 5;

  public Path tree(String version, int threads, boolean noCache, String only,
                   List<String> options) throws Exception {
    Path devJar = workspace.devJar();
    if (!Files.exists(devJar)) {
      throw new IllegalStateException("decompiler jar missing: " + devJar + " (run ./gradlew :allJar)");
    }
    // --refresh re-decompiles the cached jar; it does not re-download what is already here.
    Path client = minecraft.clientJar(version, false);
    List<Path> classpath = minecraft.classpath(version, false);
    String optionKey = options.isEmpty() ? "baked-defaults" : String.join(" ", options);
    String key = Workspace.sha256(Workspace.sha256(client) + Workspace.sha256(devJar) + optionKey
      + classpathFingerprint(classpath) + (only == null ? "" : "|only=" + only));
    Path dir = workspace.trees.resolve(key);
    Path src = dir.resolve("src");
    JsonObject meta = Files.exists(dir.resolve("meta.json"))
      ? Workspace.readJson(dir.resolve("meta.json")) : new JsonObject();

    if (!noCache && Files.isDirectory(src)) {
      meta.addProperty("lastUsed", System.currentTimeMillis());
      Workspace.writeJson(dir.resolve("meta.json"), meta);
      prune();
      return src;
    }

    Path input = client;
    if (only != null) {
      input = subsetJar(version, only);
    }

    Files.createDirectories(src);
    List<String> command = new ArrayList<>();
    command.add(javaCommand());
    command.add("-Xmx4g");
    command.add("-jar");
    command.add(devJar.toString());
    command.add("--thread-count=" + threads);
    command.addAll(options);
    command.add("-e=" + join(classpath));
    command.add(input.toString());
    command.add(src.toString());
    long started = System.nanoTime();
    Process process = new ProcessBuilder(command).inheritIO().start();
    int status = process.waitFor();
    long elapsed = (System.nanoTime() - started) / 1_000_000;
    if (status != 0) {
      throw new IOException("decompiler exited with " + status);
    }

    meta = new JsonObject();
    meta.addProperty("version", version);
    meta.addProperty("key", key);
    meta.addProperty("clientJar", client.toString());
    meta.addProperty("clientJarSha256", Workspace.sha256(client));
    meta.addProperty("decompilerJar", devJar.toString());
    meta.addProperty("decompilerJarSha256", Workspace.sha256(devJar));
    meta.addProperty("options", optionKey);
    if (only != null) {
      meta.addProperty("only", only);
    }
    meta.addProperty("createdAt", System.currentTimeMillis());
    meta.addProperty("lastUsed", System.currentTimeMillis());
    meta.addProperty("decompileMillis", elapsed);
    long[] stats = treeStats(src);
    meta.addProperty("sourceFiles", stats[0]);
    meta.addProperty("bytes", stats[1]);
    Workspace.writeJson(dir.resolve("meta.json"), meta);
    prune();
    return src;
  }

  /** The classpath is part of the decompiler's input: missing libraries change its inference. */
  private static String classpathFingerprint(List<Path> classpath) {
    StringBuilder builder = new StringBuilder();
    for (Path path : classpath) {
      try {
        builder.append(path.getFileName()).append(':').append(Files.size(path)).append(';');
      } catch (IOException ignored) {
        builder.append(path.getFileName()).append(":?;");
      }
    }
    return Workspace.sha256(builder.toString());
  }

  /** Files and bytes of a decompiled tree, in one directory walk (file attributes come with it). */
  private static long[] treeStats(Path root) throws IOException {
    long[] total = new long[2];
    Files.walkFileTree(root, new java.nio.file.SimpleFileVisitor<>() {
      @Override
      public java.nio.file.FileVisitResult visitFile(Path file,
          java.nio.file.attribute.BasicFileAttributes attrs) {
        total[0]++;
        total[1] += attrs.size();
        return java.nio.file.FileVisitResult.CONTINUE;
      }

      @Override
      public java.nio.file.FileVisitResult visitFileFailed(Path file, IOException exc) {
        return java.nio.file.FileVisitResult.CONTINUE;
      }
    });
    return total;
  }

  /** A jar with the class and everything named Class$..., so nested and anonymous classes come too. */
  private Path subsetJar(String version, String binaryName) throws Exception {
    Path client = minecraft.clientJar(version, false);
    String entryName = binaryName.replace('.', '/') + ".class";
    Path jar = workspace.tmp.resolve("subset-" + Workspace.sha256(version + "|" + binaryName) + ".jar");
    Files.createDirectories(jar.getParent());
    try (ZipFile zip = new ZipFile(client.toFile());
         ZipOutputStream out = new ZipOutputStream(Files.newOutputStream(jar))) {
      String prefix = entryName.substring(0, entryName.length() - ".class".length());
      boolean found = false;
      for (ZipEntry entry : java.util.Collections.list(zip.entries())) {
        String name = entry.getName();
        if (name.equals(entryName) || name.startsWith(prefix + "$")) {
          found = true;
          out.putNextEntry(new ZipEntry(name));
          try (var in = zip.getInputStream(entry)) {
            in.transferTo(out);
          }
          out.closeEntry();
        }
      }
      if (!found) {
        throw new IllegalArgumentException("class " + binaryName + " is not in " + client.getFileName());
      }
    }
    return jar;
  }

  /** Deletes the oldest cached trees, keeping {@link #KEEP} per version. */
  public void prune() throws IOException {
    if (!Files.isDirectory(workspace.trees)) {
      return;
    }
    record Tree(Path dir, long used) {
    }
    Map<String, List<Tree>> byVersion = new java.util.LinkedHashMap<>();
    try (var list = Files.list(workspace.trees)) {
      for (Path dir : list.toList()) {
        long used = 0;
        String version = "unknown";
        Path meta = dir.resolve("meta.json");
        if (Files.exists(meta)) {
          try {
            var json = Workspace.readJson(meta);
            used = json.get("lastUsed").getAsLong();
            if (json.has("version")) {
              version = json.get("version").getAsString();
            }
          } catch (RuntimeException ignored) {
            // A tree without a readable meta is treated as oldest.
          }
        }
        byVersion.computeIfAbsent(version, k -> new ArrayList<>()).add(new Tree(dir, used));
      }
    }
    for (List<Tree> trees : byVersion.values()) {
      trees.sort(Comparator.comparingLong(Tree::used).reversed());
      for (int i = KEEP; i < trees.size(); i++) {
        delete(trees.get(i).dir());
      }
    }
  }

  static void delete(Path dir) throws IOException {
    if (!Files.exists(dir)) {
      return;
    }
    try (var walk = Files.walk(dir)) {
      for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
        Files.deleteIfExists(path);
      }
    }
  }

  private static String javaCommand() {
    String home = System.getProperty("java.home");
    return Path.of(home, "bin", isWindows() ? "java.exe" : "java").toString();
  }

  private static boolean isWindows() {
    return System.getProperty("os.name").toLowerCase().contains("win");
  }

  private static String join(List<Path> paths) {
    StringBuilder builder = new StringBuilder();
    for (Path path : paths) {
      if (builder.length() > 0) {
        builder.append(',');
      }
      builder.append(path);
    }
    return builder.toString();
  }
}

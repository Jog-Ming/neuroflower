package org.vineflower.devtools;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
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
  /** Everything the fork bakes into its defaults; only the version and thread count matter here. */
  public static final String OPTIONS = "baked-defaults";

  private final Workspace workspace;
  private final Minecraft minecraft;

  public Decompiler(Workspace workspace, Minecraft minecraft) {
    this.workspace = workspace;
    this.minecraft = minecraft;
  }

  public Path tree(String version, int threads, boolean refresh, String only, int keep) throws Exception {
    Path devJar = workspace.devJar();
    if (!Files.exists(devJar)) {
      throw new IllegalStateException("decompiler jar missing: " + devJar + " (run ./gradlew :allJar)");
    }
    Path client = minecraft.clientJar(version, refresh);
    List<Path> classpath = minecraft.classpath(version, refresh);
    String key = Workspace.sha256(Workspace.sha256(client) + Workspace.sha256(devJar) + OPTIONS
      + classpathFingerprint(classpath) + (only == null ? "" : "|only=" + only));
    Path dir = workspace.trees.resolve(key);
    Path src = dir.resolve("src");
    JsonObject meta = Files.exists(dir.resolve("meta.json"))
      ? Workspace.readJson(dir.resolve("meta.json")) : new JsonObject();

    if (!refresh && Files.isDirectory(src)) {
      meta.addProperty("lastUsed", System.currentTimeMillis());
      Workspace.writeJson(dir.resolve("meta.json"), meta);
      prune(keep);
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
    meta.addProperty("options", OPTIONS);
    if (only != null) {
      meta.addProperty("only", only);
    }
    meta.addProperty("createdAt", System.currentTimeMillis());
    meta.addProperty("lastUsed", System.currentTimeMillis());
    meta.addProperty("decompileMillis", elapsed);
    meta.addProperty("sourceFiles", countJava(src));
    Workspace.writeJson(dir.resolve("meta.json"), meta);
    prune(keep);
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

  private static long countJava(Path root) throws IOException {
    try (var walk = Files.walk(root)) {
      return walk.filter(p -> p.toString().endsWith(".java")).count();
    }
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

  public Path subsetSource(String version, String binaryName, int threads) throws Exception {
    Path tree = tree(version, threads, false, binaryName, 2);
    String relative = binaryName.replace('.', '/') + ".java";
    Path source = tree.resolve(relative);
    if (!Files.exists(source)) {
      // Nested classes live in the outer class's file; find the file that holds the outer.
      String outer = binaryName.contains("$") ? binaryName.substring(0, binaryName.indexOf('$')) : binaryName;
      Path outerSource = tree.resolve(outer.replace('.', '/') + ".java");
      if (Files.exists(outerSource)) {
        return outerSource;
      }
      throw new IllegalStateException("no source for " + binaryName + " under " + tree);
    }
    return source;
  }

  /** Deletes the oldest cached trees, keeping the newest {@code keep}. */
  public void prune(int keep) throws IOException {
    if (!Files.isDirectory(workspace.trees)) {
      return;
    }
    record Tree(Path dir, long used) {
    }
    List<Tree> trees = new ArrayList<>();
    try (var list = Files.list(workspace.trees)) {
      for (Path dir : list.toList()) {
        long used = 0;
        Path meta = dir.resolve("meta.json");
        if (Files.exists(meta)) {
          try {
            used = Workspace.readJson(meta).get("lastUsed").getAsLong();
          } catch (RuntimeException ignored) {
            // A tree without a readable meta is treated as oldest.
          }
        }
        trees.add(new Tree(dir, used));
      }
    }
    trees.sort(Comparator.comparingLong(Tree::used).reversed());
    for (int i = keep; i < trees.size(); i++) {
      delete(trees.get(i).dir());
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

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
  /** How long one decompiler run may take before it is killed; a hang must never cost a whole run. */
  private int timeoutMinutes = 30;

  public Decompiler timeoutMinutes(int minutes) {
    this.timeoutMinutes = Math.max(1, minutes);
    return this;
  }
  private final Workspace workspace;
  private final Minecraft minecraft;

  public Decompiler(Workspace workspace, Minecraft minecraft) {
    this.workspace = workspace;
    this.minecraft = minecraft;
  }

  /** Trees kept per version; older ones are pruned after each decompile. */
  private static final int KEEP = 5;
  /** A tree used this recently may belong to a score running in another process. */
  private static final long PRUNE_GRACE_MILLIS = 10 * 60 * 1000L;
  /** What the decompiler prints where a method could not be decompiled. */
  private static final String FAILED_MARKER = "$VF: Couldn't be decompiled";

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

    // The decompiler writes into a staging directory that only becomes the cached tree once it
    // finishes: a killed run must not leave a half tree that a later run would treat as complete.
    Path staging = dir.resolve("src.part");
    deleteTree(staging);
    Files.createDirectories(staging);
    List<String> command = new ArrayList<>();
    command.add(javaCommand());
    command.add("-Xmx4g");
    command.add("-jar");
    command.add(devJar.toString());
    command.add("--thread-count=" + threads);
    command.addAll(options);
    command.add("-e=" + join(classpath));
    command.add(input.toString());
    command.add(staging.toString());
    long started = System.nanoTime();
    runDecompiler(command, staging, timeoutMinutes);
    // A method the decompiler fails on is printed as a stub that cannot compile. Such a run is
    // occasionally produced where the same jar decompiles cleanly -- thread scheduling decides an
    // internal order -- and caching it would make every later score inherit the failure. Retry
    // once and keep the tree with fewer failed methods.
    int failed = countFailedMethods(staging);
    if (failed > 0) {
      Path retry = dir.resolve("src.retry");
      deleteTree(retry);
      Files.createDirectories(retry);
      List<String> retryCommand = new ArrayList<>(command);
      retryCommand.set(retryCommand.size() - 1, retry.toString());
      runDecompiler(retryCommand, retry, timeoutMinutes);
      int retried = countFailedMethods(retry);
      if (retried < failed) {
        deleteTree(staging);
        Files.move(retry, staging);
        failed = retried;
      }
      else {
        deleteTree(retry);
      }
      System.err.println("decompiler failed on " + failed + " method(s) after retry; kept the better run");
    }
    long elapsed = (System.nanoTime() - started) / 1_000_000;
    // A --no-cache run replaces an earlier tree of the same key; the old directory must go
    // before the staging one can take its name.
    deleteTree(src);
    try {
      Files.move(staging, src, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
    } catch (java.nio.file.AtomicMoveNotSupportedException | java.nio.file.FileAlreadyExistsException e) {
      Files.move(staging, src);
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

  private static void deleteTree(Path path) throws IOException {
    if (!Files.exists(path)) {
      return;
    }
    try (java.util.stream.Stream<Path> walk = Files.walk(path)) {
      for (Path entry : walk.sorted(java.util.Comparator.reverseOrder()).toList()) {
        Files.deleteIfExists(entry);
      }
    }
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

  /** Runs the decompiler over one input into {@code out}, with the per-version timeout. */
  private static void runDecompiler(List<String> command, Path out, int timeoutMinutes) throws IOException {
    Process process = new ProcessBuilder(command).inheritIO().start();
    boolean finished;
    try {
      finished = process.waitFor(timeoutMinutes, java.util.concurrent.TimeUnit.MINUTES);
    }
    catch (InterruptedException e) {
      process.destroyForcibly();
      Thread.currentThread().interrupt();
      deleteTree(out);
      throw new IOException("decompiler interrupted", e);
    }
    if (!finished) {
      process.destroyForcibly();
      try {
        process.waitFor();
      }
      catch (InterruptedException e) {
        Thread.currentThread().interrupt();
      }
      deleteTree(out);
      throw new IOException("decompiler timed out after " + timeoutMinutes + " minutes");
    }
    int status = process.exitValue();
    if (status != 0) {
      deleteTree(out);
      throw new IOException("decompiler exited with " + status);
    }
  }

  /** Methods the decompiler gave up on, printed as stubs no compiler accepts. */
  private static int countFailedMethods(Path root) throws IOException {
    if (!Files.isDirectory(root)) {
      return 0;
    }
    int failed = 0;
    try (java.util.stream.Stream<Path> walk = Files.walk(root)) {
      for (Path file : walk.filter(f -> f.toString().endsWith(".java")).toList()) {
        String text = Files.readString(file);
        for (int at = text.indexOf(FAILED_MARKER); at >= 0; at = text.indexOf(FAILED_MARKER, at + 1)) {
          failed++;
        }
      }
    }
    return failed;
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
  public void prune() {
    if (!Files.isDirectory(workspace.trees)) {
      return;
    }
    // Several versions are scored concurrently, each in its own process, and every one of them
    // prunes. The lock makes the scan and the deletes one critical section; a process that finds
    // it held simply leaves the cache alone.
    Path lockPath = workspace.trees.resolve(".prune.lock");
    try (java.nio.channels.FileChannel channel = java.nio.channels.FileChannel.open(lockPath,
        java.nio.file.StandardOpenOption.CREATE, java.nio.file.StandardOpenOption.WRITE)) {
      java.nio.channels.FileLock lock = channel.tryLock();
      if (lock == null) {
        return;
      }
      try {
        pruneLocked();
      } finally {
        lock.release();
      }
    } catch (IOException | RuntimeException e) {
      // Trimming the cache is an optimisation; it must never fail a decompile or a score.
    }
  }

  private void pruneLocked() throws IOException {
    record Tree(Path dir, long used) {
    }
    long now = System.currentTimeMillis();
    Map<String, List<Tree>> byVersion = new java.util.LinkedHashMap<>();
    try (var list = Files.list(workspace.trees)) {
      for (Path dir : list.toList()) {
        if (!Files.isDirectory(dir)) {
          continue; // the lock file and deletion tombstones live here too
        }
        Path meta = dir.resolve("meta.json");
        if (!Files.exists(meta)) {
          // A tree is moved into place before its meta is written. Another process can see that
          // window, and a tree it cannot identify is not its to delete.
          continue;
        }
        long used;
        String version;
        try {
          var json = Workspace.readJson(meta);
          used = json.get("lastUsed").getAsLong();
          version = json.has("version") ? json.get("version").getAsString() : null;
        } catch (IOException | RuntimeException e) {
          continue; // a meta being written is not evidence that the tree is old
        }
        if (version == null) {
          continue;
        }
        byVersion.computeIfAbsent(version, k -> new ArrayList<>()).add(new Tree(dir, used));
      }
    }
    for (List<Tree> trees : byVersion.values()) {
      trees.sort(Comparator.comparingLong(Tree::used).reversed());
      for (int i = KEEP; i < trees.size(); i++) {
        if (now - trees.get(i).used() < PRUNE_GRACE_MILLIS) {
          continue; // another process may be scoring this tree right now
        }
        delete(trees.get(i).dir());
      }
    }
  }

  /**
   * Removes a tree by first renaming it away, so a scorer still walking the old path cannot add
   * files behind the deletion; failure to remove it is ignored for the same reason.
   */
  static void delete(Path dir) {
    if (!Files.exists(dir)) {
      return;
    }
    Path tombstone = dir.resolveSibling(dir.getFileName() + ".delete-"
      + java.util.UUID.randomUUID().toString().replace("-", ""));
    try {
      Files.move(dir, tombstone, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
    } catch (IOException e) {
      try {
        Files.move(dir, tombstone);
      } catch (IOException again) {
        return; // in use: leave it for a later prune
      }
    }
    try (var walk = Files.walk(tombstone)) {
      for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
        try {
          Files.deleteIfExists(path);
        } catch (IOException ignored) {
          // a concurrent writer won this file; the tombstone is retried by a later prune
        }
      }
    } catch (IOException ignored) {
      // leftovers stay in the tombstone and are invisible to the cache lookup
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

package org.vineflower.devtools;

import java.util.concurrent.TimeUnit;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * The experimental pipeline's entry point. See devtools/cli for the wrapper.
 *
 * <pre>
 *   versions [--no-cache]
 *   decompile &lt;version&gt; [--no-cache] [--threads N] [--only Class] [--options "..."]
 *   tree      &lt;version&gt; [--only Class]
 *   score     &lt;version&gt; [&lt;version&gt;...] [--no-cache] [--only Class] [--threads N] [--json] [--jobs N]
 *   compile   &lt;version&gt; &lt;Class&gt;
 *   corpus    &lt;version&gt; --ground-truth &lt;dir&gt;
 *   dataset   &lt;version&gt;
 *   clean     [--trees] [--compile] [--downloads] [--all]
 *   reports   [--version V] [--limit N]
 *   cache
 * </pre>
 */
public final class Main {
  public static void main(String[] args) throws Exception {
    if (args.length == 0) {
      usage();
      return;
    }
    Workspace workspace = Workspace.load();
    Minecraft minecraft = new Minecraft(workspace);
    Decompiler decompiler = new Decompiler(workspace, minecraft)
      .timeoutMinutes(intFlag(List.of(args), "--timeout", 15));
    String command = args[0];
    List<String> rest = List.of(args).subList(1, args.length);

    if (rest.contains("--refresh")) {
      throw new IllegalArgumentException("--refresh was renamed to --no-cache");
    }

    if (needsTargetJdk(command)) {
      List<String> targets = positionals(rest);
      if (targets.size() == 1) {
        ensureTargetJdk(minecraft, targets.get(0), args);
      }
    }

    switch (command) {
      case "versions" -> {
        boolean noCache = rest.contains("--no-cache");
        for (String id : minecraft.versionIds(noCache)) {
          System.out.println(id);
        }
      }
      case "decompile" -> {
        String version = positional(rest);
        int threads = intFlag(rest, "--threads", Math.max(1, Runtime.getRuntime().availableProcessors()));
        String only = stringFlag(rest, "--only", null);
        boolean noCache = rest.contains("--no-cache");
        Path tree = decompiler.tree(version, threads, noCache, only, optionsFlag(rest));
        System.out.println(tree);
      }
      case "tree" -> {
        String version = positional(rest);
        String only = stringFlag(rest, "--only", null);
        System.out.println(decompiler.tree(version, threadsDefault(), false, only, optionsFlag(rest)));
      }
      case "score" -> {
        List<String> versions = positionals(rest);
        if (versions.isEmpty()) {
          throw new IllegalArgumentException("missing version");
        }
        if (versions.size() > 1) {
          scoreMany(workspace, versions, rest);
        } else {
          String version = versions.get(0);
          boolean noCache = rest.contains("--no-cache");
          String only = stringFlag(rest, "--only", null);
          int threads = intFlag(rest, "--threads", threadsDefault());
          boolean json = rest.contains("--json");
          Path tree = decompiler.tree(version, threads, noCache, only, optionsFlag(rest));
          new Verifier(workspace, minecraft).score(version, tree, only, threads, json);
        }
      }
      case "compile" -> {
        List<String> positional = positionals(rest);
        if (positional.size() < 2) {
          throw new IllegalArgumentException("usage: compile <version> <Class> [--no-cache] [--options \"...\"]");
        }
        String version = positional.get(0);
        String className = positional.get(1);
        boolean noCache = rest.contains("--no-cache");
        Path tree = decompiler.tree(version, threadsDefault(), noCache, className, optionsFlag(rest));
        List<Path> sources = Verifier.sources(tree, className);
        if (sources.isEmpty()) {
          throw new IllegalArgumentException("no source for " + className + " under " + tree);
        }
        List<Path> classpath = minecraft.classpath(version, false);
        int release = Verifier.releaseOf(minecraft.clientJar(version, false));
        boolean ok = true;
        for (Path source : sources) {
          List<Verifier.Problem> problems = Verifier.diagnose(source, classpath, release);
          for (Verifier.Problem problem : problems) {
            System.out.printf(Locale.ROOT, "%s:%d:%d: %s%n", tree.relativize(source),
              problem.line(), problem.column(), problem.message());
          }
          System.out.printf(Locale.ROOT, "%s %s%n", problems.isEmpty() ? "compiled" : "failed",
            tree.relativize(source));
          ok &= problems.isEmpty();
        }
        if (!ok) {
          System.exit(1);
        }
      }
      case "dataset" -> {
        String version = positional(rest);
        String only = stringFlag(rest, "--only", null);
        int threads = intFlag(rest, "--threads", threadsDefault());
        Path tree = decompiler.tree(version, threads, false, only, List.of());
        List<Path> classpath = minecraft.classpath(version, false);
        int release = Verifier.releaseOf(minecraft.clientJar(version, false));
        Path out = workspace.dev.resolve("datasets").resolve(version + "-methods.jsonl");
        Dataset.Result result = Dataset.write(tree, minecraft.extractedClasses(version, false),
          classpath, release, only, threads, out);
        System.out.printf(java.util.Locale.ROOT,
          "methods %d from %d files in %.1fs -> %s%n", result.methods(), result.files(),
          result.millis() / 1000.0, out);
      }
      case "corpus" -> {
        String version = positional(rest);
        String groundTruth = stringFlag(rest, "--ground-truth", null);
        if (groundTruth == null) {
          throw new IllegalArgumentException("corpus needs --ground-truth <minecraft source tree>");
        }
        String only = stringFlag(rest, "--only", null);
        int threads = intFlag(rest, "--threads", threadsDefault());
        Path tree = decompiler.tree(version, threads, false, only, List.of());
        List<Verifier.FileResult> results =
          new Verifier(workspace, minecraft).score(version, tree, only, threads, false);
        Path manifest = Corpus.write(workspace.dev.resolve("corpus"), version, tree,
          Path.of(groundTruth), results);
        System.out.println(manifest);
      }
      case "reports" -> reports(workspace, rest);
      case "clean" -> clean(workspace, rest);
      case "cache" -> cache(workspace, rest);
      default -> usage();
    }
  }

  /**
   * Scores several versions concurrently, one child process per version: their trees, verifier
   * heaps and decompiler processes are independent. Threads are split across the jobs, so the
   * machine is not oversubscribed. Logs: {@code .dev/tmp/score-<version>.out}.
   */
  private static void scoreMany(Workspace workspace, List<String> versions, List<String> rest)
      throws Exception {
    if (stringFlag(rest, "--only", null) != null) {
      throw new IllegalArgumentException("--only needs a single version");
    }
    if (new java.util.HashSet<>(versions).size() != versions.size()) {
      throw new IllegalArgumentException("duplicate version in " + versions);
    }
    int jobs = Math.max(1, Math.min(versions.size(), intFlag(rest, "--jobs", 2)));
    int timeout = intFlag(rest, "--timeout", 15);
    int threads = intFlag(rest, "--threads",
      Math.max(1, Runtime.getRuntime().availableProcessors() / jobs));
    boolean noCache = rest.contains("--no-cache");
    Path jar = Path.of(Main.class.getProtectionDomain().getCodeSource().getLocation().toURI());
    Path java = Path.of(System.getProperty("java.home"), "bin", isWindows() ? "java.exe" : "java");
    Files.createDirectories(workspace.tmp);
    System.out.printf(Locale.ROOT, "scoring %d versions, %d at a time, %d threads each%n",
      versions.size(), jobs, threads);

    ExecutorService pool = Executors.newFixedThreadPool(jobs);
    List<Future<String>> futures = new ArrayList<>();
    long started = System.nanoTime();
    try {
      for (String version : versions) {
        futures.add(pool.submit(() -> {
          Path log = workspace.tmp.resolve("score-" + version + ".out");
          List<String> command = new ArrayList<>(List.of(java.toString(), "-jar", jar.toString(),
            "score", version, "--threads", Integer.toString(threads), "--json",
            "--timeout", Integer.toString(timeout)));
          if (noCache) {
            command.add("--no-cache");
          }
          long begin = System.nanoTime();
          Process process = new ProcessBuilder(command)
            .redirectErrorStream(true)
            .redirectOutput(log.toFile())
            .start();
          boolean finished = process.waitFor(timeout, TimeUnit.MINUTES);
          long seconds = (System.nanoTime() - begin) / 1_000_000_000L;
          if (!finished) {
            process.destroyForcibly();
            process.waitFor();
            return version + "\tfailed (timed out after " + timeout + "m)\t" + seconds + "s";
          }
          int status = process.exitValue();
          return version + "\t" + (status == 0 ? summaryOf(log) : "failed (exit " + status + ")")
            + "\t" + seconds + "s";
        }));
      }
      int failures = 0;
      for (int i = 0; i < futures.size(); i++) {
        String line;
        try {
          line = futures.get(i).get();
        } catch (ExecutionException e) {
          line = versions.get(i) + "\tfailed: " + e.getCause().getMessage() + "\t";
        }
        System.out.println(line);
        if (line.contains("failed")) {
          failures++;
        }
      }
      System.out.printf(Locale.ROOT, "total %ds; logs in %s%n",
        (System.nanoTime() - started) / 1_000_000_000L, workspace.tmp);
      if (failures > 0) {
        throw new IllegalStateException(failures + " version(s) failed");
      }
    } finally {
      pool.shutdownNow();
    }
  }

  private static String summaryOf(Path log) {
    try {
      for (String line : Files.readAllLines(log, StandardCharsets.UTF_8)) {
        if (line.startsWith("sources ")) {
          return line;
        }
      }
    } catch (IOException ignored) {
      // an unreadable log is reported as a missing summary by the caller
    }
    return "no summary";
  }

  /** The append-only run index: one line per score, so history never has to be guessed from names. */
  private static void reports(Workspace workspace, List<String> flags) throws Exception {
    Path index = workspace.reports.resolve("index.tsv");
    if (!Files.exists(index)) {
      System.out.println("no reports yet");
      return;
    }
    List<String> lines = Files.readAllLines(index);
    String version = stringFlag(flags, "--version", null);
    int limit = intFlag(flags, "--limit", 20);
    if (lines.isEmpty()) {
      System.out.println("no reports yet");
      return;
    }
    System.out.println(lines.get(0));
    List<String> body = lines.subList(1, lines.size());
    if (version != null) {
      body = body.stream().filter(line -> line.split("	")[1].equals(version)).toList();
    }
    for (int i = Math.max(0, body.size() - limit); i < body.size(); i++) {
      System.out.println(body.get(i));
    }
  }

  private static void clean(Workspace workspace, List<String> flags) throws Exception {
    boolean all = flags.contains("--all");
    boolean downloads = flags.contains("--downloads") || all;
    boolean compile = flags.contains("--compile") || (!flags.contains("--trees") && !downloads && !all);
    boolean trees = flags.contains("--trees") || (!downloads && !all);
    
    if (all) {
      Decompiler.delete(workspace.dev);
      System.out.println("removed " + workspace.dev);
      return;
    }
    if (trees) {
      new Decompiler(workspace, new Minecraft(workspace)).prune();
      System.out.println("pruned trees");
    }
    if (compile) {
      Decompiler.delete(workspace.cache.resolve("compile"));
      Decompiler.delete(workspace.cache.resolve("classes"));
      System.out.println("removed compile cache");
    }
    if (downloads) {
      Decompiler.delete(workspace.versions);
      System.out.println("removed " + workspace.versions);
    }
  }

  private static void cache(Workspace workspace, List<String> rest) throws Exception {
    boolean measure = rest.contains("--measure");
    System.out.println("cache root: " + workspace.cache);
    long[] versions = versionUsage(workspace.versions, measure);
    long[] compile = usage(workspace.cache.resolve("compile"));
    long[] classes = usage(workspace.cache.resolve("classes"));
    long[] trees = treeUsage(workspace.trees, measure);
    System.out.println("versions: " + versions[0] + " files, " + human(versions[1]));
    System.out.println("compile: " + compile[0] + " files, " + human(compile[1]));
    System.out.println("classes: " + classes[0] + " files, " + human(classes[1]));
    System.out.println("trees: " + trees[0] + " (" + human(trees[1])
      + (trees[2] > 0 ? ", " + trees[2] + " unmeasured; run cache --measure" : "") + ")");
    System.out.println("total: " + human(versions[1] + compile[1] + classes[1] + trees[1])
      + (trees[2] > 0 ? " (measured part)" : ""));
  }

  /**
   * A version's extracted class files are counted when they are unpacked ({@code .stats.json});
   * only the rest of the version directory (jars, libraries) is walked. --measure backfills the
   * versions extracted before that.
   */
  private static long[] versionUsage(Path versions, boolean measure) throws IOException {
    if (!Files.isDirectory(versions)) {
      return new long[]{0, 0};
    }
    long files = 0;
    long bytes = 0;
    List<Path> children = new ArrayList<>();
    try (var list = Files.list(versions)) {
      list.forEach(children::add);
    }
    for (Path version : children) {
      Path classes = version.resolve("classes");
      Path statsFile = classes.resolve(".stats.json");
      long[] known = null;
      if (Files.exists(statsFile)) {
        try {
          var json = Workspace.readJson(statsFile);
          known = new long[]{json.get("classes").getAsLong(), json.get("bytes").getAsLong()};
        } catch (Exception ignored) {
          // a damaged stats file is treated like a missing one
        }
      }
      if (known != null) {
        long[] rest = walkExcept(version, classes);
        // The classes subtree also holds the bookkeeping files; count them so the reported size
        // matches a plain walk and does not change when .stats.json is written.
        long extraFiles = 0;
        long extraBytes = 0;
        for (String name : new String[]{".stats.json", ".stamp"}) {
          Path file = classes.resolve(name);
          if (Files.isRegularFile(file)) {
            extraFiles++;
            extraBytes += Files.size(file);
          }
        }
        files += known[0] + extraFiles + rest[0];
        bytes += known[1] + extraBytes + rest[1];
      } else {
        long[] all = walk(version);
        files += all[0];
        bytes += all[1];
        if (measure && Files.isDirectory(classes)) {
          long[] counted = walk(classes);
          var json = new com.google.gson.JsonObject();
          json.addProperty("classes", counted[0]);
          json.addProperty("bytes", counted[1]);
          Workspace.writeJson(statsFile, json);
        }
      }
    }
    return new long[]{files, bytes};
  }

  private static long[] walkExcept(Path root, Path excluded) {
    long[] total = new long[2];
    try {
      Files.walkFileTree(root, new SimpleFileVisitor<>() {
        @Override
        public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
          return dir.equals(excluded) ? FileVisitResult.SKIP_SUBTREE : FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
          total[0]++;
          total[1] += attrs.size();
          return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFileFailed(Path file, IOException exc) {
          return FileVisitResult.CONTINUE;
        }
      });
    } catch (IOException ignored) {
      // an unreadable subtree contributes nothing
    }
    return total;
  }

  /** Trees are measured once, at decompile time; --measure backfills trees created before that. */
  private static long[] treeUsage(Path trees, boolean measure) throws IOException {
    if (!Files.isDirectory(trees)) {
      return new long[]{0, 0, 0};
    }
    List<Path> children = new ArrayList<>();
    try (var list = Files.list(trees)) {
      list.forEach(children::add);
    }
    long bytes = 0;
    List<Path> unmeasured = new ArrayList<>();
    for (Path tree : children) {
      Path meta = tree.resolve("meta.json");
      if (Files.exists(meta)) {
        try {
          var json = Workspace.readJson(meta);
          if (json.has("bytes")) {
            // meta.json itself is outside the measured src directory; count it too.
            bytes += json.get("bytes").getAsLong() + Files.size(meta);
            continue;
          }
        } catch (Exception ignored) {
          // a damaged meta.json is treated like a missing one
        }
      }
      unmeasured.add(tree);
    }
    if (measure && !unmeasured.isEmpty()) {
      ExecutorService pool = Executors.newFixedThreadPool(
        Math.max(1, Math.min(unmeasured.size(), Runtime.getRuntime().availableProcessors())));
      try {
        List<Future<long[]>> futures = new ArrayList<>();
        for (Path tree : unmeasured) {
          futures.add(pool.submit(() -> walk(tree.resolve("src"))));
        }
        for (int i = 0; i < futures.size(); i++) {
          long size;
          try {
            size = futures.get(i).get()[1];
          } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            break;
          } catch (ExecutionException e) {
            continue;
          }
          bytes += size;
          Path meta = unmeasured.get(i).resolve("meta.json");
          try {
            var json = Files.exists(meta) ? Workspace.readJson(meta) : new com.google.gson.JsonObject();
            json.addProperty("bytes", size);
            Workspace.writeJson(meta, json);
            bytes += Files.size(meta);
          } catch (Exception ignored) {
            // the size is still counted for this run
          }
        }
      } finally {
        pool.shutdownNow();
      }
      return new long[]{children.size(), bytes, 0};
    }
    return new long[]{children.size(), bytes, unmeasured.size()};
  }

  private static void printUsage(String label, Path dir) throws IOException {
    long[] usage = usage(dir);
    System.out.println(label + ": " + usage[0] + " files, " + human(usage[1]));
  }

  /**
   * File count and byte size under a directory, walked in parallel over its immediate children:
   * the caches hold hundreds of thousands of small files, and one sequential walk is dominated by
   * per-file metadata latency on Windows.
   */
  private static long[] usage(Path dir) throws IOException {
    if (!Files.isDirectory(dir)) {
      return new long[]{0, 0};
    }
    List<Path> children = new ArrayList<>();
    try (var list = Files.list(dir)) {
      list.forEach(children::add);
    }
    int threads = Math.max(1, Math.min(children.size(), Runtime.getRuntime().availableProcessors()));
    ExecutorService pool = Executors.newFixedThreadPool(threads);
    try {
      List<Future<long[]>> futures = new ArrayList<>();
      for (Path child : children) {
        futures.add(pool.submit(() -> walk(child)));
      }
      long files = 0;
      long bytes = 0;
      for (Future<long[]> future : futures) {
        try {
          long[] part = future.get();
          files += part[0];
          bytes += part[1];
        } catch (ExecutionException e) {
          // an unreadable subtree contributes nothing
        } catch (InterruptedException e) {
          Thread.currentThread().interrupt();
          break;
        }
      }
      return new long[]{files, bytes};
    } finally {
      pool.shutdownNow();
    }
  }

  private static long[] walk(Path root) {
    long[] total = new long[2];
    try (var walk = Files.walk(root)) {
      walk.forEach(path -> {
        if (Files.isRegularFile(path)) {
          total[0]++;
          try {
            total[1] += Files.size(path);
          } catch (IOException ignored) {
            // files can vanish under a concurrent prune; they contribute no bytes
          }
        }
      });
    } catch (IOException ignored) {
      // an unreadable subtree contributes nothing
    }
    return total;
  }

  private static String human(long bytes) {
    if (bytes >= 1_000_000_000L) {
      return String.format(Locale.ROOT, "%.1f GB", bytes / 1_000_000_000.0);
    }
    return String.format(Locale.ROOT, "%.1f MB", bytes / 1_000_000.0);
  }

  private static int threadsDefault() {
    return Math.max(1, Runtime.getRuntime().availableProcessors());
  }

  /**
   * Verification must run on the JDK the target was compiled with: a different javac renumbers
   * lambdas and moves line anchors, so identical classes would be reported as differing. The
   * command re-runs itself on a matching installed JDK; nothing is exposed on the command line.
   */
  private static final String REEXEC = "DEVTOOLS_JDK_EXEC";

  private static boolean needsTargetJdk(String command) {
    return switch (command) {
      case "score", "dataset", "corpus", "compile" -> true;
      default -> false;
    };
  }

  private static void ensureTargetJdk(Minecraft minecraft, String version, String[] args) throws Exception {
    if (System.getenv(REEXEC) != null) {
      return;
    }
    int release = Verifier.releaseOf(minecraft.clientJar(version, false));
    int current = Runtime.version().feature();
    if (release <= 0 || release == current) {
      return;
    }
    Path java = findJdk(release);
    if (java == null) {
      System.err.println("devtools: no JDK " + release + " installed; running on JDK " + current);
      return;
    }
    Path jar = Path.of(Main.class.getProtectionDomain().getCodeSource().getLocation().toURI());
    List<String> command = new ArrayList<>();
    command.add(java.toString());
    command.add("-jar");
    command.add(jar.toString());
    command.addAll(List.of(args));
    ProcessBuilder builder = new ProcessBuilder(command).inheritIO();
    builder.environment().put(REEXEC, "1");
    System.exit(builder.start().waitFor());
  }

  private static Path findJdk(int release) {
    List<Path> candidates = new ArrayList<>();
    String home = System.getenv("JAVA_HOME");
    if (home != null && !home.isBlank()) {
      candidates.add(Path.of(home));
    }
    String path = System.getenv("PATH");
    if (path != null) {
      for (String entry : path.split(java.io.File.pathSeparator)) {
        Path bin = Path.of(entry);
        if (Files.isRegularFile(bin.resolve("java.exe")) || Files.isRegularFile(bin.resolve("java"))) {
          candidates.add(bin.getParent());
        }
      }
    }
    String userHome = System.getProperty("user.home");
    List<String> bases = new ArrayList<>(List.of(userHome + "/.gradle/jdks", userHome + "/.jdks"));
    if (isWindows()) {
      bases.add("C:/Program Files/Java");
      bases.add("C:/Program Files/Eclipse Adoptium");
    } else {
      bases.add("/usr/lib/jvm");
      bases.add("/Library/Java/JavaVirtualMachines");
    }
    for (String base : bases) {
      Path dir = Path.of(base);
      if (!Files.isDirectory(dir)) {
        continue;
      }
      try (var list = Files.list(dir)) {
        for (Path child : list.filter(Files::isDirectory).toList()) {
          candidates.add(child);
          candidates.add(child.resolve("Contents/Home")); // macOS bundle layout
        }
      } catch (java.io.IOException ignored) {
        // An unreadable install directory simply offers no candidate.
      }
    }
    for (Path candidate : candidates) {
      if (majorOf(candidate) == release) {
        return candidate.resolve("bin").resolve(isWindows() ? "java.exe" : "java");
      }
    }
    return provisionJdk(release);
  }

  /**
   * Asks Gradle's toolchain service for a matching JDK; the foojay resolver downloads one into
   * the Gradle user home when no local installation matches.
   */
  private static Path provisionJdk(int release) {
    Path root = projectRoot();
    if (root == null) {
      return null;
    }
    System.err.println("devtools: no JDK " + release + " installed; asking Gradle to provision one");
    List<String> command = new ArrayList<>();
    if (isWindows()) {
      command.add("cmd.exe");
      command.add("/c");
      command.add(root.resolve("gradlew.bat").toString());
    } else {
      command.add(root.resolve("gradlew").toString());
    }
    command.add("-q");
    command.add(":devtools:provisionJdk");
    command.add("-Pjdk=" + release);
    try {
      Process process = new ProcessBuilder(command).directory(root.toFile())
        .redirectErrorStream(true).start();
      String out = new String(process.getInputStream().readAllBytes(),
        java.nio.charset.StandardCharsets.UTF_8);
      if (process.waitFor() != 0) {
        System.err.println("devtools: Gradle could not provision JDK " + release
          + (out.isBlank() ? "" : ": " + out.strip()));
        return null;
      }
      String[] lines = out.strip().split("\\R");
      Path home = Path.of(lines[lines.length - 1].strip());
      Path java = home.resolve("bin").resolve(isWindows() ? "java.exe" : "java");
      return Files.isRegularFile(java) ? java : null;
    } catch (Exception e) {
      System.err.println("devtools: Gradle could not provision JDK " + release + ": " + e.getMessage());
      return null;
    }
  }

  /** The checkout carrying the Gradle build, found from the working directory or the jar. */
  private static Path projectRoot() {
    List<Path> starts = new ArrayList<>();
    starts.add(Path.of("").toAbsolutePath());
    try {
      Path jar = Path.of(Main.class.getProtectionDomain().getCodeSource().getLocation().toURI());
      starts.add(Files.isDirectory(jar) ? jar : jar.getParent());
    } catch (Exception ignored) {
      // An unreadable code source simply offers no starting point.
    }
    for (Path start : starts) {
      for (Path dir = start; dir != null; dir = dir.getParent()) {
        if (Files.isRegularFile(dir.resolve("gradlew")) && Files.isRegularFile(dir.resolve("settings.gradle"))) {
          return dir;
        }
      }
    }
    return null;
  }

  private static int majorOf(Path jdk) {
    Path javaBin = jdk.resolve("bin").resolve(isWindows() ? "java.exe" : "java");
    if (!Files.isRegularFile(javaBin)) {
      return -1;
    }
    try {
      Process process = new ProcessBuilder(javaBin.toString(), "-version").redirectErrorStream(true).start();
      String output = new String(process.getInputStream().readAllBytes(),
        java.nio.charset.StandardCharsets.UTF_8);
      process.waitFor();
      var matcher = java.util.regex.Pattern.compile("version \"(\\d+)").matcher(output);
      return matcher.find() ? Integer.parseInt(matcher.group(1)) : -1;
    } catch (Exception e) {
      return -1;
    }
  }

  private static boolean isWindows() {
    return System.getProperty("os.name").toLowerCase().contains("win");
  }

  private static String positional(List<String> args) {
    List<String> all = positionals(args);
    if (all.isEmpty()) {
      throw new IllegalArgumentException("missing version");
    }
    return all.get(0);
  }

  /** Every non-flag argument, skipping the value of the flags that take one. */
  private static List<String> positionals(List<String> args) {
    List<String> values = new ArrayList<>();
    for (int i = 0; i < args.size(); i++) {
      String arg = args.get(i);
      if (arg.equals("--threads") || arg.equals("--only") || arg.equals("--jobs")
          || arg.equals("--options") || arg.equals("--timeout")) {
        i++;
        continue;
      }
      if (!arg.startsWith("--")) {
        values.add(arg);
      }
    }
    return values;
  }

  private static int intFlag(List<String> args, String name, int fallback) {
    for (int i = 0; i < args.size() - 1; i++) {
      if (args.get(i).equals(name)) {
        return Integer.parseInt(args.get(i + 1));
      }
    }
    return fallback;
  }

  private static String stringFlag(List<String> args, String name, String fallback) {
    for (int i = 0; i < args.size() - 1; i++) {
      if (args.get(i).equals(name)) {
        return args.get(i + 1);
      }
    }
    return fallback;
  }

  /** Decompiler flags for an experimental variant, e.g. {@code --options "--rt-no-generic-cast=1"}. */
  private static List<String> optionsFlag(List<String> args) {
    String value = stringFlag(args, "--options", null);
    if (value == null || value.isBlank()) {
      return List.of();
    }
    return List.of(value.trim().split("\\s+"));
  }

  private static void usage() {
    System.out.println("""
      usage: devtools/cli <command> [options]

        versions [--no-cache]                  list Mojang's versions
        decompile <version> [--no-cache] [--threads N] [--only Class]
        tree      <version> [--only Class]    print the cached tree path
        score     <version> [<version>...] [--no-cache] [--only Class] [--threads N] [--json] [--jobs N] [--timeout minutes]
                                             several versions run concurrently, --jobs at a time
        compile   <version> <Class>            compile that one class with the verifier's javac
                                             settings and print its errors
        corpus    <version> --ground-truth D  write the class-to-ground-truth corpus
        dataset   <version>                   export per-instruction line alignment for the model
        clean     [--trees] [--compile] [--downloads] [--all]
        reports   [--version V] [--limit N]   list past scores
        cache                                 show cache usage (file counts and sizes)
      """);
  }

  private Main() {
  }
}

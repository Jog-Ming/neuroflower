package org.vineflower.devtools;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.FileObject;
import javax.tools.ForwardingJavaFileManager;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.OutputStream;
import java.net.URI;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.zip.ZipFile;

/**
 * Compiles a source tree (or one file) against the original jar and reports per-class attribute
 * matches. Results are cached by source content and toolchain, so an unchanged file is never
 * compiled twice.
 */
public final class Verifier {
  public record ClassResult(String name, Map<String, Boolean> flags, List<String> details, boolean compiled,
                            boolean extra) {
  }

  public record FileResult(String source, List<ClassResult> classes, List<String> errors, boolean cached,
                           Metrics metrics) {
  }

  /**
   * Source-quality counters of one file or tree. Raw types, redundant single casts and unchecked
   * operations come from javac's lint; double casts come from the text matcher, since javac has no
   * warning for them.
   */
  public record Metrics(int raw, int redundantCasts, int unchecked, int doubleCasts) {
    public static final Metrics ZERO = new Metrics(0, 0, 0, 0);

    public Metrics plus(Metrics other) {
      return new Metrics(raw + other.raw, redundantCasts + other.redundantCasts,
        unchecked + other.unchecked, doubleCasts + other.doubleCasts);
    }
  }

  record Compiled(boolean ok, Map<String, byte[]> outputs, List<String> errors, Metrics metrics) {
  }

  /** One compiler and one file manager per worker: scanning the classpath is the expensive part. */
  private static final ThreadLocal<JavaCompiler> COMPILER =
    ThreadLocal.withInitial(ToolProvider::getSystemJavaCompiler);
  private static final ThreadLocal<StandardJavaFileManager> FILES = ThreadLocal.withInitial(() ->
    COMPILER.get().getStandardFileManager(null, Locale.ROOT, StandardCharsets.UTF_8));

  /** Bump when the comparison changes: it is part of the cache key, not of the source hash. */
  private static final String COMPARATOR_VERSION = "11";

  private final Workspace workspace;
  private final Minecraft minecraft;

  public Verifier(Workspace workspace, Minecraft minecraft) {
    this.workspace = workspace;
    this.minecraft = minecraft;
  }

  public List<FileResult> score(String version, Path target, String only, int threads, boolean json)
      throws Exception {
    return score(version, target, only, threads, json, null);
  }

  /**
   * Scores a tree, and when {@code since} is given also lists which files changed relative to that
   * earlier tree — the attribution half of an A/B, which the attribute counts cannot show.
   */
  public List<FileResult> score(String version, Path target, String only, int threads, boolean json,
                                Path since) throws Exception {
    Path client = minecraft.clientJar(version, false);
    Path originalClasses = minecraft.extractedClasses(version, false);
    List<Path> classpath = minecraft.classpath(version, false);
    int release = releaseOf(client);
    String stamp = stamp(client, classpath, release);

    List<Path> sources = sources(target, only);
    if (sources.isEmpty()) {
      throw new IllegalArgumentException("no sources under " + target + (only == null ? "" : " for " + only));
    }

    ExecutorService pool = Executors.newFixedThreadPool(Math.max(1, threads));
    List<Callable<FileResult>> tasks = new ArrayList<>();
    Path compileCache = workspace.cache.resolve("compile");
    for (Path source : sources) {
      tasks.add(() -> scoreFile(source, originalClasses, classpath, release, stamp, compileCache));
    }

    long started = System.nanoTime();
    List<FileResult> results = new ArrayList<>();
    try {
      for (Future<FileResult> future : pool.invokeAll(tasks)) {
        results.add(future.get());
      }
    } finally {
      pool.shutdown();
    }
    long elapsed = (System.nanoTime() - started) / 1_000_000;

    // Entries are evicted by age, not by whether this run used them: an A/B alternates between
    // two source sets, and evicting the other side each time would make every run a cold one.
    if (only == null && Files.isDirectory(target)) {
      // Nine versions with ~7k sources each fit at once; a smaller cap makes every sweep a cold
      // compile for the versions that fell out. The walk stats every entry, which costs minutes
      // on Windows, so a day's grace between prunes keeps the scoring loop cheap.
      if (pruneDue(workspace)) {
        pruneCompileCache(compileCache, ".json", 200_000);
        pruneCompileCache(workspace.cache.resolve("classes"), ".bin", 150_000);
      }
    }

    long totalClasses = Files.isDirectory(target) && only == null
      ? countClasses(originalClasses) : 0;
    report(version, target, results, elapsed, json, totalClasses);
    if (since != null) {
      System.out.print(treeSince(target, since));
    }
    return results;
  }

  /**
   * Which generated files differ between two trees. Both trees are content-addressed outputs of a
   * decompile, so the comparison is a hash walk: no decompile, no compile, no verifier.
   */
  static String treeSince(Path current, Path previous) throws IOException {
    Map<String, String> before = treeHashes(previous);
    Map<String, String> now = treeHashes(current);
    List<String> added = new ArrayList<>();
    List<String> removed = new ArrayList<>();
    List<String> changed = new ArrayList<>();
    for (Map.Entry<String, String> entry : now.entrySet()) {
      String old = before.get(entry.getKey());
      if (old == null) {
        added.add(entry.getKey());
      } else if (!old.equals(entry.getValue())) {
        changed.add(entry.getKey());
      }
    }
    for (String key : before.keySet()) {
      if (!now.containsKey(key)) {
        removed.add(key);
      }
    }
    StringBuilder out = new StringBuilder();
    out.append(String.format(Locale.ROOT, "since %s:%n  %d changed, %d added, %d removed%n",
      previous, changed.size(), added.size(), removed.size()));
    listTreeChanges(out, "changed", changed);
    listTreeChanges(out, "added", added);
    listTreeChanges(out, "removed", removed);
    return out.toString();
  }

  private static void listTreeChanges(StringBuilder out, String label, List<String> names) {
    int shown = Math.min(names.size(), 40);
    for (int i = 0; i < shown; i++) {
      out.append("  ").append(label.charAt(0)).append(' ').append(names.get(i)).append('\n');
    }
    if (names.size() > shown) {
      out.append("  ... ").append(names.size() - shown).append(" more ").append(label).append('\n');
    }
  }

  private static Map<String, String> treeHashes(Path root) throws IOException {
    Map<String, String> out = new java.util.TreeMap<>();
    try (java.util.stream.Stream<Path> walk = Files.walk(root)) {
      for (Path path : (Iterable<Path>) walk.filter(Files::isRegularFile)
          .filter(p -> p.getFileName().toString().endsWith(".java"))::iterator) {
        out.put(root.relativize(path).toString().replace('\\', '/'),
          Workspace.sha256(Files.readAllBytes(path)));
      }
    }
    return out;
  }

  /**
   * One class, verified and explained: every attribute and the per-method detail behind each
   * failure. This is what a per-class A/B needs, in one process instead of a decompile, a compile
   * and two {@code javap} runs.
   */
  public boolean diff(String version, Path tree, List<String> classes, int threads) throws Exception {
    Path client = minecraft.clientJar(version, false);
    Path originalClasses = minecraft.extractedClasses(version, false);
    List<Path> classpath = minecraft.classpath(version, false);
    int release = releaseOf(client);
    String stamp = stamp(client, classpath, release);
    // A file can hold several requested classes (an outer and its nests), so it is verified once.
    java.util.LinkedHashSet<Path> files = new java.util.LinkedHashSet<>();
    for (String className : classes) {
      List<Path> found = sources(tree, className);
      if (found.isEmpty()) {
        throw new IllegalArgumentException("no source for " + className + " under " + tree);
      }
      files.addAll(found);
    }
    System.out.println("tree:   " + tree);
    System.out.println("note:   a subset decompile; the whole-tree score is the only evidence");
    boolean ok = true;
    Path compileCache = workspace.cache.resolve("compile");
    for (Path source : files) {
      System.out.println("source: " + tree.relativize(source));
      FileResult result = scoreFile(source, originalClasses, classpath, release, stamp, compileCache);
      for (String error : result.errors()) {
        System.out.println("  error " + error);
      }
      for (ClassResult cls : result.classes()) {
        if (cls.extra()) {
          System.out.println(cls.name() + "  extra (no original class)");
          ok = false;
          continue;
        }
        if (!cls.compiled()) {
          System.out.println(cls.name() + "  did not compile");
          ok = false;
          continue;
        }
        List<String> failed = new ArrayList<>();
        for (String attribute : ClassDiff.ATTRIBUTES) {
          if (!cls.flags().getOrDefault(attribute, false)) {
            failed.add(attribute);
          }
        }
        System.out.println(cls.name() + "  " + (failed.isEmpty() ? "identical" : String.join(",", failed)));
        boolean structure = false;
        for (String detail : cls.details()) {
          if (detail.equals("bytes: raw bytes differ")) {
            continue; // the strictest check; every other detail says what actually diverged
          }
          structure = true;
          System.out.println("    " + detail);
        }
        if (!cls.flags().getOrDefault("bytes", true)
            && !cls.flags().getOrDefault(ClassDiff.NOLNT, true)) {
          Compiled compiled = compile(source, classpath, release);
          byte[] ours = compiled.outputs().get(cls.name().replace('/', '.'));
          Path originalFile = originalClasses.resolve(cls.name() + ".class");
          if (ours != null && Files.exists(originalFile)) {
            for (String line : ClassDiff.byteDifference(Files.readAllBytes(originalFile), ours)) {
              System.out.println("    " + line);
            }
            if (System.getenv("NEUROFLOWER_DIFF_BYTES") != null) {
              Path dumped = workspace.tmp.resolve("compiled").resolve(cls.name() + ".class");
              Files.createDirectories(dumped.getParent());
              Workspace.write(dumped, ours);
              System.out.println("    wrote " + dumped);
            }
          }
        }
        if (!structure && failed.size() == 1 && failed.get(0).equals("bytes")) {
          System.out.println("    every structural attribute matches: only the constant pool or its"
            + " ordering differs");
        }
        ok &= failed.isEmpty();
      }
    }
    return ok;
  }

  private FileResult scoreFile(Path source, Path originalClasses, List<Path> classpath, int release,
                               String stamp, Path compileCache) throws Exception {
    byte[] bytes = Files.readAllBytes(source);
    // javac records the source file's own name in SourceFile; the same text under another
    // name compiles to different bytes.
    String key = Workspace.sha256(Workspace.sha256(bytes) + "|" + source.getFileName() + "|" + stamp);
    Path cached = compileCache.resolve(key.substring(0, 2)).resolve(key + ".json");
    if (Files.exists(cached) && System.getenv("NEUROFLOWER_DIFF_DUMP") == null) {
      Files.setLastModifiedTime(cached, java.nio.file.attribute.FileTime.fromMillis(System.currentTimeMillis()));
      return readCache(source, cached);
    }

    Compiled compiled = compile(source, classpath, release);
    SourceMetrics.Counts sourceCounts = SourceMetrics.casts(new String(bytes, StandardCharsets.UTF_8));
    Metrics metrics = new Metrics(compiled.metrics().raw(), compiled.metrics().redundantCasts(),
      compiled.metrics().unchecked(), sourceCounts.doubleCasts());

    List<ClassResult> classes = new ArrayList<>();
    List<String> errors = new ArrayList<>();
    if (!compiled.ok()) {
      errors.addAll(compiled.errors());
      classes.add(new ClassResult(classNameOf(source), allFalse("not compiled: "
        + (errors.isEmpty() ? "javac failed" : errors.get(0))), errors, false, false));
    } else {
      Map<String, byte[]> outputs = compiled.outputs();
      List<String> names = new ArrayList<>(outputs.keySet());
      Collections.sort(names);
      for (String binary : names) {
        String name = binary.replace('.', '/');
        Path originalFile = originalClasses.resolve(name + ".class");
        if (!Files.exists(originalFile)) {
          classes.add(new ClassResult(name, allFalse("no original class in the jar"), List.of(), true, true));
          continue;
        }
        ClassDiff diff = ClassDiff.compare(Files.readAllBytes(originalFile), outputs.get(binary));
        classes.add(new ClassResult(diff.name, diff.matches, diff.details, true, false));
      }
    }
    FileResult result = new FileResult(source.toString(), classes, errors, false, metrics);
    writeCache(cached, result);
    return result;
  }

  /** One error with the source position javac attributes to it. */
  public record Problem(long position, long line, long column, String message) {
  }

  static List<Problem> diagnose(Path source, List<Path> classpath, int release) throws IOException {
    DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<>();
    JavaCompiler compiler = COMPILER.get();
    StandardJavaFileManager files = FILES.get();
    MemoryOutput memory = new MemoryOutput(files);
    compiler.getTask(null, memory, diagnostics, options(classpath, release), null,
      files.getJavaFileObjects(source)).call();
    List<Problem> problems = new ArrayList<>();
    for (Diagnostic<? extends JavaFileObject> diagnostic : diagnostics.getDiagnostics()) {
      if (diagnostic.getKind() == Diagnostic.Kind.ERROR) {
        problems.add(new Problem(diagnostic.getPosition(), diagnostic.getLineNumber(),
          diagnostic.getColumnNumber(), diagnostic.getMessage(Locale.ROOT)));
      }
    }
    return problems;
  }

  private static List<String> options(List<Path> classpath, int release) {
    // The lint categories feed the source-quality counters; they are measured, not acted on. A
    // diagnostic collector receives them instead of the console, so no -nowarn is needed.
    return List.of(
      "--release", Integer.toString(release),
      "-g", "-parameters", "-proc:none", "-implicit:none",
      "-Xlint:rawtypes,cast,unchecked",
      "-classpath", join(classpath));
  }

  private static final Map<String, String> STAMPS = new java.util.concurrent.ConcurrentHashMap<>();
  private static Path classCache;

  private static synchronized Path classCache() {
    if (classCache == null) {
      classCache = Workspace.load().cache.resolve("classes");
    }
    return classCache;
  }

  /** Identifies the compiler, its flags and the classpath a cached class set belongs to. */
  private static String compileStamp(List<Path> classpath, int release) {
    String key = release + "|" + classpath;
    return STAMPS.computeIfAbsent(key, ignored -> {
      StringBuilder libs = new StringBuilder();
      for (Path path : classpath) {
        try {
          libs.append(path.getFileName()).append(':').append(Files.size(path)).append(';');
        } catch (IOException e) {
          libs.append(path.getFileName()).append(":?;");
        }
      }
      String client = classpath.isEmpty() ? "" : Workspace.sha256(classpath.get(0));
      return Workspace.sha256(COMPARATOR_VERSION + "|" + System.getProperty("java.version") + "|"
        + System.getProperty("java.home") + "|" + release + "|" + client + "|" + libs);
    });
  }

  /** One file, compiled against the original jar, with its classes kept in memory. */
  static Compiled compile(Path source, List<Path> classpath, int release) throws IOException {
    byte[] sourceBytes = Files.readAllBytes(source);
    String key = Workspace.sha256(
      Workspace.sha256(sourceBytes) + "|" + source.getFileName() + "|" + compileStamp(classpath, release));
    Path cached = classCache().resolve(key.substring(0, 2)).resolve(key + ".bin");
    if (Files.exists(cached)) {
      try {
        Compiled compiled = readCompiled(cached);
        Files.setLastModifiedTime(cached,
          java.nio.file.attribute.FileTime.fromMillis(System.currentTimeMillis()));
        return compiled;
      } catch (IOException | RuntimeException ignored) {
        // A truncated entry is simply recompiled.
      }
    }
    DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<>();
    JavaCompiler compiler = COMPILER.get();
    StandardJavaFileManager files = FILES.get();
    MemoryOutput memory = new MemoryOutput(files);
    boolean ok = compiler.getTask(null, memory, diagnostics, options(classpath, release), null,
      files.getJavaFileObjects(source)).call();
    List<String> errors = new ArrayList<>();
    int raw = 0;
    int redundantCasts = 0;
    int unchecked = 0;
    for (Diagnostic<? extends JavaFileObject> diagnostic : diagnostics.getDiagnostics()) {
      if (diagnostic.getKind() == Diagnostic.Kind.ERROR) {
        if (!ok && errors.size() < 8) {
          errors.add(diagnostic.getLineNumber() + ":"
            + diagnostic.getMessage(Locale.ROOT).split("\n")[0]);
        }
        continue;
      }
      if (diagnostic.getKind() != Diagnostic.Kind.WARNING
          && diagnostic.getKind() != Diagnostic.Kind.MANDATORY_WARNING) {
        continue;
      }
      String code = diagnostic.getCode();
      if (code.startsWith("compiler.warn.raw.")) {
        raw++;
      }
      else if (code.startsWith("compiler.warn.redundant.cast")) {
        redundantCasts++;
      }
      else if (code.startsWith("compiler.warn.unchecked")
          || code.startsWith("compiler.warn.prob.found.req")) {
        unchecked++;
      }
    }
    Metrics metrics = new Metrics(raw, redundantCasts, unchecked, 0);
    if (ok) {
      try {
        Workspace.write(cached, serialize(memory.outputs, metrics));
      } catch (IOException ignored) {
        // The cache is an optimisation; a failed write must not fail the compile.
      }
    }
    return new Compiled(ok, ok ? memory.outputs : Map.of(), errors, metrics);
  }

  private static byte[] serialize(Map<String, byte[]> outputs, Metrics metrics) throws IOException {
    ByteArrayOutputStream bytes = new ByteArrayOutputStream();
    try (DataOutputStream data = new DataOutputStream(bytes)) {
      data.writeInt(outputs.size());
      for (Map.Entry<String, byte[]> entry : outputs.entrySet()) {
        data.writeUTF(entry.getKey());
        data.writeInt(entry.getValue().length);
        data.write(entry.getValue());
      }
      data.writeInt(metrics.raw());
      data.writeInt(metrics.redundantCasts());
      data.writeInt(metrics.unchecked());
    }
    return bytes.toByteArray();
  }

  private static Compiled readCompiled(Path file) throws IOException {
    try (DataInputStream data = new DataInputStream(Files.newInputStream(file))) {
      int count = data.readInt();
      Map<String, byte[]> outputs = new LinkedHashMap<>();
      for (int i = 0; i < count; i++) {
        String name = data.readUTF();
        byte[] bytes = new byte[data.readInt()];
        data.readFully(bytes);
        outputs.put(name, bytes);
      }
      Metrics metrics = new Metrics(data.readInt(), data.readInt(), data.readInt(), 0);
      return new Compiled(true, outputs, List.of(), metrics);
    }
  }

  /** Compiles into memory: no per-file output directory, no write and read back. */
  static final class MemoryOutput extends ForwardingJavaFileManager<JavaFileManager> {
    final Map<String, byte[]> outputs = new LinkedHashMap<>();

    MemoryOutput(JavaFileManager delegate) {
      super(delegate);
    }

    @Override
    public JavaFileObject getJavaFileForOutput(JavaFileManager.Location location, String className,
                                               JavaFileObject.Kind kind,
                                               FileObject sibling) {
      return new SimpleJavaFileObject(URI.create("mem:///" + className.replace('.', '/') + kind.extension), kind) {
        @Override
        public OutputStream openOutputStream() {
          return new ByteArrayOutputStream() {
            @Override
            public void close() throws IOException {
              outputs.put(className, toByteArray());
              super.close();
            }
          };
        }
      };
    }
  }

  private static Map<String, Boolean> allFalse(String detail) {
    Map<String, Boolean> flags = new LinkedHashMap<>();
    for (String attribute : ClassDiff.ATTRIBUTES) {
      flags.put(attribute, false);
    }
    return flags;
  }

  private static String classNameOf(Path source) {
    String name = source.getFileName().toString();
    return name.endsWith(".java") ? name.substring(0, name.length() - ".java".length()) : name;
  }

  private static long countClasses(Path dir) throws IOException {
    try (var walk = Files.walk(dir)) {
      return walk.filter(p -> p.toString().endsWith(".class")).count();
    }
  }

  private void report(String version, Path target, List<FileResult> results, long elapsed, boolean json,
                      long totalClasses) throws IOException {
    int files = results.size();
    int cached = (int) results.stream().filter(FileResult::cached).count();
    int classes = 0;
    int compiled = 0;
    Map<String, Integer> matches = new LinkedHashMap<>();
    for (String attribute : ClassDiff.ATTRIBUTES) {
      matches.put(attribute, 0);
    }
    int fully = 0;
    int nonLnt = 0;
    int extras = 0;
    int failingFiles = 0;
    Metrics totals = Metrics.ZERO;
    List<String> worst = new ArrayList<>();
    for (FileResult result : results) {
      totals = totals.plus(result.metrics());
      if (!result.errors().isEmpty()) {
        failingFiles++;
      }
      for (ClassResult cls : result.classes()) {
        if (cls.extra()) {
          extras++;
          continue;
        }
        if (!cls.compiled()) {
          continue; // the file did not compile; counted below, not as a class
        }
        classes++;
        compiled++;
        boolean all = true;
        for (String attribute : ClassDiff.ATTRIBUTES) {
          boolean value = cls.flags().getOrDefault(attribute, false);
          if (value) {
            matches.merge(attribute, 1, Integer::sum);
          } else {
            all = false;
          }
        }
        if (cls.flags().getOrDefault(ClassDiff.NOLNT, true)) {
          nonLnt++;
        }
        if (all) {
          fully++;
        } else if (worst.size() < 12) {
          List<String> failed = new ArrayList<>();
          for (String attribute : ClassDiff.ATTRIBUTES) {
            if (!cls.flags().getOrDefault(attribute, false)) {
              failed.add(attribute);
            }
          }
          worst.add(cls.name() + "  " + String.join(",", failed)
            + (cls.details().isEmpty() ? "" : "  (" + cls.details().get(0) + ")"));
        }
      }
    }

    long missing = totalClasses > 0 ? totalClasses - compiled : 0;
    System.out.printf(Locale.ROOT,
      "sources %d (%d cached)  classes %d  compiled %d  missing %d  fully %d  extra %d  in %.1fs%n",
      files, cached, classes, compiled, Math.max(0, missing), fully, extras, elapsed / 1000.0);
    // A method Vineflower failed on is printed as a stub, so its class cannot compile and shows
    // up as missing. Say it here: the tree is cached and every later score would inherit it.
    Path treeMeta = target.getParent() == null ? null : target.getParent().resolve("meta.json");
    if (treeMeta != null && Files.exists(treeMeta)) {
      JsonObject meta = Workspace.readJson(treeMeta);
      JsonElement failedMethods = meta.get("failedMethods");
      if (failedMethods != null && failedMethods.getAsInt() > 0) {
        System.out.println("decompile failed on " + failedMethods.getAsInt()
          + " method(s) when this tree was built; rerun with --no-cache on a quiet machine");
      }
    }
    System.out.printf(Locale.ROOT, "%-12s %8s %8s%n", "attribute", "match", "rate");
    for (String attribute : ClassDiff.ATTRIBUTES) {
      int count = matches.get(attribute);
      // `code` compares instruction streams with the pool resolved by symbol, so it is the
      // non-reflective execution-logic metric: identical instructions, pool order ignored.
      String label = attribute.equals("code") ? "code/logic" : attribute;
      System.out.printf(Locale.ROOT, "%-12s %8d %7.1f%%%n", label, count,
        classes == 0 ? 0.0 : 100.0 * count / classes);
    }

    System.out.printf(Locale.ROOT, "non-lnt identical %d/%d (%.1f%%)%n",
      nonLnt, classes, classes == 0 ? 0.0 : 100.0 * nonLnt / classes);
    System.out.printf(Locale.ROOT, "metrics raw %d  cast %d  double %d  unchecked %d%n",
      totals.raw(), totals.redundantCasts(), totals.doubleCasts(), totals.unchecked());
    if (failingFiles > 0) {
      System.out.println("files that did not compile: " + failingFiles);
    }
    if (!worst.isEmpty()) {
      System.out.println("first diverging classes:");
      for (String line : worst) {
        System.out.println("  " + line);
      }
    }

    appendIndex(version, target, files, cached, classes, compiled, fully, matches, elapsed, totals);


    if (json) {
      JsonObject report = new JsonObject();
      report.addProperty("version", version);
      report.addProperty("tree", target.toString());
      report.addProperty("target", target.toString());
      report.addProperty("files", files);
      report.addProperty("cachedFiles", cached);
      report.addProperty("classes", classes);
      report.addProperty("compiled", compiled);
      report.addProperty("jarClasses", totalClasses);
      report.addProperty("fully", fully);
      report.addProperty("extraClasses", extras);
      report.addProperty("elapsedMillis", elapsed);
      JsonObject attributeJson = new JsonObject();
      matches.forEach(attributeJson::addProperty);
      report.add("attributes", attributeJson);
      JsonObject metricsJson = new JsonObject();
      metricsJson.addProperty("raw", totals.raw());
      metricsJson.addProperty("redundantCasts", totals.redundantCasts());
      metricsJson.addProperty("doubleCasts", totals.doubleCasts());
      metricsJson.addProperty("unchecked", totals.unchecked());
      report.add("metrics", metricsJson);
      JsonArray fileArray = new JsonArray();
      for (FileResult result : results) {
        JsonObject fileJson = new JsonObject();
        fileJson.addProperty("source", result.source());
        JsonObject fileMetrics = new JsonObject();
        fileMetrics.addProperty("raw", result.metrics().raw());
        fileMetrics.addProperty("redundantCasts", result.metrics().redundantCasts());
        fileMetrics.addProperty("doubleCasts", result.metrics().doubleCasts());
        fileMetrics.addProperty("unchecked", result.metrics().unchecked());
        fileJson.add("metrics", fileMetrics);
        if (!result.errors().isEmpty()) {
          JsonArray errorArray = new JsonArray();
          result.errors().forEach(errorArray::add);
          fileJson.add("errors", errorArray);
        }
        JsonArray classArray = new JsonArray();
        for (ClassResult cls : result.classes()) {
          JsonObject classJson = new JsonObject();
          classJson.addProperty("name", cls.name());
          classJson.addProperty("compiled", cls.compiled());
          classJson.addProperty("extra", cls.extra());
          JsonObject flags = new JsonObject();
          cls.flags().forEach(flags::addProperty);
          classJson.add("flags", flags);
          JsonArray details = new JsonArray();
          cls.details().forEach(details::add);
          classJson.add("details", details);
          classArray.add(classJson);
        }
        fileJson.add("classes", classArray);
        fileArray.add(fileJson);
      }
      report.add("files_detail", fileArray);
      Path reports = workspace.reports;
      Files.createDirectories(reports);
      Path path = reports.resolve("score-" + version + "-" + System.currentTimeMillis() + ".json");
      Workspace.writeJson(path, report);
      pruneReports(reports, 50);
      System.out.println("report: " + path);
    }
  }

  /** One line per run: small enough to keep forever, enough to compare runs and plot progress. */
  private void appendIndex(String version, Path target, int files, int cached, int classes, int compiled,
                           int fully, Map<String, Integer> matches, long elapsed, Metrics totals)
    throws IOException {
    Path index = workspace.reports.resolve("index.tsv");
    boolean fresh = !Files.exists(index);
    StringBuilder line = new StringBuilder();
    if (fresh) {
      line.append("epoch\tversion\tclasses\tcompiled\tfully\tcached\tfiles\tmillis");
      for (String attribute : ClassDiff.ATTRIBUTES) {
        line.append('\t').append(attribute);
      }
      line.append("\ttree\traw\tcast\tdouble\tunchecked\n");
    }
    line.append(System.currentTimeMillis()).append('\t').append(version).append('\t')
      .append(classes).append('\t').append(compiled).append('\t').append(fully).append('\t')
      .append(cached).append('\t').append(files).append('\t').append(elapsed);
    for (String attribute : ClassDiff.ATTRIBUTES) {
      line.append('\t').append(matches.getOrDefault(attribute, 0));
    }
    line.append('\t').append(target)
      .append('\t').append(totals.raw())
      .append('\t').append(totals.redundantCasts())
      .append('\t').append(totals.doubleCasts())
      .append('\t').append(totals.unchecked())
      .append('\n');
    Files.createDirectories(index.getParent());
    Files.writeString(index, line, StandardOpenOption.CREATE, StandardOpenOption.APPEND);
  }

  /** Keeps entries that were used recently; the cap bounds a very large A/B matrix. */
  /** Whether a day has passed since the cache was last pruned. */
  private static boolean pruneDue(Workspace workspace) throws IOException {
    Path marker = workspace.cache.resolve("last-prune");
    long now = System.currentTimeMillis();
    if (Files.isRegularFile(marker)
        && now - Files.getLastModifiedTime(marker).toMillis() < 24L * 60 * 60 * 1000) {
      return false;
    }
    Files.createDirectories(marker.getParent());
    Files.writeString(marker, Long.toString(now));
    return true;
  }

  private static void pruneCompileCache(Path compileCache, String suffix, int maxEntries) throws IOException {
    if (!Files.isDirectory(compileCache)) {
      return;
    }
    long now = System.currentTimeMillis();
    long maxAge = 14L * 24 * 60 * 60 * 1000;
    List<Path> entries = new ArrayList<>();
    try (var walk = Files.walk(compileCache)) {
      for (Path path : walk.filter(p -> p.toString().endsWith(suffix)).toList()) {
        long used = Files.getLastModifiedTime(path).toMillis();
        if (now - used > maxAge) {
          Files.deleteIfExists(path);
        } else {
          entries.add(path);
        }
      }
    }
    if (entries.size() > maxEntries) {
      entries.sort(java.util.Comparator.comparingLong(p -> {
        try {
          return Files.getLastModifiedTime(p).toMillis();
        } catch (IOException e) {
          return 0L;
        }
      }));
      for (int i = 0; i < entries.size() - maxEntries; i++) {
        Files.deleteIfExists(entries.get(i));
      }
    }
  }

  private static void pruneReports(Path reports, int keep) throws IOException {
    try (var list = Files.list(reports)) {
      List<Path> files = new ArrayList<>(list.filter(p -> p.getFileName().toString().endsWith(".json")).toList());
      // Newest first by modification time: sorting the names put every 26.x report ahead of
      // 1.21.x, so the main version's reports were the ones pruned.
      files.sort(java.util.Comparator.comparingLong((Path p) -> {
        try {
          return java.nio.file.Files.getLastModifiedTime(p).toMillis();
        } catch (IOException e) {
          return 0L;
        }
      }).reversed());
      for (int i = keep; i < files.size(); i++) {
        Files.deleteIfExists(files.get(i));
      }
    }
  }

  static List<Path> sources(Path target, String only) throws IOException {
    if (Files.isRegularFile(target)) {
      return List.of(target);
    }
    Path root = target;
    String relative = only == null ? null : only.replace('.', '/') + ".java";
    try (var walk = Files.walk(root)) {
      List<Path> list = new ArrayList<>(walk.filter(p -> p.toString().endsWith(".java")).toList());
      if (relative != null) {
        String wanted = relative.replace('\\', '/');
        // An inner class has no file of its own: the decompiler names the file after the outermost
        // class, so X$Y is scored through X.java.
        int dollar = only.indexOf('$');
        String outer = dollar > 0 ? only.substring(0, dollar).replace('.', '/') + ".java" : null;
        list.removeIf(p -> {
          String path = root.relativize(p).toString().replace('\\', '/');
          return !path.endsWith(wanted) && (outer == null || !path.endsWith(outer));
        });
      }
      Collections.sort(list);
      return list;
    }
  }

  // ------------------------------------------------------------------ cache and toolchain

  private FileResult readCache(Path source, Path cached) throws IOException {
    JsonObject json = Workspace.readJson(cached);
    List<ClassResult> classes = new ArrayList<>();
    for (JsonElement element : json.getAsJsonArray("classes")) {
      JsonObject object = element.getAsJsonObject();
      Map<String, Boolean> flags = new LinkedHashMap<>();
      object.getAsJsonObject("flags").entrySet()
        .forEach(e -> flags.put(e.getKey(), e.getValue().getAsBoolean()));
      List<String> details = new ArrayList<>();
      object.getAsJsonArray("details").forEach(d -> details.add(d.getAsString()));
      classes.add(new ClassResult(object.get("name").getAsString(), flags, details,
        object.get("compiled").getAsBoolean(),
        object.has("extra") && object.get("extra").getAsBoolean()));
    }
    List<String> errors = new ArrayList<>();
    if (json.has("errors")) {
      json.getAsJsonArray("errors").forEach(e -> errors.add(e.getAsString()));
    }
    Metrics metrics = Metrics.ZERO;
    if (json.has("metrics")) {
      JsonObject object = json.getAsJsonObject("metrics");
      metrics = new Metrics(intOf(object, "raw"), intOf(object, "redundantCasts"),
        intOf(object, "unchecked"), intOf(object, "doubleCasts"));
    }
    return new FileResult(source.toString(), classes, errors, true, metrics);
  }

  private static int intOf(JsonObject object, String key) {
    return object.has(key) ? object.get(key).getAsInt() : 0;
  }

  private void writeCache(Path cached, FileResult result) throws IOException {
    JsonObject json = new JsonObject();
    JsonArray classes = new JsonArray();
    for (ClassResult cls : result.classes()) {
      JsonObject object = new JsonObject();
      object.addProperty("name", cls.name());
      object.addProperty("compiled", cls.compiled());
      object.addProperty("extra", cls.extra());
      JsonObject flags = new JsonObject();
      cls.flags().forEach(flags::addProperty);
      object.add("flags", flags);
      JsonArray details = new JsonArray();
      cls.details().forEach(details::add);
      object.add("details", details);
      classes.add(object);
    }
    json.add("classes", classes);
    JsonArray errors = new JsonArray();
    result.errors().forEach(errors::add);
    json.add("errors", errors);
    JsonObject metrics = new JsonObject();
    metrics.addProperty("raw", result.metrics().raw());
    metrics.addProperty("redundantCasts", result.metrics().redundantCasts());
    metrics.addProperty("unchecked", result.metrics().unchecked());
    metrics.addProperty("doubleCasts", result.metrics().doubleCasts());
    json.add("metrics", metrics);
    Workspace.writeJson(cached, json);
  }

  private String stamp(Path client, List<Path> classpath, int release) throws IOException {
    StringBuilder libs = new StringBuilder();
    for (Path lib : classpath) {
      if (lib.getFileName().toString().equals("client.jar")) {
        continue;
      }
      libs.append(lib.getFileName()).append(':').append(Files.size(lib)).append(';');
    }
    return Workspace.sha256(COMPARATOR_VERSION + "|" + System.getProperty("java.version") + "|"
      + System.getProperty("java.home") + "|" + release + "|" + Workspace.sha256(client) + "|"
      + Workspace.sha256(libs.toString()));
  }

  static int releaseOf(Path jar) throws IOException {
    try (ZipFile zip = new ZipFile(jar.toFile())) {
      var entries = zip.entries();
      while (entries.hasMoreElements()) {
        var entry = entries.nextElement();
        if (entry.getName().endsWith(".class") && !entry.getName().contains("META-INF")) {
          try (var in = zip.getInputStream(entry)) {
            byte[] header = in.readNBytes(8);
            int major = ((header[6] & 0xFF) << 8) | (header[7] & 0xFF);
            return major - 44;
          }
        }
      }
    }
    throw new IOException("no classes in " + jar);
  }

  private static String join(List<Path> paths) {
    StringBuilder builder = new StringBuilder();
    for (Path path : paths) {
      if (builder.length() > 0) {
        builder.append(java.io.File.pathSeparatorChar);
      }
      builder.append(path);
    }
    return builder.toString();
  }
}

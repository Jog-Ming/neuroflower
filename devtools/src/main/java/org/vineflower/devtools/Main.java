package org.vineflower.devtools;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * The experimental pipeline's entry point. See ./nf for the wrapper.
 *
 * <pre>
 *   versions [--refresh]
 *   download  &lt;version&gt; [--refresh]
 *   decompile &lt;version&gt; [--refresh] [--threads N] [--only Class] [--keep N]
 *   tree      &lt;version&gt; [--only Class]
 *   score     &lt;version&gt; [--refresh] [--only Class] [--threads N] [--json]
 *   class     &lt;version&gt; &lt;Class&gt;
 *   clean     [--trees] [--downloads] [--all] [--keep N]
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
    Decompiler decompiler = new Decompiler(workspace, minecraft);
    String command = args[0];
    List<String> rest = List.of(args).subList(1, args.length);

    switch (command) {
      case "versions" -> {
        boolean refresh = rest.contains("--refresh");
        for (String id : minecraft.versionIds(refresh)) {
          System.out.println(id);
        }
      }
      case "download" -> {
        String version = positional(rest);
        boolean refresh = rest.contains("--refresh");
        Path client = minecraft.clientJar(version, refresh);
        List<Path> libs = minecraft.libraries(version, refresh);
        System.out.println("client: " + client);
        System.out.println("libs:   " + libs.size() + " jars under " + client.getParent().resolve("libs"));
      }
      case "decompile" -> {
        String version = positional(rest);
        int threads = intFlag(rest, "--threads", Math.max(1, Runtime.getRuntime().availableProcessors()));
        int keep = intFlag(rest, "--keep", 3);
        String only = stringFlag(rest, "--only", null);
        boolean refresh = rest.contains("--refresh");
        Path tree = decompiler.tree(version, threads, refresh, only, keep);
        System.out.println(tree);
      }
      case "tree" -> {
        String version = positional(rest);
        String only = stringFlag(rest, "--only", null);
        System.out.println(decompiler.tree(version, threadsDefault(), false, only, 3));
      }
      case "score" -> {
        String version = positional(rest);
        boolean refresh = rest.contains("--refresh");
        String only = stringFlag(rest, "--only", null);
        int threads = intFlag(rest, "--threads", threadsDefault());
        boolean json = rest.contains("--json");
        Path tree = decompiler.tree(version, threads, refresh, only, 3);
        new Verifier(workspace, minecraft).score(version, tree, only, threads, json);
      }
      case "class" -> {
        String version = rest.get(0);
        String name = rest.get(1);
        Path source = decompiler.subsetSource(version, name, threadsDefault());
        new Verifier(workspace, minecraft).score(version, source, null, 1, false);
      }
      case "reports" -> reports(workspace, rest);
      case "clean" -> clean(workspace, rest);
      case "cache" -> cache(workspace);
      default -> usage();
    }
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
    int keep = intFlag(flags, "--keep", 0);
    if (all) {
      Decompiler.delete(workspace.dev);
      System.out.println("removed " + workspace.dev);
      return;
    }
    if (trees) {
      new Decompiler(workspace, new Minecraft(workspace)).prune(keep);
      System.out.println("pruned trees, kept " + keep);
    }
    if (compile) {
      Decompiler.delete(workspace.cache.resolve("compile"));
      System.out.println("removed compile cache");
    }
    if (downloads) {
      Decompiler.delete(workspace.versions);
      System.out.println("removed " + workspace.versions);
    }
  }

  private static void cache(Workspace workspace) throws Exception {
    System.out.println("cache root: " + workspace.cache);
    if (Files.isDirectory(workspace.versions)) {
      try (var list = Files.list(workspace.versions)) {
        System.out.println("versions: " + list.count());
      }
    }
    if (Files.isDirectory(workspace.trees)) {
      try (var list = Files.list(workspace.trees)) {
        System.out.println("trees: " + list.count());
      }
    }
  }

  private static int threadsDefault() {
    return Math.max(1, Runtime.getRuntime().availableProcessors());
  }

  private static String positional(List<String> args) {
    for (String arg : args) {
      if (!arg.startsWith("--")) {
        return arg;
      }
    }
    throw new IllegalArgumentException("missing version");
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

  private static void usage() {
    System.out.println("""
      usage: nf <command> [options]

        versions [--refresh]                  list Mojang's versions
        download  <version> [--refresh]       cache the client jar and libraries
        decompile <version> [--refresh] [--threads N] [--only Class] [--keep N]
        tree      <version> [--only Class]    print the cached tree path
        score     <version> [--refresh] [--only Class] [--threads N] [--json]
        class     <version> <Class>           decompile, compile and report one class
        clean     [--trees] [--compile] [--downloads] [--all] [--keep N]
        reports   [--version V] [--limit N]   list past scores
        cache                                 show cache contents
      """);
  }

  private Main() {
  }
}

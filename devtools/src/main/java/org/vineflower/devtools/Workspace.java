package org.vineflower.devtools;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HexFormat;

/** Paths and small file helpers for the experimental pipeline. Everything lives under .dev/. */
public final class Workspace {
  public static final Gson GSON = new GsonBuilder().setPrettyPrinting().create();
  public static final Gson COMPACT = new Gson();

  public final Path root;
  public final Path dev;
  public final Path cache;
  public final Path versions;
  public final Path trees;
  public final Path reports;
  public final Path tmp;

  public Workspace(Path root) {
    this.root = root;
    this.dev = root.resolve(".dev");
    this.cache = dev.resolve("cache");
    this.versions = cache.resolve("versions");
    this.trees = cache.resolve("trees");
    this.reports = dev.resolve("reports");
    this.tmp = dev.resolve("tmp");
  }

  public static Workspace load() {
    String root = System.getenv("DEVTOOLS_ROOT");
    return new Workspace(Path.of(root == null ? System.getProperty("user.dir") : root));
  }

  /**
   * The Vineflower fork jar a decompile runs: this build by default, or the one named by
   * {@code DECOMPILER_JAR} for a deliberate A/B against another build. The tree cache keys on the
   * jar's hash, so two builds never share a tree. This is the decompiler, not the devtools jar.
   */
  public Path devJar() {
    String override = System.getenv("DECOMPILER_JAR");
    if (override != null && !override.isBlank()) {
      return Path.of(override);
    }
    return root.resolve("build/libs/vineflower-1.13.0+local.jar");
  }

  public static String sha256(Path path) {
    try (var in = Files.newInputStream(path)) {
      MessageDigest digest = MessageDigest.getInstance("SHA-256");
      byte[] buffer = new byte[1 << 16];
      int read;
      while ((read = in.read(buffer)) > 0) {
        digest.update(buffer, 0, read);
      }
      return HexFormat.of().formatHex(digest.digest());
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    } catch (NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  public static String sha256(byte[] bytes) {
    try {
      return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(bytes));
    } catch (NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  public static String sha256(String text) {
    try {
      return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256")
        .digest(text.getBytes(StandardCharsets.UTF_8)));
    } catch (NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  /** Writes a file through a temporary sibling and an atomic rename. */
  public static void write(Path target, byte[] bytes) throws IOException {
    Files.createDirectories(target.getParent());
    // Several versions are scored in parallel processes, and two of them touch the same marker
    // files. A shared temporary name lets one process move the other's file away mid-write, which
    // Windows reports as an access denial on the rename.
    Path temp = target.resolveSibling(target.getFileName() + ".tmp-"
      + ProcessHandle.current().pid() + "-" + java.util.UUID.randomUUID());
    Files.write(temp, bytes);
    try {
      Files.move(temp, target, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
    } catch (IOException e) {
      try {
        Files.move(temp, target, StandardCopyOption.REPLACE_EXISTING);
      } catch (IOException again) {
        Files.deleteIfExists(temp);
        throw again;
      }
    }
  }

  public static void write(Path target, String text) throws IOException {
    write(target, text.getBytes(StandardCharsets.UTF_8));
  }

  public static JsonObject readJson(Path path) throws IOException {
    return JsonParser.parseString(Files.readString(path, StandardCharsets.UTF_8)).getAsJsonObject();
  }

  public static void writeJson(Path target, JsonObject json) throws IOException {
    write(target, GSON.toJson(json) + "\n");
  }
}

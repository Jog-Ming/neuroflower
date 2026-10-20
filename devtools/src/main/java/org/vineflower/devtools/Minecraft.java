package org.vineflower.devtools;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.HexFormat;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.stream.Stream;

/**
 * Resolves, downloads and caches a Minecraft version's client jar and libraries.
 *
 * Three sources, in order: the experimental unobfuscated builds that Mojang ships outside the
 * manifest (a fixed object URL each), Mojang's own manifest (26.1 and later are not obfuscated),
 * and the skyrising/mc-versions list, which tracks the unobfuscated builds. A {@code _unobfuscated}
 * build has no metadata of its own, so its libraries come from the release it belongs to.
 */
public final class Minecraft {
  private static final String MOJANG_MANIFEST = "https://piston-meta.mojang.com/mc/game/version_manifest_v2.json";
  private static final String SKYRISING_MANIFEST =
    "https://raw.githubusercontent.com/skyrising/mc-versions/master/data/version_manifest.json";
  private static final Duration MAX_AGE = Duration.ofHours(24);

  /** Builds Mojang ships without obfuscation but does not list in its manifest. */
  /** Compile-time-only annotations Minecraft's own metadata does not list. */
  private static final String[][] COMMON_LIBRARIES = {
    {"jsr305-3.0.2.jar", "https://repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2/jsr305-3.0.2.jar"},
    {"annotations-24.0.0.jar", "https://repo1.maven.org/maven2/org/jetbrains/annotations/24.0.0/annotations-24.0.0.jar"},
    {"jspecify-1.0.0.jar", "https://repo1.maven.org/maven2/org/jspecify/jspecify/1.0.0/jspecify-1.0.0.jar"},
  };

  private static final Map<String, String> UNOBFUSCATED_CLIENTS = Map.of(
    "1.21.11_unobfuscated",
    "https://piston-data.mojang.com/v1/objects/4509ee9b65f226be61142d37bf05f8d28b03417b/client.jar");

  public record VersionData(String clientUrl, String clientSha1, String libraryBase, JsonObject mojang) {
  }

  private final Workspace workspace;
  private final HttpClient http = HttpClient.newBuilder()
    .followRedirects(HttpClient.Redirect.NORMAL)
    .connectTimeout(Duration.ofSeconds(30))
    .build();

  public Minecraft(Workspace workspace) {
    this.workspace = workspace;
  }

  public VersionData resolve(String version, boolean refresh) throws IOException, InterruptedException {
    String known = UNOBFUSCATED_CLIENTS.get(version);
    if (known != null) {
      return new VersionData(known, null, baseRelease(version), null);
    }
    JsonObject mojang = findMojang(version, refresh);
    if (mojang != null) {
      JsonObject client = mojang.getAsJsonObject("downloads").getAsJsonObject("client");
      return new VersionData(client.get("url").getAsString(), client.get("sha1").getAsString(), version, mojang);
    }
    JsonObject skyrising = findSkyrising(version, refresh);
    if (skyrising != null) {
      JsonObject client = skyrising.getAsJsonObject("downloads").getAsJsonObject("client");
      return new VersionData(client.get("url").getAsString(), client.get("sha1").getAsString(),
        baseRelease(version), null);
    }
    throw new IllegalArgumentException("unknown version '" + version + "' (not in Mojang's manifest or "
      + "the mc-versions list)");
  }

  private static String baseRelease(String version) {
    return version.endsWith("_unobfuscated") ? version.substring(0, version.length() - "_unobfuscated".length())
      : version;
  }

  public Path clientJar(String version, boolean refresh) throws IOException, InterruptedException {
    VersionData data = resolve(version, refresh);
    Path jar = workspace.versions.resolve(version).resolve("client.jar");
    if (refresh || !Files.exists(jar)) {
      System.err.println("fetching client jar for " + version);
    }
    download(data.clientUrl(), data.clientSha1(), jar, refresh);
    return jar;
  }

  /** The version's metadata: its own, or the base release's for a {@code _unobfuscated} build. */
  public JsonObject versionJson(String version, boolean refresh) throws IOException, InterruptedException {
    VersionData data = resolve(version, refresh);
    if (data.mojang() != null) {
      return data.mojang();
    }
    JsonObject base = findMojang(data.libraryBase(), refresh);
    if (base == null) {
      throw new IOException("no metadata for base release " + data.libraryBase());
    }
    JsonObject synthetic = base.deepCopy();
    synthetic.addProperty("id", version);
    return synthetic;
  }

  public List<Path> libraries(String version, boolean refresh) throws IOException, InterruptedException {
    JsonObject metadata = versionJson(version, refresh);
    Path libs = workspace.versions.resolve(version).resolve("libs");
    List<JsonObject> artifacts = new ArrayList<>();
    if (metadata.has("libraries")) {
      for (JsonElement entry : metadata.getAsJsonArray("libraries")) {
        JsonObject library = entry.getAsJsonObject();
        // No OS filter: the compile classpath needs every platform's jar, because source files
        // reference classes that only exist on other platforms (ca.weblite.objc on macOS).
        JsonObject downloads = library.getAsJsonObject("downloads");
        if (downloads != null && downloads.has("artifact")) {
          artifacts.add(downloads.getAsJsonObject("artifact"));
        }
      }
    }
    long missing = artifacts.stream().filter(a -> {
      Path target = libs.resolve(a.get("path").getAsString());
      try {
        return !Files.exists(target) || !a.get("sha1").getAsString().equals(sha1(target));
      } catch (IOException e) {
        return true;
      }
    }).count();
    if (missing > 0) {
      System.err.println("fetching " + missing + " libraries into " + libs);
    }
    ExecutorService pool = Executors.newFixedThreadPool(Math.min(8, Math.max(1, artifacts.size())));
    try {
      List<Future<?>> futures = new ArrayList<>();
      for (JsonObject artifact : artifacts) {
        futures.add(pool.submit(() -> {
          try {
            download(artifact.get("url").getAsString(), artifact.get("sha1").getAsString(),
              libs.resolve(artifact.get("path").getAsString()), refresh);
          } catch (IOException | InterruptedException e) {
            throw new RuntimeException(e);
          }
          return null;
        }));
      }
      for (Future<?> future : futures) {
        try {
          future.get();
        } catch (Exception e) {
          throw new IOException("library download failed", e);
        }
      }
    } finally {
      pool.shutdown();
    }
    try (Stream<Path> walk = Files.walk(libs)) {
      return walk.filter(p -> p.toString().endsWith(".jar")).sorted().toList();
    }
  }

  /**
   * The client jar's classes extracted once into the cache. Reading 9436 small files is much cheaper
   * than opening the 37&nbsp;MB jar for every source file, and the extraction is keyed by the jar's
   * hash so a changed download re-extracts.
   */
  public Path extractedClasses(String version, boolean refresh) throws IOException, InterruptedException {
    Path jar = clientJar(version, refresh);
    Path dir = workspace.versions.resolve(version).resolve("classes");
    Path stamp = dir.resolve(".stamp");
    String hash = Workspace.sha256(jar);
    if (!refresh && Files.exists(stamp) && Files.readString(stamp).trim().equals(hash)) {
      return dir;
    }
    Decompiler.delete(dir);
    Files.createDirectories(dir);
    try (var zip = new java.util.zip.ZipFile(jar.toFile())) {
      for (var entry : java.util.Collections.list(zip.entries())) {
        String name = entry.getName();
        if (!name.endsWith(".class") || name.startsWith("META-INF/")) {
          continue;
        }
        Path target = dir.resolve(name);
        Files.createDirectories(target.getParent());
        try (var in = zip.getInputStream(entry)) {
          Files.write(target, in.readAllBytes());
        }
      }
    }
    Files.writeString(stamp, hash);
    return dir;
  }

  public List<Path> classpath(String version, boolean refresh) throws IOException, InterruptedException {
    List<Path> cp = new ArrayList<>();
    cp.add(clientJar(version, refresh));
    cp.addAll(libraries(version, refresh));
    cp.addAll(commonLibraries(refresh));
    return cp;
  }

  private List<Path> commonLibraries(boolean refresh) throws IOException, InterruptedException {
    Path dir = workspace.cache.resolve("common");
    List<Path> paths = new ArrayList<>();
    for (String[] library : COMMON_LIBRARIES) {
      Path path = dir.resolve(library[0]);
      download(library[1], null, path, refresh);
      paths.add(path);
    }
    return paths;
  }

  /** Every version either source knows, Mojang's first. */
  public List<String> versionIds(boolean refresh) throws IOException, InterruptedException {
    Set<String> ids = new LinkedHashSet<>(UNOBFUSCATED_CLIENTS.keySet());
    JsonObject mojang = manifest(MOJANG_MANIFEST, workspace.versions.resolve("manifest.json"), refresh);
    for (JsonElement element : mojang.getAsJsonArray("versions")) {
      ids.add(element.getAsJsonObject().get("id").getAsString());
    }
    try {
      JsonObject sky = manifest(SKYRISING_MANIFEST, workspace.versions.resolve("mc-versions.json"), refresh);
      for (JsonElement element : sky.getAsJsonArray("versions")) {
        ids.add(element.getAsJsonObject().get("id").getAsString());
      }
    } catch (IOException ignored) {
      // The skyrising list is a convenience; its absence must not hide Mojang's versions.
    }
    return new ArrayList<>(ids);
  }

  // ------------------------------------------------------------------ sources

  private JsonObject findMojang(String id, boolean refresh) throws IOException, InterruptedException {
    JsonObject manifest = manifest(MOJANG_MANIFEST, workspace.versions.resolve("manifest.json"), refresh);
    for (JsonElement element : manifest.getAsJsonArray("versions")) {
      JsonObject entry = element.getAsJsonObject();
      if (entry.get("id").getAsString().equals(id)) {
        Path path = workspace.versions.resolve(id).resolve(id + ".json");
        if (refresh || !Files.exists(path)) {
          Workspace.writeJson(path, fetchJson(entry.get("url").getAsString()));
        }
        return Workspace.readJson(path);
      }
    }
    return null;
  }

  private JsonObject findSkyrising(String id, boolean refresh) throws IOException, InterruptedException {
    JsonObject manifest = manifest(SKYRISING_MANIFEST, workspace.versions.resolve("mc-versions.json"), refresh);
    for (JsonElement element : manifest.getAsJsonArray("versions")) {
      JsonObject entry = element.getAsJsonObject();
      if (entry.get("id").getAsString().equals(id)) {
        Path path = workspace.versions.resolve(id).resolve(id + ".json");
        if (refresh || !Files.exists(path)) {
          Workspace.writeJson(path, fetchJson(
            "https://raw.githubusercontent.com/skyrising/mc-versions/master/data/"
              + entry.get("url").getAsString()));
        }
        return Workspace.readJson(path);
      }
    }
    return null;
  }

  private JsonObject manifest(String url, Path cache, boolean refresh) throws IOException, InterruptedException {
    if (!refresh && Files.exists(cache)
      && Files.getLastModifiedTime(cache).toInstant().isAfter(Instant.now().minus(MAX_AGE))) {
      return Workspace.readJson(cache);
    }
    JsonObject json = fetchJson(url);
    Workspace.writeJson(cache, json);
    return json;
  }

  private static boolean allowed(JsonObject library) {
    if (!library.has("rules")) {
      return true;
    }
    // The launcher's rule evaluation: the last matching rule decides; allow if none matched.
    boolean allow = false;
    for (JsonElement element : library.getAsJsonArray("rules")) {
      JsonObject rule = element.getAsJsonObject();
      JsonObject os = rule.getAsJsonObject("os");
      boolean matches = os == null || (os.has("name") && os.get("name").getAsString().equals("windows"));
      if (matches) {
        allow = "allow".equals(rule.get("action").getAsString());
      }
    }
    return allow;
  }

  // ------------------------------------------------------------------ transfer

  private void download(String url, String sha1, Path target, boolean refresh)
    throws IOException, InterruptedException {
    if (!refresh && Files.exists(target) && (sha1 == null || sha1.equals(sha1(target)))) {
      return;
    }
    Files.createDirectories(target.getParent());
    Path temp = target.resolveSibling(target.getFileName() + ".download");
    HttpRequest request = HttpRequest.newBuilder(URI.create(url)).timeout(Duration.ofMinutes(10)).build();
    HttpResponse<InputStream> response = http.send(request, HttpResponse.BodyHandlers.ofInputStream());
    if (response.statusCode() != 200) {
      throw new IOException("HTTP " + response.statusCode() + " for " + url);
    }
    try (InputStream in = response.body()) {
      Files.copy(in, temp, java.nio.file.StandardCopyOption.REPLACE_EXISTING);
    }
    if (sha1 != null) {
      String actual = sha1(temp);
      if (!sha1.equals(actual)) {
        Files.deleteIfExists(temp);
        throw new IOException("SHA-1 mismatch for " + target.getFileName() + ": " + actual);
      }
    }
    Files.move(temp, target, java.nio.file.StandardCopyOption.REPLACE_EXISTING,
      java.nio.file.StandardCopyOption.ATOMIC_MOVE);
  }

  private JsonObject fetchJson(String url) throws IOException, InterruptedException {
    HttpRequest request = HttpRequest.newBuilder(URI.create(url)).timeout(Duration.ofSeconds(30)).build();
    HttpResponse<String> response = http.send(request, HttpResponse.BodyHandlers.ofString());
    if (response.statusCode() != 200) {
      throw new IOException("HTTP " + response.statusCode() + " for " + url);
    }
    return com.google.gson.JsonParser.parseString(response.body()).getAsJsonObject();
  }

  private static String sha1(Path path) throws IOException {
    try (InputStream in = Files.newInputStream(path)) {
      MessageDigest digest = MessageDigest.getInstance("SHA-1");
      byte[] buffer = new byte[1 << 16];
      int read;
      while ((read = in.read(buffer)) > 0) {
        digest.update(buffer, 0, read);
      }
      return HexFormat.of().formatHex(digest.digest());
    } catch (java.security.NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }
}

package org.vineflower.devtools;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.BufferedWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Writes the training corpus for the repair model: one JSON line per class that pairs the
 * decompiled source file with the ground-truth source file and records what the verifier said about
 * each attribute. Paths are references, not copies; the tree lives in the cache and the ground truth
 * tree is the user's.
 */
public final class Corpus {
  private Corpus() {
  }

  public static Path write(Path corpusRoot, String version, Path tree, Path groundTruth,
                           List<Verifier.FileResult> results) throws Exception {
    Path dir = corpusRoot.resolve(version);
    Files.createDirectories(dir);
    Path manifest = dir.resolve("manifest.jsonl");
    try (BufferedWriter out = Files.newBufferedWriter(manifest, StandardCharsets.UTF_8)) {
      for (Verifier.FileResult result : results) {
        Path source = Path.of(result.source()).toAbsolutePath().normalize();
        String relative = tree.toAbsolutePath().normalize().relativize(source).toString().replace('\\', '/');
        Path target = groundTruth.resolve("src/main/java").resolve(relative);
        for (Verifier.ClassResult cls : result.classes()) {
          JsonObject entry = new JsonObject();
          entry.addProperty("version", version);
          entry.addProperty("class", cls.name());
          entry.addProperty("source", source.toString());
          entry.addProperty("sourceRelative", relative);
          entry.addProperty("target", Files.exists(target) ? target.toString() : null);
          entry.addProperty("compiled", cls.compiled());
          entry.addProperty("extra", cls.extra());
          JsonObject flags = new JsonObject();
          cls.flags().forEach(flags::addProperty);
          entry.add("flags", flags);
          JsonArray details = new JsonArray();
          cls.details().forEach(details::add);
          entry.add("details", details);
          JsonArray errors = new JsonArray();
          result.errors().forEach(errors::add);
          entry.add("errors", errors);
          out.write(Workspace.COMPACT.toJson(entry));
          out.write('\n');
        }
      }
    }
    return manifest;
  }
}

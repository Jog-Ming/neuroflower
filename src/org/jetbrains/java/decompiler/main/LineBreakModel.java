// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

/**
 * Inference side of the line-start model trained by {@code ml/train_linebreak.py}.
 *
 * <p>The weights are a TSV of feature tab weight, so no JSON dependency is needed. The feature
 * names must match the training script exactly: instruction categories of the previous and the
 * current instruction, their pair, a position bucket and the length of the run of instructions
 * already on this printed line. The model does not replace the target's line table; it reports
 * which instructions should start a line, and LineAlign logs its agreement with the table when
 * {@code NEUROFLOWER_ML_BREAKS} is set. Wiring it into a line-breaking decision waits for token-level
 * offset maps, which the printer does not record yet.
 */
public final class LineBreakModel {
  private static LineBreakModel instance;
  private static boolean loaded;

  private final Map<String, Double> weights;
  private final double bias;

  private LineBreakModel(Map<String, Double> weights) {
    this.weights = weights;
    this.bias = weights.getOrDefault("bias", 0.0);
  }

  /** The model when one is configured with {@code NEUROFLOWER_LINEBREAK_WEIGHTS}, else null. */
  public static synchronized LineBreakModel current() {
    if (!loaded) {
      loaded = true;
      String path = System.getenv("NEUROFLOWER_LINEBREAK_WEIGHTS");
      if (path != null && !path.isEmpty()) {
        instance = load(Path.of(path));
      }
    }
    return instance;
  }

  private static LineBreakModel load(Path path) {
    if (!Files.isRegularFile(path)) {
      return null;
    }
    Map<String, Double> weights = new HashMap<>();
    try {
      for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
        int tab = line.indexOf('\t');
        if (tab > 0) {
          weights.put(line.substring(0, tab), Double.parseDouble(line.substring(tab + 1)));
        }
      }
    } catch (IOException | NumberFormatException e) {
      return null;
    }
    return weights.isEmpty() ? null : new LineBreakModel(weights);
  }

  /** True when the model expects the current instruction to start a new source line. */
  public boolean startsLine(String previousOp, String currentOp, int index, int length, int run) {
    String previous = category(previousOp);
    String current = category(currentOp);
    int bucket = Math.min(7, index * 8 / Math.max(1, length));
    int runBucket = Math.min(3, run);
    double z = bias
      + weights.getOrDefault("p:" + previous, 0.0)
      + weights.getOrDefault("c:" + current, 0.0)
      + weights.getOrDefault("pc:" + previous + "|" + current, 0.0)
      + weights.getOrDefault("i:" + bucket, 0.0)
      + weights.getOrDefault("r:" + runBucket, 0.0);
    return z > 0;
  }

  /** The instruction an offset belongs to, as the dataset names it ('op:N' or a pool name). */
  static String opName(StructMethod method, int offset) {
    FullInstructionSequence code = method.getInstructionSequence();
    if (code == null) {
      return "op";
    }
    for (Instruction instruction : code) {
      if (instruction.startOffset == offset) {
        return "op:" + instruction.opcode;
      }
    }
    return "op";
  }

  private static String category(String op) {
    if (op == null) {
      return "op";
    }
    if (op.startsWith("op:")) {
      int code;
      try {
        code = Integer.parseInt(op.substring(3));
      } catch (NumberFormatException e) {
        return "op";
      }
      if (code >= 172 && code <= 177) {
        return "return";
      }
      if (code >= 153 && code <= 166 || code == 167 || code == 198 || code == 199) {
        return "branch";
      }
      if (code >= 59 && code <= 81 || code >= 182 && code <= 195) {
        return "invoke/new";
      }
      if (code >= 178 && code <= 181) {
        return "field";
      }
      if (code >= 21 && code <= 53) {
        return "var";
      }
      if (code >= 2 && code <= 15 || code == 18 || code == 20) {
        return "const";
      }
      if (code >= 83 && code <= 132) {
        return "array";
      }
      return "op";
    }
    if (op.startsWith("type:")) {
      return "type";
    }
    if (op.startsWith("const:")) {
      return "const";
    }
    return "name";
  }
}

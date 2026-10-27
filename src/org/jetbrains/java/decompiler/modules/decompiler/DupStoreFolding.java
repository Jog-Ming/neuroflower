// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The value an assignment expression hands to the surrounding expression.
 *
 * <p>javac compiles {@code bounds(x, topPos += spacing, y, z)} as the argument's value followed by
 * {@code dup; istore topPos}: the duplicate on the operand stack and the local both receive the
 * new value, so the local and the stack copy are one variable version. The decompiler keeps the
 * stack copy as a synthetic stack variable, which prints as a name of its own —
 * {@code var6 = topPos + spacing} inside the call — and the store to the local disappears.
 *
 * <p>The class file proves the identity: the last instruction of the synthetic value's definition
 * is a {@code dup} whose successor stores into slot N, and N has an LVT entry — a source-named
 * local. Every read of the synthetic value also sits after that store and before any later store
 * to N, so each one reads exactly what the local holds. Rewriting the definition's target and its
 * reads to that local restores {@code topPos += spacing} in argument position and leaves the
 * synthetic variable unreferenced.
 */
public final class DupStoreFolding {
  private DupStoreFolding() {
  }

  public static boolean fold(Statement root, StructMethod method) {
    if (method == null || !RoundTrip.enabled() || !RoundTrip.selector("dupstore")) {
      return false;
    }
    Uses uses = new Uses();
    collect(root, uses);
    if (uses.byIndex.isEmpty()) {
      return false;
    }

    List<Runnable> rewrites = new ArrayList<>();
    for (Map.Entry<Integer, List<Use>> entry : uses.byIndex.entrySet()) {
      List<Use> occurrences = entry.getValue();
      Use write = null;
      boolean multipleWrites = false;
      for (Use use : occurrences) {
        if (use.write) {
          if (write != null) {
            multipleWrites = true;
            break;
          }
          write = use;
        }
      }
      if (multipleWrites || write == null || write.topLevel) {
        continue;
      }
      VarExprent value = write.var;
      int store = RoundTrip.lastInstructionStart(value.bytecode, method);
      int slot = RoundTrip.dupStoreSlot(method, store);
      if (store < 0 || slot < 0 || value.getLVT() != null
        || value.getProcessor() == null
        || value.getProcessor().getVarOriginalIndex(value.getIndex()) == null
        || value.getProcessor().getVarOriginalIndex(value.getIndex()) != slot) {
        continue;
      }
      VarExprent local = uses.localFor(slot, value.getVarType());
      if (local == null) {
        continue;
      }
      // Every read has to happen after the store and before the slot is written again, or the
      // local no longer holds the value the assignment expression produced.
      boolean usable = true;
      for (Use use : occurrences) {
        if (use == write) {
          continue;
        }
        int first = use.var.bytecode == null ? -1 : use.var.bytecode.nextSetBit(0);
        int last = use.var.bytecode == null ? -1 : use.var.bytecode.previousSetBit(Integer.MAX_VALUE);
        if (first < 0 || first <= store || RoundTrip.storedIn(method, slot, store, last)) {
          usable = false;
          break;
        }
      }
      if (!usable) {
        continue;
      }
      AssignmentExprent assignment = (AssignmentExprent)write.parent;
      Use writeUse = write;
      rewrites.add(() -> {
        assignment.replaceExprent(value, localCopy(local, value));
        for (Use use : occurrences) {
          if (use == writeUse || use.parent == null) {
            continue;
          }
          use.parent.replaceExprent(use.var, localCopy(local, use.var));
        }
      });
    }

    for (Runnable rewrite : rewrites) {
      rewrite.run();
    }
    return !rewrites.isEmpty();
  }

  private static VarExprent localCopy(VarExprent local, VarExprent replaced) {
    VarExprent copy = (VarExprent)local.copy();
    copy.setDefinition(false);
    if (replaced.bytecode != null) {
      copy.addBytecodeOffsets(replaced.bytecode);
    }
    return copy;
  }

  private static final class Use {
    final Exprent parent;
    final VarExprent var;
    final boolean write;
    final boolean topLevel;

    Use(Exprent parent, VarExprent var, boolean write, boolean topLevel) {
      this.parent = parent;
      this.var = var;
      this.write = write;
      this.topLevel = topLevel;
    }
  }

  private static final class Uses {
    final Map<Integer, List<Use>> byIndex = new HashMap<>();
    final List<VarExprent> all = new ArrayList<>();

    void add(Exprent parent, VarExprent var, boolean topLevel) {
      boolean write = parent instanceof AssignmentExprent assignment && assignment.getLeft() == var;
      byIndex.computeIfAbsent(var.getIndex(), k -> new ArrayList<>()).add(new Use(parent, var, write, topLevel));
      all.add(var);
    }

    /**
     * A printed occurrence of the source variable in this slot: one that carries an LVT entry for
     * the slot, else the base variable — the version that keeps the slot's own index and therefore
     * the parameter or local name.
     */
    VarExprent localFor(int slot, org.jetbrains.java.decompiler.struct.gen.VarType type) {
      VarExprent base = null;
      for (VarExprent var : all) {
        if (!type.equals(var.getVarType()) || var.getProcessor() == null) {
          continue;
        }
        LocalVariable lvt = var.getLVT();
        if (lvt != null && lvt.getVersion().var == slot) {
          return var;
        }
        if (base == null && var.getIndex() == slot) {
          base = var;
        }
      }
      return base;
    }
  }

  private static void collect(Statement stat, Uses uses) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent != null) {
          collect(exprent, uses, true);
        }
      }
    }
    for (Exprent exprent : stat.getStatExprents()) {
      if (exprent != null) {
        collect(exprent, uses, true);
      }
    }
    for (Statement child : stat.getStats()) {
      collect(child, uses);
    }
  }

  private static void collect(Exprent exprent, Uses uses, boolean topLevel) {
    for (Exprent child : exprent.getAllExprents()) {
      if (child == null) {
        continue;
      }
      if (child instanceof VarExprent var) {
        uses.add(exprent, var, topLevel);
      }
      collect(child, uses, false);
    }
  }
}

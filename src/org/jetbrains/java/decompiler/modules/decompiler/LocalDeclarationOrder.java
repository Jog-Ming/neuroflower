// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

import java.util.List;

/**
 * javac allocates local slots in declaration order. A source that declares a variable without an
 * initializer before another local's declaration still gives it the lower slot, even though our
 * printer emits the bare declaration at its first assignment. The target's LocalVariableTable is
 * the evidence: when a bare declaration sits after a declaration whose slot is higher, the source
 * must have written it earlier. Moving the bare declaration left within its exprent list only
 * reorders declarations and never moves an initializer, so evaluation order is unchanged.
 */
public final class LocalDeclarationOrder {
  private LocalDeclarationOrder() {
  }

  public static void reorder(Statement root) {
    reorderStat(root);
  }

  private static void reorderStat(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (int i = 1; i < exprents.size(); i++) {
        Exprent exprent = exprents.get(i);
        int slot = bareDeclarationSlot(exprent);
        if (slot < 0) {
          continue;
        }
        int j = i;
        while (j > 0) {
          Exprent previous = exprents.get(j - 1);
          int previousSlot = declarationSlot(previous);
          if (previousSlot < 0 || previousSlot <= slot) {
            break;
          }
          exprents.set(j, previous);
          exprents.set(j - 1, exprent);
          j--;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      reorderStat(child);
    }
  }

  /** The slot of a declaration statement that only names a variable, or -1. */
  private static int bareDeclarationSlot(Exprent exprent) {
    if (exprent instanceof VarExprent var && isRealDefinition(var)) {
      return slotOf(var);
    }
    return -1;
  }

  /** The slot of a bare or initialized declaration statement, or -1 for any other exprent. */
  private static int declarationSlot(Exprent exprent) {
    if (exprent instanceof VarExprent var && isRealDefinition(var)) {
      return slotOf(var);
    }
    if (exprent instanceof AssignmentExprent assignment
      && assignment.getLeft() instanceof VarExprent var && isRealDefinition(var)) {
      return slotOf(var);
    }
    return -1;
  }

  private static boolean isRealDefinition(VarExprent var) {
    return var.isDefinition() && !var.isStack();
  }

  private static int slotOf(VarExprent var) {
    LocalVariable lvt = var.getLVT();
    return lvt == null ? -1 : lvt.getVersion().var;
  }
}

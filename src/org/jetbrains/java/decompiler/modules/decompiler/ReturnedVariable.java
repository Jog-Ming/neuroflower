// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarTypeProcessor.FinalType;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

import java.util.List;

/**
 * The target's last three instructions before a value return are sometimes
 * {@code store N; load N; return}: the source assigned the returned value to a variable and then
 * returned that variable. Copy propagation folded the pair into the return expression. The
 * instruction pattern is the proof, and the variable must already be printed in the expression
 * (a parameter or a local the expression reads); otherwise the target's variable has no name we
 * could write. Splitting the statement back gives {@code T v = expr; return v;}, the same
 * instructions the target carries.
 */
public final class ReturnedVariable {
  private ReturnedVariable() {
  }

  public static void restore(Statement root) {
    restoreStat(root);
  }

  private static void restoreStat(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (int i = 0; i < exprents.size(); i++) {
        if (!(exprents.get(i) instanceof ExitExprent exit)
          || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() == null) {
          continue;
        }
        int slot = RoundTrip.storedBeforeReturn(exit.bytecode);
        if (slot < 0) {
          continue;
        }
        VarExprent variable = findVariable(exit.getValue(), slot);
        if (variable == null || exit.getValue() instanceof VarExprent) {
          continue;
        }
        VarProcessor processor = variable.getProcessor();
        if (processor != null && processor.getVarFinal(variable.getVarVersionPair()) == FinalType.EXPLICIT_FINAL) {
          continue;
        }
        Exprent value = exit.getValue();
        AssignmentExprent assignment = new AssignmentExprent(variable.copy(), value, value.bytecode);
        ExitExprent replacement = new ExitExprent(ExitExprent.Type.RETURN, variable.copy(),
          exit.getRetType(), exit.bytecode, exit.getMethodDescriptor());
        exprents.set(i, assignment);
        exprents.add(i + 1, replacement);
        i++;
      }
    }
    for (Statement child : stat.getStats()) {
      restoreStat(child);
    }
  }

  /** The printed variable the target stored into {@code slot}, or null when it is not printed. */
  private static VarExprent findVariable(Exprent value, int slot) {
    if (value instanceof VarExprent var) {
      return matches(var, slot) ? var : null;
    }
    for (Exprent child : value.getAllExprents(true)) {
      if (child instanceof VarExprent var && matches(var, slot)) {
        return var;
      }
    }
    return null;
  }

  private static boolean matches(VarExprent var, int slot) {
    if (var.isStack()) {
      return false;
    }
    LocalVariable lvt = var.getLVT();
    if (lvt != null) {
      return lvt.getVersion().var == slot;
    }
    // Lambda parameters carry no LocalVariableTable entry; their slot is the original index.
    VarProcessor processor = var.getProcessor();
    Integer original = processor == null ? null : processor.getVarOriginalIndex(var.getIndex());
    return (original != null ? original : var.getIndex()) == slot;
  }
}

// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarTypeProcessor.FinalType;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

import java.util.BitSet;
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
        // The target kept the value in a local across the catch: `T v; try { v = expr; } catch { }
        // return v;`. The second table range for the slot is what makes the declaration outside.
        int[] tryShape = RoundTrip.tryStoredBeforeReturn(exit.bytecode);
        if (tryShape != null && restoreTryReturn(stat, exprents, i, exit, tryShape)) {
          i++;
          continue;
        }
        int slot = RoundTrip.storedBeforeReturn(exit.bytecode);
        if (slot < 0) {
          // Inside a try-with-resources javac copies the return value into a hidden slot across the
          // close, so the store/load pair is not adjacent to the return; the recorded shape proves
          // the same source assignment.
          slot = RoundTrip.twrStoredBeforeReturn(exit.bytecode);
        }
        if (slot < 0) {
          continue;
        }
        if (exit.getValue() instanceof VarExprent) {
          continue;
        }
        VarExprent variable = findVariable(exit.getValue(), slot);
        if (variable == null) {
          // The expression does not read the slot: the source assigned the value to a variable
          // and returned it, which the target's `store N; load N; return` still shows (a switch
          // expression's result, for one). The table names the variable; without a row it has no
          // printable name.
          LocalVariable lvt = exit.bytecode == null ? null : localOf(slot, exit.bytecode.nextSetBit(0));
          if (lvt == null) {
            continue;
          }
          variable = new VarExprent(slot, lvt.getVarType(), null);
          variable.setLVT(lvt);
        }
        VarProcessor processor = variable.getProcessor();
        if (processor != null && processor.getVarFinal(variable.getVarVersionPair()) == FinalType.EXPLICIT_FINAL) {
          continue;
        }
        Exprent value = exit.getValue();
        AssignmentExprent assignment = new AssignmentExprent((VarExprent) variable.copy(), value, value.bytecode);
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

  /**
   * Splits a return carried across a catch back into the assignment the try made and the return
   * the source wrote after it. The variable's two table ranges prove it was declared outside, so
   * the declaration goes on the try statement and the printer hoists the return past the brace.
   */
  private static boolean restoreTryReturn(Statement stat, List<Exprent> exprents, int index,
                                          ExitExprent exit, int[] shape) {
    Statement holder = stat;
    while (holder != null && !(holder instanceof CatchStatement)) {
      holder = holder.getParent();
    }
    if (holder == null) {
      return false;
    }
    int slot = shape[0];
    LocalVariable lvt = localOf(slot, shape[1]);
    if (lvt == null) {
      return false;
    }
    VarExprent variable = new VarExprent(slot, lvt.getVarType(), null);
    variable.setLVT(lvt);
    BitSet loadBits = new BitSet();
    loadBits.set(shape[1]);
    variable.addBytecodeOffsets(loadBits);

    Exprent value = exit.getValue();
    AssignmentExprent assignment = new AssignmentExprent((VarExprent) variable.copy(), value, value.bytecode);
    VarExprent returned = (VarExprent) variable.copy();
    BitSet returnBits = new BitSet();
    returnBits.set(shape[2]);
    returned.addBytecodeOffsets(returnBits);
    ExitExprent replacement = new ExitExprent(ExitExprent.Type.RETURN, returned,
      exit.getRetType(), returnBits, exit.getMethodDescriptor());

    exprents.set(index, assignment);
    exprents.add(index + 1, replacement);

    // A declaration emits no instruction, so it carries no bytecode mapping: a covered offset
    // would pull the line aligner's target for the load up to where the declaration prints.
    VarExprent declaration = new VarExprent(slot, lvt.getVarType(), null);
    declaration.setLVT(lvt);
    declaration.setDefinition(true);
    holder.getVarDefinitions().add(declaration);
    return true;
  }

  /** The table entry for a slot whose range covers this offset. */
  private static LocalVariable localOf(int slot, int offset) {
    StructMethod method = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    StructLocalVariableTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return null;
    }
    for (LocalVariable var : table.getVariables().toList()) {
      if (var.getIndex() == slot && var.getStart() <= offset && var.getEnd() > offset) {
        return var;
      }
    }
    return null;
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

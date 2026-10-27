// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.gen.CodeType;

import java.util.List;

/**
 * A constructor or call whose value the decompiler discarded, where the target stored it into a
 * source-named local that it never reads again.
 *
 * <p>{@code EmbeddedChannel channel = new EmbeddedChannel(connection);} compiles to the
 * constructor's value followed by {@code astore N}; the local is dead, so no read follows. The
 * tree keeps only the constructor call as a statement, and dropping the store recompiles to
 * {@code pop} — a different instruction. The class file names the variable: slot N has a single
 * LVT entry covering the store, and the method never loads N. Restoring the definition writes the
 * declaration back.
 */
public final class NamedDeadStore {
  private NamedDeadStore() {
  }

  public static boolean restore(Statement root, StructMethod method, VarProcessor varproc) {
    if (method == null || varproc == null || !RoundTrip.enabled() || !RoundTrip.selector("deadstore")) {
      return false;
    }
    int[] count = {0};
    collect(root, method, varproc, count);
    return count[0] > 0;
  }

  private static void collect(Statement stat, StructMethod method, VarProcessor varproc, int[] count) {
    if (stat.getExprents() != null) {
      for (int i = 0; i < stat.getExprents().size(); i++) {
        Exprent exprent = stat.getExprents().get(i);
        if (exprent == null) {
          continue;
        }
        LocalVariable lvt = deadStoreTarget(exprent, method);
        if (lvt == null) {
          continue;
        }
        int index = DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER);
        VarExprent variable = new VarExprent(index, exprent.getExprType(), varproc);
        variable.setLVT(lvt);
        variable.setDefinition(true);
        variable.addBytecodeOffsets(exprent.bytecode);
        stat.getExprents().set(i, new AssignmentExprent(variable, exprent, exprent.bytecode));
        count[0]++;
      }
    }
    for (Statement child : stat.getStats()) {
      collect(child, method, varproc, count);
    }
  }

  /**
   * The table entry of the dead local a discarded value was stored into, or null. The statement
   * must end in an instruction whose successor stores into a slot the method never loads, and the
   * slot must have exactly one table entry — a scope that exists only for this store.
   */
  private static LocalVariable deadStoreTarget(Exprent exprent, StructMethod method) {
    if (!(exprent instanceof NewExprent) && !(exprent instanceof InvocationExprent)) {
      return null;
    }
    if (exprent.getExprType() == null || exprent.getExprType().type == CodeType.VOID) {
      return null;
    }
    // The value's last instruction is inside the expression tree: a constructor call is a child
    // of the NewExprent and carries the invokespecial's offsets, not the `new` opcode's.
    int last = -1;
    List<Exprent> parts = new java.util.ArrayList<>(exprent.getAllExprents(true, true));
    if (exprent instanceof NewExprent created && created.getConstructor() != null) {
      parts.add(created.getConstructor());
      parts.addAll(created.getConstructor().getAllExprents(true, true));
    }
    for (Exprent part : parts) {
      last = Math.max(last, RoundTrip.lastInstructionStart(part.bytecode, method));
    }
    if (last < 0) {
      return null;
    }
    // The statement's bytes may end on the store itself or just before it.
    int store = last;
    int storeEnd = RoundTrip.instructionEnd(method, last);
    int slot = RoundTrip.storeSlotAt(method, last);
    if (slot < 0) {
      store = storeEnd;
      storeEnd = RoundTrip.instructionEnd(method, store);
      slot = RoundTrip.storeSlotAt(method, store);
    }
    if (slot < 0 || storeEnd < 0) {
      return null;
    }
    if (slot < 0 || RoundTrip.loadsSlot(method, slot)) {
      return null;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return null;
    }
    LocalVariable found = null;
    int entries = 0;
    for (LocalVariable var : table.getVariables().toList()) {
      if (var.getIndex() != slot) {
        continue;
      }
      entries++;
      // The table starts a local's range right after the store that first fills it.
      if (var.getStart() == storeEnd) {
        found = var;
      }
    }
    return entries == 1 && found != null && found.getName() != null ? found : null;
  }
}

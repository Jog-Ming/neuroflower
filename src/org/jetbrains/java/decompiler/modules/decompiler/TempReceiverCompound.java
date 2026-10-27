// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructMethod;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * A compound assignment on a field whose receiver javac cached in a temporary.
 *
 * <p>{@code this.part.f += e} is not compilable through a duplicate of the receiver, because the
 * receiver itself is a field access: javac evaluates it into a synthetic slot and stores through
 * that — {@code aload_0; getfield part; astore N; aload N; aload N; getfield f; ...; dup_x1;
 * putfield f; pop}. The decompiler keeps the store to N as a local declaration
 * ({@code ModelPart var2 = this.part;}) and the value-producing store as an expanded assignment,
 * which recompiles without the {@code dup_x1}/{@code pop} the target kept.
 *
 * <p>The class file proves the source form: the store's putfield is preceded by {@code dup_x1}
 * (or {@code dup2_x1} for a wide value) and followed by {@code pop} (or {@code pop2}), and the
 * field read has no duplicate before its getfield. The temporary is synthetic — no LVT entry —
 * and every occurrence of its slot is one of the matched pairs, so removing the pairs leaves no
 * reference behind. Each pair rewrites to {@code recv.f op= rhs}, which javac re-lowers to the
 * same instructions.
 */
public final class TempReceiverCompound {
  private TempReceiverCompound() {
  }

  public static boolean fold(Statement root, StructMethod method) {
    if (method == null || !RoundTrip.enabled() || !RoundTrip.selector("compound-temp")) {
      return false;
    }

    List<Statement> statements = new ArrayList<>();
    collectStatements(root, statements);

    List<Pair> pairs = new ArrayList<>();
    for (Statement stat : statements) {
      List<Exprent> exprents = stat.getExprents();
      if (exprents == null) {
        continue;
      }
      for (int i = 0; i + 1 < exprents.size(); i++) {
        Pair pair = match(exprents, i);
        if (pair != null) {
          pairs.add(pair);
        }
      }
    }
    if (pairs.isEmpty()) {
      return false;
    }

    // Every occurrence of a temporary's slot has to belong to a matched pair: the declaration
    // must disappear with the pairs, and a remaining use would read a variable we just removed.
    Set<VarExprent> covered = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Pair pair : pairs) {
      covered.add(pair.temp);
      covered.add(pair.storeReceiver);
      covered.add(pair.readReceiver);
    }
    Set<Integer> slots = new java.util.HashSet<>();
    for (Pair pair : pairs) {
      slots.add(pair.temp.getIndex());
    }
    Set<Integer> complete = new java.util.HashSet<>(slots);
    for (Statement stat : statements) {
      for (VarExprent var : varUses(stat)) {
        if (complete.contains(var.getIndex()) && !covered.contains(var)) {
          complete.remove(var.getIndex());
        }
      }
    }

    boolean changed = false;
    for (Pair pair : pairs) {
      if (!complete.contains(pair.temp.getIndex())) {
        continue;
      }
      Exprent receiver = pair.definition.getRight();
      pair.store.replaceExprent(pair.storeReceiver, receiver.copy());
      pair.assignment.setRight(pair.operand);
      pair.assignment.setCondType(pair.function.getFuncType());
      List<Exprent> exprents = pair.list;
      for (int i = exprents.size() - 1; i >= 0; i--) {
        if (exprents.get(i) == pair.definition) {
          exprents.remove(i);
        }
      }
      changed = true;
    }
    return changed;
  }

  private static Pair match(List<Exprent> exprents, int index) {
    Exprent first = exprents.get(index);
    Exprent second = exprents.get(index + 1);
    if (!(first instanceof AssignmentExprent definition)) {
      return null;
    }
    if (!(definition.getLeft() instanceof VarExprent temp) || temp.isStack() || temp.getLVT() != null) {
      return null;
    }
    Exprent receiver = definition.getRight();
    if (receiver == null || containsSlot(receiver, temp.getIndex())) {
      return null;
    }
    if (!(second instanceof AssignmentExprent assignment) || assignment.getCondType() != null) {
      return null;
    }
    if (!(assignment.getLeft() instanceof FieldExprent store) || store.isStatic()) {
      return null;
    }
    if (!(store.getInstance() instanceof VarExprent storeReceiver) || storeReceiver.isStack()
      || storeReceiver.getIndex() != temp.getIndex()) {
      return null;
    }
    if (!(assignment.getRight() instanceof FunctionExprent function)) {
      return null;
    }
    // Only the operators the compound printer renders; a string concatenation lowers differently.
    switch (function.getFuncType()) {
      case ADD:
      case SUB:
      case MUL:
      case DIV:
      case REM:
      case AND:
      case OR:
      case XOR:
      case SHL:
      case SHR:
      case USHR:
        break;
      default:
        return null;
    }
    List<Exprent> operands = function.getLstOperands();
    if (operands.size() != 2) {
      return null;
    }
    // `f op= e` reads the target first, so the target is always the left operand in the target.
    if (!(operands.get(0) instanceof FieldExprent matching) || !(matching.getInstance() instanceof VarExprent readReceiver)
      || readReceiver.isStack() || readReceiver.getIndex() != temp.getIndex()
      || !sameField(store, matching)) {
      return null;
    }
    if (!RoundTrip.isCachedReceiverTarget(store, matching)) {
      return null;
    }
    return new Pair(exprents, definition, assignment, function, store, storeReceiver, matching,
      readReceiver, operands.get(1), temp);
  }

  private static boolean sameField(FieldExprent first, FieldExprent second) {
    return first.isStatic() == second.isStatic()
      && Objects.equals(first.getName(), second.getName())
      && Objects.equals(first.getClassname(), second.getClassname())
      && Objects.equals(first.getDescriptor(), second.getDescriptor());
  }

  private static boolean containsSlot(Exprent exprent, int slot) {
    for (Exprent nested : exprent.getAllExprents(true, true)) {
      if (nested instanceof VarExprent var && var.getIndex() == slot) {
        return true;
      }
    }
    return false;
  }

  private static List<VarExprent> varUses(Statement stat) {
    List<VarExprent> out = new ArrayList<>();
    collectVars(stat, out);
    return out;
  }

  private static void collectVars(Statement stat, List<VarExprent> out) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent != null) {
          collectVars(exprent, out);
        }
      }
    }
    for (Exprent exprent : stat.getStatExprents()) {
      if (exprent != null) {
        collectVars(exprent, out);
      }
    }
    for (Statement child : stat.getStats()) {
      collectVars(child, out);
    }
  }

  private static void collectVars(Exprent exprent, List<VarExprent> out) {
    for (Exprent child : exprent.getAllExprents()) {
      if (child instanceof VarExprent var) {
        out.add(var);
      }
      if (child != null) {
        collectVars(child, out);
      }
    }
  }

  private static void collectStatements(Statement stat, List<Statement> out) {
    out.add(stat);
    for (Statement child : stat.getStats()) {
      collectStatements(child, out);
    }
  }

  private record Pair(List<Exprent> list, AssignmentExprent definition, AssignmentExprent assignment,
                      FunctionExprent function, FieldExprent store, VarExprent storeReceiver,
                      FieldExprent matching, VarExprent readReceiver, Exprent operand, VarExprent temp) {
  }
}

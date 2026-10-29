// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;

import java.util.ArrayList;
import java.util.List;

/**
 * The target's {@code return expr} inside a try can reach the compiler as a value left on the
 * operand stack when the protected range ends (the monitorexit of an enclosing synchronized block
 * runs before the areturn). The decompiler models the value crossing the block boundary as a
 * synthetic stack variable, so the tree reads {@code v = expr;} in the try body and
 * {@code return v;} after the catch. A stack variable has no source spelling: the target wrote a
 * return inside the try, and printing one reproduces its bytes. The fold is only taken when the
 * handlers leave the method themselves (they cannot fall through to the return) and the variable
 * has exactly the two occurrences the fold rewrites.
 */
public final class TryReturnFold {
  private TryReturnFold() {
  }

  public static void fold(Statement root) {
    foldStat(root);
  }

  private static void foldStat(Statement stat) {
    if (stat instanceof SequenceStatement) {
      List<Statement> stats = stat.getStats();
      for (int i = 0; i + 1 < stats.size(); i++) {
        if (stats.get(i) instanceof CatchStatement catchStatement
            && fold(catchStatement, stats.get(i + 1), stat)) {
          // The return after the try is gone; continue with the next pair.
          i--;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      foldStat(child);
    }
  }

  private static boolean fold(CatchStatement catchStatement, Statement after, Statement parent) {
    List<Exprent> returnExprents = after.getExprents();
    if (returnExprents == null || returnExprents.size() != 1) {
      return false;
    }
    if (!(returnExprents.get(0) instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() == null
        || !(exit.getValue() instanceof VarExprent returned) || !isSyntheticValue(returned)) {
      return false;
    }
    // Every handler must leave the method: a handler that falls through would reach the return
    // after the try, which the fold deletes.
    for (int i = 1; i < catchStatement.getStats().size(); i++) {
      if (!exits(catchStatement.getStats().get(i))) {
        return false;
      }
    }
    // Nothing outside the try may reach the statement the fold deletes.
    for (org.jetbrains.java.decompiler.modules.decompiler.StatEdge edge : after.getAllPredecessorEdges()) {
      Statement source = edge.getSource();
      if (source != catchStatement && !isInside(source, catchStatement)) {
        return false;
      }
    }
    Statement body = catchStatement.getFirst();
    List<Exprent> bodyExprents = body.getExprents();
    if (bodyExprents == null || bodyExprents.isEmpty()) {
      return false;
    }
    Exprent last = bodyExprents.get(bodyExprents.size() - 1);
    if (!(last instanceof AssignmentExprent assignment) || assignment.getCondType() != null
        || !(assignment.getLeft() instanceof VarExprent assigned)
        || assigned.getIndex() != returned.getIndex() || assigned.getVersion() != returned.getVersion()) {
      return false;
    }
    // The variable must exist only as the assignment the fold rewrites and the return it moves.
    if (countUses(parent.getTopParent(), returned.getIndex(), returned.getVersion()) != 2) {
      return false;
    }

    Exprent value = assignment.getRight();
    org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent folded =
      new ExitExprent(ExitExprent.Type.RETURN, value, exit.getRetType(),
        assignment.bytecode != null ? assignment.bytecode : exit.bytecode, exit.getMethodDescriptor());
    bodyExprents.set(bodyExprents.size() - 1, folded);

    // The declaration belongs to the variable, which no longer exists.
    catchStatement.getVarDefinitions().removeIf(definition -> definition instanceof VarExprent var
      && var.getIndex() == returned.getIndex());

    returnExprents.clear();
    return true;
  }

  /** Stack variables are the decompiler's stand-ins for values crossing a block boundary. */
  private static boolean isSyntheticValue(VarExprent var) {
    return var.isStack() || var.getIndex() >= VarExprent.STACK_BASE;
  }

  private static boolean isInside(Statement stat, Statement ancestor) {
    for (Statement cur = stat; cur != null; cur = cur.getParent()) {
      if (cur == ancestor) {
        return true;
      }
    }
    return false;
  }

  /** Whether this statement's own flow ends with a return or a throw. */
  private static boolean exits(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null && !exprents.isEmpty()) {
      Exprent last = exprents.get(exprents.size() - 1);
      return last instanceof ExitExprent exit
        && (exit.getExitType() == ExitExprent.Type.RETURN || exit.getExitType() == ExitExprent.Type.THROW);
    }
    List<Statement> stats = stat.getStats();
    for (int i = stats.size() - 1; i >= 0; i--) {
      Statement child = stats.get(i);
      if (child.getExprents() != null && child.getExprents().isEmpty()) {
        continue;
      }
      return exits(child);
    }
    return false;
  }

  private static int countUses(Statement stat, int index, int version) {
    int count = 0;
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        count += countIn(exprent, index, version);
      }
    }
    for (Exprent exprent : stat.getStatExprents()) {
      count += countIn(exprent, index, version);
    }
    for (Statement child : stat.getStats()) {
      count += countUses(child, index, version);
    }
    return count;
  }

  private static int countIn(Exprent exprent, int index, int version) {
    int count = 0;
    if (exprent instanceof VarExprent var && var.getIndex() == index && var.getVersion() == version) {
      count++;
    }
    for (Exprent child : exprent.getAllExprents(true)) {
      if (child != exprent && child instanceof VarExprent var
          && var.getIndex() == index && var.getVersion() == version) {
        count++;
      }
    }
    return count;
  }
}

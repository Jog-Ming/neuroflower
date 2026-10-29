// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement.EdgeDirection;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

import java.util.ArrayList;
import java.util.List;

/**
 * A {@code for (T x : c)} compiles to one loop head that every {@code continue} and the loop's own
 * back edge reach. The statement graph builder gives each back edge its own infinite loop, and the
 * two that survive are nested: the inner one holds the head and the {@code continue}s, the outer
 * one the body's tail. The source is one loop, so the pair has to become one again.
 *
 * <p>The rule is gated on the target's local variable table. The iterator a for-each creates is a
 * compiler temporary and has no row; a source that declared {@code Iterator it = ...} itself has
 * one, and its loop must keep the explicit form. That row is the whole difference between the two.
 */
public final class NestedLoopMerge {
  private NestedLoopMerge() {}

  public static boolean merge(Statement root, StructMethod method, VarProcessor varproc) {
    return mergeRec(root, method, varproc);
  }

  private static boolean mergeRec(Statement stat, StructMethod method, VarProcessor varproc) {
    if (stat instanceof DoStatement loop && mergeOne(loop, method, varproc)) {
      return true;
    }
    for (Statement child : new ArrayList<>(stat.getStats())) {
      if (mergeRec(child, method, varproc)) {
        return true;
      }
    }
    return false;
  }

  private static boolean mergeOne(DoStatement outer, StructMethod method, VarProcessor varproc) {
    if (outer.getLooptype() != DoStatement.Type.INFINITE) {
      return false;
    }
    Statement outerBody = outer.getFirst();
    if (!(outerBody instanceof SequenceStatement body) || body.getStats().size() < 2) {
      return false;
    }
    Statement head = body.getStats().get(0);
    if (!(head instanceof DoStatement inner) || inner.getLooptype() != DoStatement.Type.INFINITE
        || inner.getStats().size() != 1 || inner.getFirst().getExprents() != null) {
      return false;
    }

    boolean hasContinue = false;
    boolean hasBreak = false;
    for (StatEdge edge : new ArrayList<>(inner.getLabelEdges())) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE && edge.getDestination() == inner) {
        hasContinue = true;
      }
      else if (edge.getType() == StatEdge.TYPE_BREAK
          && body.getStats().contains(edge.getDestination())) {
        hasBreak = true;
      }
      else {
        return false;
      }
    }
    if (!hasContinue || !hasBreak) {
      return false;
    }
    if (forEachIterator(outer, inner, method, varproc) == null) {
      return false;
    }

    // The continues jump to the outer loop's head now; the breaks land on the statement the inner
    // loop's body fell out to, which the merge leaves as a plain forward jump inside one body.
    for (StatEdge edge : new ArrayList<>(inner.getLabelEdges())) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE) {
        edge.getDestination().removePredecessor(edge);
        edge.getSource().changeEdgeNode(EdgeDirection.FORWARD, edge, outer);
        outer.addPredecessor(edge);
        outer.addLabeledEdge(edge);
      }
      else {
        edge.removeClosure();
        edge.getSource().changeEdgeType(EdgeDirection.FORWARD, edge, StatEdge.TYPE_REGULAR);
      }
    }

    // Splice the inner loop's body where the loop stood. Its last statement keeps the continue
    // the outer loop now owns, so the sequence's own successor is unchanged.
    Statement innerBody = inner.getFirst();
    List<Statement> moved = new ArrayList<>(innerBody.getStats());
    body.getStats().removeWithKey(inner.id);
    int index = 0;
    for (Statement statement : moved) {
      innerBody.getStats().removeWithKey(statement.id);
      body.getStats().addWithKeyAndIndex(index++, statement, statement.id);
      statement.setParent(body);
    }
    if (moved.isEmpty()) {
      return false;
    }
    body.setFirst(moved.get(0));

    // The statement the inner loop fell out to was reached only once its last `continue` guard
    // passed, so it belongs to that guard's arm: the source wrote it after the guard chain, inside
    // the same trailing if. Moving it there is also what lets the arm print as the loop body's end.
    Statement last = moved.get(moved.size() - 1);
    List<Statement> after = new ArrayList<>();
    for (int i = body.getStats().size() - 1; i >= 0; i--) {
      Statement statement = body.getStats().get(i);
      if (statement == last) {
        break;
      }
      after.add(0, statement);
    }
    if (!after.isEmpty() && last instanceof IfStatement guard && guard.getIfstat() != null
        && guard.getElsestat() == null && isContinueTo(last, outer)) {
      Statement arm = guard.getIfstat();
      for (Statement statement : after) {
        body.getStats().removeWithKey(statement.id);
      }
      if (arm instanceof SequenceStatement sequence) {
        for (Statement statement : after) {
          sequence.getStats().addWithKey(statement, statement.id);
          statement.setParent(sequence);
        }
      }
      else {
        List<Statement> stats = new ArrayList<>();
        stats.add(arm);
        stats.addAll(after);
        SequenceStatement sequence = new SequenceStatement(stats);
        sequence.setAllParent();
        guard.getStats().removeWithKey(arm.id);
        guard.setIfstat(sequence);
        guard.getStats().addWithKey(sequence, sequence.id);
        sequence.setParent(guard);
      }
    }

    foldGuards(body, outer);
    return true;
  }

  private static boolean isContinueTo(Statement stat, Statement loop) {
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE && edge.getDestination() == loop) {
        return true;
      }
    }
    return false;
  }

  /**
   * `if (C) goto P; region; P:` is the source's `if (!C) { region }`; the tree kept it as a guard
   * whose branch leaps over the region. Fold the region into the guard's arm, invert the test, and
   * let the guard fall out to `P`. A guard with no region left (`if (C) skip; continue;`) is the
   * source's `if (!C) continue;` and turns its branch into that continue.
   */
  private static void foldGuards(Statement stat, Statement loop) {
    foldGuard(stat, loop);
    for (Statement child : new ArrayList<>(stat.getStats())) {
      foldGuards(child, loop);
    }
  }

  private static void foldGuard(Statement stat, Statement loop) {
    if (!(stat instanceof IfStatement guard) || guard.getElsestat() != null
        || guard.getIfEdge() == null || !(guard.getParent() instanceof SequenceStatement sequence)) {
      return;
    }
    if (guard.getIfstat() != null) {
      flattenContinueGuard(guard, sequence, loop);
      return;
    }
    if (guard.getIfEdge().getType() != StatEdge.TYPE_REGULAR) {
      return;
    }
    Statement post = guard.getIfEdge().getDestination();
    List<Statement> region = new ArrayList<>();
    int index = sequence.getStats().indexOf(guard);
    for (int i = index + 1; i < sequence.getStats().size(); i++) {
      Statement next = sequence.getStats().get(i);
      if (next == post) {
        break;
      }
      region.add(next);
    }
    if (!region.isEmpty()) {
      if (!reaches(region, post)) {
        // The branch target is the guard's own arm, not the statement the region falls out to:
        // the block it lands on leaves the loop, so the source wrote its body there.
        if (isLoopArm(post, sequence, guard, loop)) {
          sequence.getStats().removeWithKey(post.id);
          guard.setIfstat(post);
          guard.getStats().addWithKey(post, post.id);
          post.setParent(guard);
        }
        return;
      }
      SequenceStatement arm = new SequenceStatement(region);
      for (Statement statement : region) {
        sequence.getStats().removeWithKey(statement.id);
      }
      arm.setAllParent();
      // The branch becomes the edge into the arm; the guard now falls out to the post.
      StatEdge branch = guard.getIfEdge();
      branch.getDestination().removePredecessor(branch);
      branch.getSource().removeSuccessor(branch);
      StatEdge into = new StatEdge(StatEdge.TYPE_REGULAR, guard.getFirst(), arm);
      into.labeled = false;
      guard.getFirst().addSuccessor(into);
      guard.setIfEdge(into);
      guard.setIfstat(arm);
      guard.getStats().addWithKey(arm, arm.id);
      arm.setParent(guard);
      for (StatEdge edge : new ArrayList<>(guard.getAllSuccessorEdges())) {
        guard.removeSuccessor(edge);
      }
      StatEdge out = new StatEdge(StatEdge.TYPE_REGULAR, guard, post);
      out.labeled = false;
      guard.addSuccessor(out);
      invertCondition(guard);
      return;
    }
    // No region between the guard and its branch target: the branch is the source's short-cut
    // past the rest of the body, and the fall-through is the loop's own continue.
    if (!isContinueTo(guard, loop)) {
      return;
    }
    StatEdge branch = guard.getIfEdge();
    branch.getDestination().removePredecessor(branch);
    branch.getSource().removeSuccessor(branch);
    StatEdge skipped = new StatEdge(StatEdge.TYPE_CONTINUE, guard.getFirst(), loop, loop);
    skipped.labeled = false;
    guard.getFirst().addSuccessor(skipped);
    guard.setIfEdge(skipped);
    for (StatEdge edge : new ArrayList<>(guard.getAllSuccessorEdges())) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE && edge.getDestination() == loop) {
        guard.removeSuccessor(edge);
      }
    }
    StatEdge out = new StatEdge(StatEdge.TYPE_BREAK, guard, post, enclosingIf(guard));
    out.labeled = false;
    out.explicit = true;
    guard.addSuccessor(out);
    invertCondition(guard);
  }

  /**
   * The tree's mirror of `if (C) continue; rest`: the guard holds `rest` as its arm and falls out
   * to the loop's back edge. The source wrote the guard and the statements after it, so the arm
   * moves back out into the enclosing block and the guard keeps only its continue. Without this the
   * arm would print inside the enclosing block's braces.
   */
  private static void flattenContinueGuard(IfStatement guard, SequenceStatement sequence, Statement loop) {
    if (!isContinueTo(guard, loop)) {
      return;
    }
    Statement arm = guard.getIfstat();
    Statement last = lastStatement(arm);
    if (last == null) {
      return;
    }
    Statement post = null;
    for (StatEdge edge : last.getAllSuccessorEdges()) {
      if (edge.getDestination() != loop && !isInside(arm, edge.getDestination())) {
        post = edge.getDestination();
        break;
      }
    }
    if (post == null) {
      return;
    }
    List<Statement> moved = new ArrayList<>();
    collect(arm, moved);
    int index = sequence.getStats().indexOf(guard);
    guard.getStats().removeWithKey(arm.id);
    guard.setIfstat(null);
    for (Statement statement : moved) {
      if (statement.getParent() instanceof SequenceStatement parent && parent != sequence) {
        parent.getStats().removeWithKey(statement.id);
      }
      sequence.getStats().addWithKeyAndIndex(++index, statement, statement.id);
      statement.setParent(sequence);
    }
    for (StatEdge edge : new ArrayList<>(guard.getAllSuccessorEdges())) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE && edge.getDestination() == loop) {
        guard.removeSuccessor(edge);
      }
    }
    // The guard now falls through to the statements that followed its arm; when it is the last
    // one, the fall-out leaves the enclosing arm for the statement after it.
    List<Statement> stats = sequence.getStats();
    int at = stats.indexOf(guard);
    if (at + 1 < stats.size()) {
      StatEdge next = new StatEdge(StatEdge.TYPE_REGULAR, guard, stats.get(at + 1));
      next.labeled = false;
      guard.addSuccessor(next);
    }
    else {
      StatEdge out = new StatEdge(StatEdge.TYPE_BREAK, guard, post, enclosingIf(guard));
      out.labeled = false;
      out.explicit = true;
      guard.addSuccessor(out);
    }
    Statement owner = enclosingIf(guard);
    if (owner != null) {
      for (StatEdge edge : new ArrayList<>(last.getAllSuccessorEdges())) {
        if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() == post) {
          Statement source = edge.getSource();
          source.removeSuccessor(edge);
          StatEdge exit = new StatEdge(StatEdge.TYPE_BREAK, source, post, owner);
          exit.labeled = false;
          exit.explicit = true;
          source.addSuccessor(exit);
        }
      }
    }

    StatEdge branch = guard.getIfEdge();
    branch.getDestination().removePredecessor(branch);
    branch.getSource().removeSuccessor(branch);
    StatEdge skipped = new StatEdge(StatEdge.TYPE_CONTINUE, guard.getFirst(), loop, loop);
    skipped.labeled = false;
    guard.getFirst().addSuccessor(skipped);
    guard.setIfEdge(skipped);
    invertCondition(guard);
  }

  private static List<Statement> collect(Statement stat, List<Statement> out) {
    if (stat instanceof SequenceStatement) {
      for (Statement child : new ArrayList<>(stat.getStats())) {
        collect(child, out);
      }
    }
    else {
      out.add(stat);
    }
    return out;
  }

  private static Statement lastStatement(Statement stat) {
    if (stat.getStats().isEmpty()) {
      return stat;
    }
    return lastStatement(stat.getStats().get(stat.getStats().size() - 1));
  }

  /** The innermost enclosing if whose arm holds the statement, or null when there is none. */
  private static Statement enclosingIf(Statement stat) {
    for (Statement parent = stat.getParent(); parent != null; parent = parent.getParent()) {
      if (parent instanceof IfStatement) {
        return parent;
      }
    }
    return null;
  }

  /** True when {@code post} is the guard's then-block: a body that leaves the loop on its own. */
  private static boolean isLoopArm(Statement post, SequenceStatement sequence, Statement guard, Statement loop) {
    if (post == guard || !sequence.getStats().contains(post)) {
      return false;
    }
    List<StatEdge> edges = post.getAllSuccessorEdges();
    if (edges.isEmpty()) {
      return false;
    }
    for (StatEdge edge : edges) {
      if (edge.getType() != StatEdge.TYPE_CONTINUE && edge.getType() != StatEdge.TYPE_BREAK
          && edge.getType() != StatEdge.TYPE_REGULAR) {
        return false;
      }
      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() != loop) {
        return false;
      }
    }
    return true;
  }

  private static boolean reaches(List<Statement> region, Statement post) {
    for (Statement statement : region) {
      if (touches(statement, post)) {
        return true;
      }
    }
    return false;
  }

  private static boolean touches(Statement stat, Statement post) {
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      if (edge.getDestination() == post) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (!isInside(child, post) && touches(child, post)) {
        return true;
      }
    }
    return false;
  }

  private static boolean isInside(Statement stat, Statement other) {
    if (stat == other) {
      return true;
    }
    for (Statement child : stat.getStats()) {
      if (isInside(child, other)) {
        return true;
      }
    }
    return false;
  }

  private static void invertCondition(IfStatement guard) {
    Exprent condition = guard.getHeadexprent().getCondition();
    IfExprent head = (IfExprent) guard.getHeadexprent().copy();
    head.setCondition(RoundTrip.negateCondition(condition));
    guard.getHeadexprentList().set(0, head);
  }

  /**
   * The iterator a for-each over a collection declares, when the target's table gives its slot no
   * row: the loop is `x = it.next()` at the body's start, `while (it.hasNext())` at the head, and
   * `it = c.iterator()` before it.
   */
  private static VarExprent forEachIterator(DoStatement outer, DoStatement inner, StructMethod method, VarProcessor varproc) {
    Statement pre = previousData(outer);
    if (pre == null || pre.getExprents() == null || pre.getExprents().isEmpty()) {
      return null;
    }
    Exprent last = pre.getExprents().get(pre.getExprents().size() - 1);
    if (!(last instanceof AssignmentExprent init) || !(init.getLeft() instanceof VarExprent iterator)) {
      return null;
    }
    if (!(init.getRight() instanceof InvocationExprent call) || call.getInstance() == null
        || !"iterator".equals(call.getName())) {
      return null;
    }
    if (!isHasNextGuard(inner, iterator) || !isNextStore(inner, iterator)) {
      return null;
    }
    return hasLvtRow(method, varproc, iterator) ? null : iterator;
  }

  private static Statement previousData(Statement stat) {
    Statement current = stat;
    while (true) {
      Statement parent = current.getParent();
      if (parent == null) {
        return null;
      }
      if (parent instanceof SequenceStatement sequence) {
        int index = sequence.getStats().indexOf(current);
        if (index > 0) {
          return lastData(sequence.getStats().get(index - 1));
        }
        if (index != 0) {
          return null;
        }
        current = parent;
      }
      else {
        return null;
      }
    }
  }

  private static Statement lastData(Statement stat) {
    if (stat.getExprents() != null) {
      return stat;
    }
    for (int i = stat.getStats().size() - 1; i >= 0; i--) {
      Statement last = lastData(stat.getStats().get(i));
      if (last != null && !last.getExprents().isEmpty()) {
        return last;
      }
    }
    return null;
  }

  /** `if (!it.hasNext()) ...` at the head of the inner loop. */
  private static boolean isHasNextGuard(DoStatement inner, VarExprent iterator) {
    Statement first = inner.getFirst();
    while (first instanceof SequenceStatement sequence && !sequence.getStats().isEmpty()) {
      first = sequence.getFirst();
    }
    if (!(first instanceof IfStatement guard) || guard.getIfstat() == null || guard.getElsestat() != null) {
      return false;
    }
    Exprent condition = guard.getHeadexprent().getCondition();
    if (!(condition instanceof FunctionExprent function)
        || function.getFuncType() != FunctionExprent.FunctionType.BOOL_NOT
        || function.getLstOperands().size() != 1) {
      return false;
    }
    return isCallOn(function.getLstOperands().get(0), "hasNext", iterator);
  }

  /** The loop body starts with `x = (T) it.next()` once its header guard is skipped. */
  private static boolean isNextStore(DoStatement inner, VarExprent iterator) {
    Statement first = firstDataAfterGuard(inner);
    if (first == null || first.getExprents() == null || first.getExprents().isEmpty()) {
      return false;
    }
    if (!(first.getExprents().get(0) instanceof AssignmentExprent assignment)) {
      return false;
    }
    return isCallOn(uncast(assignment.getRight()), "next", iterator);
  }

  private static boolean isCallOn(Exprent exprent, String name, VarExprent iterator) {
    if (!(exprent instanceof InvocationExprent call) || !name.equals(call.getName())
        || !(call.getInstance() instanceof VarExprent receiver)) {
      return false;
    }
    return receiver.getIndex() == iterator.getIndex() && receiver.getVersion() == iterator.getVersion();
  }

  private static Statement firstDataAfterGuard(DoStatement inner) {
    Statement body = inner.getFirst();
    if (body instanceof SequenceStatement sequence) {
      boolean first = true;
      for (Statement child : sequence.getStats()) {
        if (first && child instanceof IfStatement) {
          first = false;
          continue;
        }
        first = false;
        Statement data = firstData(child);
        if (data != null) {
          return data;
        }
      }
      return null;
    }
    return firstData(body);
  }

  private static Exprent uncast(Exprent exprent) {
    while (exprent instanceof FunctionExprent function
        && function.getFuncType() == FunctionExprent.FunctionType.CAST
        && !function.getLstOperands().isEmpty()) {
      exprent = function.getLstOperands().get(0);
    }
    return exprent;
  }

  private static Statement firstData(Statement stat) {
    if (stat.getExprents() != null) {
      return stat;
    }
    for (Statement child : stat.getStats()) {
      Statement first = firstData(child);
      if (first != null && !first.getExprents().isEmpty()) {
        return first;
      }
    }
    return null;
  }

  private static boolean hasLvtRow(StructMethod method, VarProcessor varproc, VarExprent var) {
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    int slot = var.getIndex();
    Integer original = varproc == null ? null : varproc.getVarOriginalIndex(slot);
    for (LocalVariable local : table.getVariables().toList()) {
      if (local.getIndex() == slot || (original != null && local.getIndex() == original)) {
        return true;
      }
    }
    return false;
  }
}

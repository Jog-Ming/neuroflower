package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;

import java.util.ArrayList;
import java.util.List;

/**
 * One source loop whose head several back edges reach is built as a chain of infinite loops that
 * share the head block: each back edge opens a wrapper, the wrappers nest, and each wrapper's body
 * begins with the next one. The source has one loop, so the chain has to merge into it; until it
 * does, the loop's test sits inside a body and the printer emits {@code while (true)} with a
 * redundant inner loop.
 *
 * <p>The chain is only merged when every edge that leaves its loops means the same at the
 * outermost level: a continue of any chain loop is a continue of the merged loop, a break into the
 * merged body is fall-through, and the one shape the wrappers cut in two -- an if whose branch
 * leaves the innermost body for the statement right after it -- is proven rebuildable. Anything
 * else keeps the wrappers as they are: a wrong merge would print a jump the printer cannot
 * express.
 */
public final class LoopWrapperMerge {
  private LoopWrapperMerge() {}

  public static boolean restructure(Statement root) {
    if (!RoundTrip.selector("loopwrap")) {
      return false;
    }
    if (mergeChains(root)) {
      return true;
    }
    return recoverRec(root);
  }

  // ---------------------------------------------------------------------------------------------
  // The wrapper chain

  private static boolean mergeChains(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      if (mergeChains(child)) {
        return true;
      }
    }
    if (!(stat instanceof DoStatement loop)) {
      return false;
    }
    List<DoStatement> chain = chainOf(loop);
    if (chain.size() < 2) {
      return false;
    }
    Statement root = stat;
    while (root.getParent() != null) {
      root = root.getParent();
    }
    if (!validateChain(chain)) {
      return false;
    }
    for (int i = 0; i < chain.size() - 1; i++) {
      mergePair(chain.get(i), chain.get(i + 1));
    }
    SequenceHelper.condenseSequences(root);
    return true;
  }

  /**
   * The loops that wrap this one: each one's body must open with the loop inside it, and the
   * heads must be the same block -- the class file's way of saying the loops test the same
   * instructions. A loop that merely contains another at a later point is not a wrapper.
   */
  private static List<DoStatement> chainOf(DoStatement loop) {
    List<DoStatement> chain = new ArrayList<>();
    chain.add(loop);
    DoStatement current = loop;
    while (true) {
      Statement parentStat = current.getParent();
      if (!(parentStat instanceof SequenceStatement body) || body.getFirst() != current) {
        break;
      }
      Statement owner = body.getParent();
      if (!(owner instanceof DoStatement outer) || outer.getLooptype() != DoStatement.Type.INFINITE
          || outer.getFirst() != body || outer.getBasichead() != current.getBasichead()) {
        break;
      }
      chain.add(outer);
      current = outer;
    }
    return chain;
  }

  /**
   * The merged body in print order: the innermost body's statements, then what follows each
   * wrapper in the next one's body.
   */
  private static List<Statement> mergedOrder(List<DoStatement> chain) {
    List<Statement> order = new ArrayList<>();
    Statement innermost = chain.get(0).getFirst();
    if (!(innermost instanceof SequenceStatement body)) {
      return null;
    }
    order.addAll(body.getStats());
    for (int i = 1; i < chain.size(); i++) {
      Statement parentStat = chain.get(i - 1).getParent();
      if (!(parentStat instanceof SequenceStatement sequence)) {
        return null;
      }
      int at = sequence.getStats().indexOf(chain.get(i - 1));
      if (at < 0) {
        return null;
      }
      order.addAll(sequence.getStats().subList(at + 1, sequence.getStats().size()));
    }
    return order;
  }

  private static boolean validateChain(List<DoStatement> chain) {
    if (!(chain.get(0).getFirst() instanceof SequenceStatement innermost)) {
      return false;
    }
    List<Statement> order = mergedOrder(chain);
    if (order == null || order.isEmpty()) {
      return false;
    }
    int innerCount = innermost.getStats().size();
    if (innerCount == 0 || innerCount > order.size()) {
      return false;
    }
    DoStatement outermost = chain.get(chain.size() - 1);
    int arms = 0;
    // A wrapper's own fall-out edge is dropped by the merge, so it must not count as an entry
    // into the region the arm will occupy.
    List<StatEdge> removed = new ArrayList<>();
    for (DoStatement loop : chain) {
      if (loop != outermost) {
        removed.addAll(loop.getAllSuccessorEdges());
      }
    }
    for (DoStatement loop : chain) {
      for (StatEdge edge : new ArrayList<>(loop.getLabelEdges())) {
        if (edge.getType() == StatEdge.TYPE_CONTINUE) {
          if (!isChainLoop(edge.getDestination(), chain)) {
            return false;
          }
        }
        else if (edge.getType() == StatEdge.TYPE_BREAK && edge.getDestination() instanceof DummyExitStatement) {
          continue;
        }
        else if (edge.getType() == StatEdge.TYPE_BREAK && outermost.containsStatementStrict(edge.getDestination())) {
          int kind = validInternalBreak(edge, innermost, order, innerCount, removed);
          if (kind == 0) {
            return false;
          }
          if (kind == 2) {
            // The wrappers were cut around exactly one branch: the innermost loop's if whose arm
            // the source wrote inside the loop. More than one, or a branch anywhere else, is a
            // structure this pass cannot prove it rebuilds.
            if (loop != chain.get(0) || ++arms > 1) {
              return false;
            }
          }
        }
        else {
          return false;
        }
      }
      if (loop != outermost) {
        for (StatEdge edge : new ArrayList<>(loop.getAllSuccessorEdges())) {
          if (edge.getType() != StatEdge.TYPE_REGULAR || !outermost.containsStatementStrict(edge.getDestination())) {
            return false;
          }
        }
      }
    }
    return arms == 1;
  }

  private static boolean isChainLoop(Statement stat, List<DoStatement> chain) {
    for (DoStatement loop : chain) {
      if (loop == stat) {
        return true;
      }
    }
    return false;
  }

  /**
   * A break that lands inside the merged body has exactly two printable forms, told apart by the
   * return value: 1 for a try body's fall-through (the destination is the statement after the one
   * the source lives in), 2 for an if's arm (the branch opens the source's then arm and the
   * statements between the test and the break's target are its else arm -- the shape the wrappers
   * cut in two, only taken when both arms end by leaving and nothing else enters them). 0 means
   * the edge cannot be printed at all.
   */
  private static int validInternalBreak(StatEdge edge, SequenceStatement innermost,
                                        List<Statement> order, int innerCount, List<StatEdge> removed) {
    Statement source = edge.getSource();
    Statement target = edge.getDestination();
    Statement owner = null;
    for (Statement up = source; up != null; up = up.getParent()) {
      if (order.contains(up)) {
        owner = up;
        break;
      }
    }
    if (owner == null) {
      return 0;
    }
    if (!(owner instanceof IfStatement guard) || guard.getFirst() != source) {
      // Only a try body's fall-through is printable: the destination is the statement after the
      // one the source lives in, and the source must not be the branch of an if.
      if (source instanceof IfStatement || isIfHead(source)) {
        return 0;
      }
      int at = order.indexOf(owner);
      return at >= 0 && at + 1 < order.size() && order.get(at + 1) == target ? 1 : 0;
    }
    // The if's branch: it must be a direct statement of the innermost body, so its sequence and
    // the region after it are the ones the merge creates.
    if (!innermost.getStats().contains(guard) || guard.iftype != IfStatement.IFTYPE_IF
        || guard.getIfstat() != null || guard.getElsestat() != null || guard.isLabeled()
        || guard.isPatternMatched()) {
      return 0;
    }
    List<Statement> rest = new ArrayList<>(innermost.getStats().subList(
      innermost.getStats().indexOf(guard) + 1, innermost.getStats().size()));
    List<Statement> region = new ArrayList<>(order.subList(innerCount, order.size()));
    if (rest.isEmpty() || region.isEmpty() || region.get(0) != target) {
      return 0;
    }
    List<StatEdge> falls = guard.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (falls.size() != 1 || falls.get(0).getType() != StatEdge.TYPE_REGULAR
        || falls.get(0).getDestination() != rest.get(0)) {
      return 0;
    }
    if (!enteredOnlyBy(region, edge, removed) || !enteredOnlyBy(rest, falls.get(0), removed)) {
      return 0;
    }
    return endsAway(region.get(region.size() - 1)) && endsAway(rest.get(rest.size() - 1)) ? 2 : 0;
  }

  private static boolean isIfHead(Statement stat) {
    return stat.getParent() instanceof IfStatement ifStatement && ifStatement.getFirst() == stat;
  }

  private static boolean enteredOnlyBy(List<Statement> region, StatEdge opening, List<StatEdge> removed) {
    for (Statement statement : region) {
      for (StatEdge edge : statement.getAllPredecessorEdges()) {
        if (edge == opening || containsIdentity(removed, edge)) {
          continue;
        }
        if (!containsRegion(region, edge.getSource())) {
          return false;
        }
      }
    }
    return true;
  }

  private static boolean containsRegion(List<Statement> region, Statement stat) {
    for (Statement candidate : region) {
      if (candidate == stat || candidate.containsStatementStrict(stat)) {
        return true;
      }
    }
    return false;
  }

  /** True when the statement's own flow leaves instead of falling on. */
  private static boolean endsAway(Statement stat) {
    List<StatEdge> edges = stat.getAllSuccessorEdges();
    if (edges.isEmpty()) {
      return false;
    }
    for (StatEdge edge : edges) {
      if (edge.getType() != StatEdge.TYPE_CONTINUE && edge.getType() != StatEdge.TYPE_BREAK) {
        return false;
      }
    }
    return true;
  }

  /** Merges one wrapper into the next; the chain was validated as a whole. */
  private static void mergePair(DoStatement loop, DoStatement parent) {
    List<StatEdge> continues = new ArrayList<>();
    List<StatEdge> internalBreaks = new ArrayList<>();
    List<StatEdge> outsideBreaks = new ArrayList<>();
    for (StatEdge edge : new ArrayList<>(loop.getLabelEdges())) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE) {
        continues.add(edge);
      }
      else if (edge.getType() == StatEdge.TYPE_BREAK && parent.containsStatementStrict(edge.getDestination())) {
        internalBreaks.add(edge);
      }
      else {
        outsideBreaks.add(edge);
      }
    }
    List<StatEdge> dropped = new ArrayList<>();
    for (StatEdge edge : new ArrayList<>(loop.getAllSuccessorEdges())) {
      if (containsIdentity(continues, edge) || containsIdentity(internalBreaks, edge)
          || containsIdentity(outsideBreaks, edge)) {
        continue;
      }
      dropped.add(edge);
    }
    for (StatEdge edge : continues) {
      edge.changeDestination(parent);
      parent.addLabeledEdge(edge);
    }
    for (StatEdge edge : internalBreaks) {
      edge.removeClosure();
      edge.changeType(StatEdge.TYPE_REGULAR);
    }
    for (StatEdge edge : outsideBreaks) {
      edge.changeClosure(parent);
    }
    for (StatEdge edge : dropped) {
      edge.remove();
    }
    Statement content = loop.getFirst();
    loop.replaceWith(content);
  }

  private static boolean containsIdentity(List<StatEdge> edges, StatEdge edge) {
    for (StatEdge candidate : edges) {
      if (candidate == edge) {
        return true;
      }
    }
    return false;
  }

  // ---------------------------------------------------------------------------------------------
  // Arms the wrappers kept apart

  /**
   * While the wrappers stood, a branch out of the inner one landed after its body in the outer
   * one, so the source's if/else was cut in two: the then region sits after the enclosing
   * sequence and the fall-through region ends that sequence. Once the wrappers are one loop both
   * regions are ordinary statements, and the branch target is the statement right after the if's
   * sequence. Rebuilding the two arms from those regions restores the if/else the class file
   * compiled: the branch enters the then arm, the fall-through enters the else arm.
   */
  private static boolean recoverRec(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      if (recoverRec(child)) {
        return true;
      }
    }
    return stat instanceof IfStatement guard && recoverOne(guard);
  }

  private static boolean recoverOne(IfStatement guard) {
    if (guard.iftype != IfStatement.IFTYPE_IF || guard.getIfstat() != null || guard.getElsestat() != null
        || guard.isLabeled() || guard.isPatternMatched()) {
      return false;
    }
    Statement innerStat = guard.getParent();
    if (!(innerStat instanceof SequenceStatement inner)) {
      return false;
    }
    Statement outerStat = inner.getParent();
    if (!(outerStat instanceof SequenceStatement outer)) {
      return false;
    }
    int innerIndex = inner.getStats().indexOf(guard);
    int outerIndex = outer.getStats().indexOf(inner);
    if (innerIndex < 0 || outerIndex < 0
        || innerIndex + 1 >= inner.getStats().size()
        || outerIndex + 1 >= outer.getStats().size()) {
      return false;
    }
    StatEdge branch = guard.getIfEdge();
    if (branch == null || branch.getType() != StatEdge.TYPE_REGULAR) {
      return false;
    }
    List<Statement> region = new ArrayList<>(outer.getStats().subList(outerIndex + 1, outer.getStats().size()));
    List<Statement> rest = new ArrayList<>(inner.getStats().subList(innerIndex + 1, inner.getStats().size()));
    if (branch.getDestination() != region.get(0)) {
      return false;
    }
    List<StatEdge> falls = guard.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (falls.size() != 1 || falls.get(0).getType() != StatEdge.TYPE_REGULAR
        || falls.get(0).getDestination() != rest.get(0)) {
      return false;
    }
    // Neither region may be entered from outside itself except by the test that opens it, and
    // neither may fall back into the other or past the enclosing statement: both arms end by
    // leaving the enclosing region, exactly as the two regions did.
    if (!enteredOnlyBy(region, branch, List.of()) || !enteredOnlyBy(rest, falls.get(0), List.of())) {
      return false;
    }
    if (!endsAway(region.get(region.size() - 1)) || !endsAway(rest.get(rest.size() - 1))) {
      return false;
    }

    Statement thenArm = arm(region);
    Statement elseArm = arm(rest);
    for (Statement statement : region) {
      outer.getStats().removeWithKey(statement.id);
    }
    for (Statement statement : rest) {
      inner.getStats().removeWithKey(statement.id);
    }
    branch.changeDestination(thenArm);
    guard.setIfEdge(branch);
    StatEdge elseEdge = falls.get(0);
    elseEdge.changeSource(guard.getFirst());
    elseEdge.changeDestination(elseArm);
    guard.setElseEdge(elseEdge);
    guard.setIfstat(thenArm);
    guard.setElsestat(elseArm);
    guard.getStats().addWithKey(thenArm, thenArm.id);
    guard.getStats().addWithKey(elseArm, elseArm.id);
    if (thenArm instanceof SequenceStatement sequence) {
      sequence.setAllParent();
    }
    if (elseArm instanceof SequenceStatement sequence) {
      sequence.setAllParent();
    }
    thenArm.setParent(guard);
    elseArm.setParent(guard);
    guard.iftype = IfStatement.IFTYPE_IFELSE;
    return true;
  }

  private static Statement arm(List<Statement> statements) {
    return statements.size() == 1 ? statements.get(0) : new SequenceStatement(statements);
  }
}

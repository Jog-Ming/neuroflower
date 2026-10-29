// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;

import java.util.ArrayList;
import java.util.List;

/**
 * A {@code for} loop whose body ends in {@code count = …; break;} after an if/else-if chain that
 * jumps to it from inside a labelled block. javac emits the chain's arms as jumps past the label's
 * end, so the tree keeps a block labelled for those jumps, the join after it, and the update inside
 * the block; the printer can then only lay the block out as a labelled block with explicit breaks.
 *
 * <p>The class file's layout is the source's: the join is the code after the if chain, reachable
 * only from the chain's arms, and the update is the loop header's. Moving the join to the end of
 * the deepest sequence that holds the arms' break sources turns those jumps into fall-through, and
 * moving the update out of the block turns the edges into it into continues; the block's label is
 * then unused and the ordinary for recognizer folds the update into the header.
 */
public final class LoopJoinSink {
  private LoopJoinSink() {}

  public static boolean sink(Statement root) {
    if (!RoundTrip.selector("joinsink")) {
      return false;
    }
    return sinkRec(root);
  }

  private static boolean sinkRec(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      if (sinkRec(child)) {
        return true;
      }
    }
    return stat instanceof DoStatement loop && sinkOne(loop);
  }

  private static boolean sinkOne(DoStatement loop) {
    if (loop.getLooptype() != DoStatement.Type.WHILE) {
      return false;
    }
    // The body's shape: the labelled block, then the join that leaving the block reaches.
    if (!(loop.getFirst() instanceof SequenceStatement body) || body.getStats().size() != 2) {
      return false;
    }
    Statement block = body.getStats().get(0);
    Statement join = body.getStats().get(1);
    if (!(block instanceof SequenceStatement) || !block.isLabeled() || block.getStats().isEmpty()) {
      return false;
    }

    // The block's tail is the loop's update: it ends by continuing to the loop.
    Statement update = block.getStats().getLast();
    List<StatEdge> updateEdges = update.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (!(update instanceof BasicBlockStatement) || update.getExprents() == null
        || update.getExprents().isEmpty() || updateEdges.size() != 1
        || updateEdges.get(0).getType() != StatEdge.TYPE_CONTINUE
        || updateEdges.get(0).getDestination() != loop) {
      return false;
    }

    // The join leaves the loop, and only breaks out of the block reach it.
    List<StatEdge> joinEdges = join.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (join.getExprents() == null || join.getExprents().isEmpty() || joinEdges.size() != 1
        || joinEdges.get(0).getType() != StatEdge.TYPE_BREAK
        || loop.containsStatementStrict(joinEdges.get(0).getDestination())) {
      return false;
    }
    List<StatEdge> breaks = new ArrayList<>();
    for (StatEdge edge : join.getPredecessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getSource() == block) {
        continue; // the block's fall-through edge, not a jump the class file has
      }
      if (edge.getType() != StatEdge.TYPE_BREAK || !block.containsStatementStrict(edge.getSource())
          || edge.closure != block || !edge.explicit) {
        return false;
      }
      breaks.add(edge);
    }
    if (breaks.isEmpty()) {
      return false;
    }

    // The deepest sequence of the block that holds every arm the breaks come from: the join is the
    // code right after that sequence's last statement.
    Statement common = breaks.get(0).getSource();
    while (!holds(common, breaks)) {
      common = common.getParent();
      if (common == null || common == loop) {
        return false;
      }
    }
    if (!(common instanceof SequenceStatement sequence) || sequence == block
        || sequence.containsStatementStrict(join) || !block.containsStatementStrict(sequence)) {
      return false;
    }
    // The update is only ever reached from inside the loop; an outside edge would turn into a
    // jump into the loop's middle.
    for (StatEdge edge : update.getAllPredecessorEdges()) {
      if (!loop.containsStatementStrict(edge.getSource())) {
        return false;
      }
    }

    // The breaks now fall through to the join, which moves into the sequence.
    for (StatEdge edge : breaks) {
      retarget(edge, StatEdge.TYPE_REGULAR, null);
    }
    for (StatEdge edge : new ArrayList<>(block.getSuccessorEdges(StatEdge.TYPE_REGULAR))) {
      if (edge.getDestination() == join) {
        block.removeSuccessor(edge);
      }
    }
    body.getStats().removeWithKey(join.id);
    sequence.getStats().addWithKey(join, join.id);
    join.setParent(sequence);

    // Every path that fell out of the block or jumped to its tail now continues to the update,
    // which leaves the block for the loop body's end.
    for (StatEdge edge : new ArrayList<>(update.getAllPredecessorEdges())) {
      retarget(edge, StatEdge.TYPE_CONTINUE, loop);
    }
    block.getStats().removeWithKey(update.id);
    body.getStats().addWithKey(update, update.id);
    update.setParent(body);

    // The arms that jump to the join now read as the source's if/else-if chain, and the last
    // arm's continue as its else.
    nestChain(sequence, join);
    return true;
  }

  /**
   * A run of plain ifs whose arms all jump to the join is the source's if/else-if chain: each
   * if's false path reaches the next, and the last one continues to the loop. Nesting them makes
   * the else arms explicit, which is the only form that prints a continue as an else branch.
   */
  private static void nestChain(SequenceStatement sequence, Statement join) {
    List<Statement> stats = sequence.getStats();
    if (stats.isEmpty() || stats.get(stats.size() - 1) != join) {
      return;
    }
    List<IfStatement> chain = new ArrayList<>();
    for (int i = stats.size() - 2; i >= 0; i--) {
      if (!(stats.get(i) instanceof IfStatement)) {
        break;
      }
      chain.add(0, (IfStatement) stats.get(i));
    }
    if (chain.size() < 2) {
      return;
    }
    for (int i = 0; i < chain.size(); i++) {
      IfStatement ifstat = chain.get(i);
      if (ifstat.iftype != IfStatement.IFTYPE_IF || ifstat.getIfstat() == null
          || ifstat.getElsestat() != null || !fallsTo(ifstat.getIfstat(), join)) {
        return;
      }
      List<StatEdge> falseEdges = ifstat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
      if (falseEdges.size() != 1) {
        return;
      }
      StatEdge edge = falseEdges.get(0);
      boolean last = i == chain.size() - 1;
      if (last ? edge.getType() != StatEdge.TYPE_CONTINUE
               : edge.getType() != StatEdge.TYPE_REGULAR || edge.getDestination() != chain.get(i + 1)) {
        return;
      }
    }

    IfStatement last = chain.get(chain.size() - 1);
    BasicBlockStatement exit = BasicBlockStatement.create();
    last.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL).get(0).changeSource(exit);
    attachElse(last, exit);

    for (int i = chain.size() - 2; i >= 0; i--) {
      IfStatement ifstat = chain.get(i);
      Statement arm = chain.get(i + 1);
      ifstat.removeSuccessor(ifstat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL).get(0));
      sequence.getStats().removeWithKey(arm.id);
      attachElse(ifstat, arm);
    }
  }

  /** Makes {@code arm} the else branch of {@code ifstat}. */
  private static void attachElse(IfStatement ifstat, Statement arm) {
    StatEdge elseedge = new StatEdge(StatEdge.TYPE_REGULAR, ifstat.getFirst(), arm);
    ifstat.getFirst().addSuccessor(elseedge);
    ifstat.setElsestat(arm);
    ifstat.setElseEdge(elseedge);
    ifstat.getStats().addWithKey(arm, arm.id);
    arm.setParent(ifstat);
    ifstat.iftype = IfStatement.IFTYPE_IFELSE;
  }

  /** True when the statement's own flow reaches {@code target} by a plain edge. */
  private static boolean fallsTo(Statement stat, Statement target) {
    for (StatEdge edge : stat.getSuccessorEdges(StatEdge.TYPE_REGULAR)) {
      if (edge.getDestination() == target) {
        return true;
      }
    }
    return false;
  }

  private static boolean holds(Statement candidate, List<StatEdge> breaks) {
    for (StatEdge edge : breaks) {
      if (edge.getSource() != candidate && !candidate.containsStatementStrict(edge.getSource())) {
        return false;
      }
    }
    return true;
  }

  /** Changes an edge's type and closure, keeping the closure's label set consistent. */
  private static void retarget(StatEdge edge, int type, Statement closure) {
    Statement source = edge.getSource();
    if (edge.closure != null && edge.closure != closure) {
      edge.closure.getLabelEdges().remove(edge);
    }
    source.changeEdgeType(Statement.EdgeDirection.FORWARD, edge, type);
    edge.closure = closure;
    edge.labeled = type == StatEdge.TYPE_CONTINUE;
    if (closure != null) {
      closure.addLabeledEdge(edge);
    }
  }
}

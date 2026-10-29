// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * The source's {@code while (C) { … }} compiles its test at the loop head; when the body can leave
 * through the same block the failing test reaches, the statement graph builder keeps that block
 * inside the infinite loop, with the test as an if whose fall-through lands on it. The tree then
 * prints {@code while (true) { if (C) { … } exit }}, which lays the exit block out before the
 * update and drops the test into the body.
 *
 * <p>The fix is the layout the class file shows: the block the test's false branch reaches starts
 * past the loop's back edge, so it is code after the loop. Moving it out leaves the ordinary while
 * recognizer ({@link MergeHelper#matchWhile}) the shape it knows, and the break edges that reached
 * the block now leave the loop, labelled, which is how the source's {@code break} jumps back out.
 */
public final class LoopExitLift {
  private LoopExitLift() {}

  public static boolean lift(Statement root) {
    if (!RoundTrip.selector("exitlift")) {
      return false;
    }
    return liftRec(root);
  }

  private static boolean liftRec(Statement stat) {
    for (Statement child : new ArrayList<>(stat.getStats())) {
      if (liftRec(child)) {
        return true;
      }
    }
    return stat instanceof DoStatement loop && liftOne(loop);
  }

  private static boolean liftOne(DoStatement loop) {
    if (loop.getLooptype() != DoStatement.Type.INFINITE) {
      return false;
    }
    int[] exit = RoundTrip.loopExitOffsets(loop);
    if (exit == null) {
      return false;
    }
    int tail = exit[3];

    // The loop's test is the leading if: its condition's last branch lands on the exit block.
    Statement first = loop.getFirst();
    while (first instanceof SequenceStatement sequence && !sequence.getStats().isEmpty()) {
      first = sequence.getFirst();
    }
    if (!(first instanceof IfStatement test)) {
      return false;
    }
    if (test.iftype != IfStatement.IFTYPE_IF || test.getIfstat() == null || test.getElsestat() != null) {
      return false;
    }
    if (test.getFirst() == null || test.getFirst().getExprents() == null
        || !test.getFirst().getExprents().isEmpty()) {
      return false;
    }
    if (RoundTrip.lastBranchTarget(test.getHeadexprent()) != tail) {
      return false;
    }

    // The test's fall-through reaches the block, and the block is the trailing run of the
    // sequence the test lives in: everything the loop prints after the test is exit code.
    Statement parent = test.getParent();
    if (!(parent instanceof SequenceStatement sequence)) {
      return false;
    }
    int index = sequence.getStats().indexOf(test);
    if (index < 0 || index + 1 >= sequence.getStats().size()) {
      return false;
    }
    List<Statement> moved = new ArrayList<>(sequence.getStats().subList(index + 1, sequence.getStats().size()));
    Statement landing = fallThrough(test);
    if (landing == null || moved.get(0) != landing) {
      return false;
    }
    for (Statement statement : moved) {
      if (RoundTrip.firstOffset(statement) < tail) {
        return false;
      }
    }

    // A block another path enters is not the loop's own exit.
    Set<Statement> region = Collections.newSetFromMap(new IdentityHashMap<>());
    region.addAll(moved);
    for (Statement statement : moved) {
      for (StatEdge edge : statement.getAllPredecessorEdges()) {
        if (!loop.containsStatementStrict(edge.getSource())) {
          return false;
        }
      }
      // The block also has to leave the loop where the loop leaves: a jump from it back into the
      // body would make the moved code a second entry into the loop, not its exit.
      if (returnsInto(statement, loop, region)) {
        return false;
      }
    }

    for (Statement statement : moved) {
      sequence.getStats().removeWithKey(statement.id);
    }
    List<Statement> blockStats = new ArrayList<>();
    blockStats.add(loop);
    blockStats.addAll(moved);
    SequenceStatement block = new SequenceStatement(blockStats);
    loop.getParent().replaceStatement(loop, block);
    block.setAllParent();

    // Replacing the loop retargets its predecessors at the new block; a continue belongs to the
    // loop it jumps to, not to the sequence the loop was spliced into.
    for (StatEdge edge : block.getPredecessorEdges(StatEdge.TYPE_CONTINUE)) {
      if (loop.containsStatementStrict(edge.getSource())) {
        block.removePredecessor(edge);
        edge.getSource().changeEdgeNode(Statement.EdgeDirection.FORWARD, edge, loop);
        loop.addPredecessor(edge);
      }
    }

    // The breaks that reached the block now leave the loop, and the test is the loop's own:
    // the ordinary while recognizer folds it in from here.
    relabelBreaks(loop, loop, region);
    StatEdge exitEdge = new StatEdge(StatEdge.TYPE_REGULAR, loop, landing);
    exitEdge.labeled = false;
    loop.addSuccessor(exitEdge);
    return MergeHelper.matchWhile(loop);
  }

  /** True when a statement in the region jumps into the loop's remaining body. */
  private static boolean returnsInto(Statement stat, Statement loop, Set<Statement> region) {
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      Statement destination = edge.getDestination();
      if (destination == null || destination instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement
          || region.contains(destination) || !loop.containsStatementStrict(destination)) {
        continue;
      }
      // A destination inside the loop that is not part of the region: the region is not the exit.
      if (!containsRegion(destination, region)) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (returnsInto(child, loop, region)) {
        return true;
      }
    }
    return false;
  }

  private static boolean containsRegion(Statement destination, Set<Statement> region) {
    for (Statement candidate : region) {
      if (candidate == destination || candidate.containsStatementStrict(destination)) {
        return true;
      }
    }
    return false;
  }

  /** The destination of the leading if's fall-through edge, or null. */
  private static Statement fallThrough(IfStatement test) {
    for (StatEdge edge : test.getAllSuccessorEdges()) {
      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() != test.getIfstat()) {
        return edge.getDestination();
      }
    }
    return null;
  }

  /** Makes every break that lands on the moved block a labelled break out of the loop. */
  private static void relabelBreaks(Statement stat, DoStatement loop, Set<Statement> region) {
    for (StatEdge edge : new ArrayList<>(stat.getAllSuccessorEdges())) {
      if (edge.getType() == StatEdge.TYPE_BREAK && region.contains(edge.getDestination())) {
        edge.closure = loop;
        edge.labeled = true;
        loop.addLabeledEdge(edge);
      }
    }
    for (Statement child : stat.getStats()) {
      relabelBreaks(child, loop, region);
    }
  }
}

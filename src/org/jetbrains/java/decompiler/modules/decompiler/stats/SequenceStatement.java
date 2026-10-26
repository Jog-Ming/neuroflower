// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Arrays;
import java.util.List;


public class SequenceStatement extends Statement {


  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected SequenceStatement() {
    super(StatementType.SEQUENCE);
  }

  public SequenceStatement(Statement... stats) {
    this(Arrays.asList(stats));
  }

  public SequenceStatement(List<? extends Statement> lst) {

    this();

    lastBasicType = lst.get(lst.size() - 1).getLastBasicType();

    for (Statement st : lst) {
      stats.addWithKey(st, st.id);
    }

    first = stats.get(0);
  }

  protected SequenceStatement(Statement head, Statement tail) {

    this(Arrays.asList(head, tail));

    List<StatEdge> lstSuccs = tail.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (!lstSuccs.isEmpty()) {
      StatEdge edge = lstSuccs.get(0);

      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() != head) {
        post = edge.getDestination();
      }
    }
  }


  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead2Block(Statement head) {

    if (head.getLastBasicType() != LastBasicType.GENERAL) {
      return null;
    }

    // at most one outgoing edge
    StatEdge edge = null;
    List<StatEdge> lstSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (!lstSuccs.isEmpty()) {
      edge = lstSuccs.get(0);
    }

    if (edge != null && edge.getType() == StatEdge.TYPE_REGULAR) {
      Statement stat = edge.getDestination();

      if (stat != head && stat.getPredecessorEdges(StatEdge.TYPE_REGULAR).size() == 1
          && !stat.isMonitorEnter()) {

        if (stat.getLastBasicType() == LastBasicType.GENERAL) {
          if (DecHelper.checkStatementExceptions(Arrays.asList(head, stat))) {
            return new SequenceStatement(head, stat);
          }
        }
      }
    }

    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();
    boolean islabeled = isLabeled();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    if (islabeled) {
      buf.appendIndent(indent++).append("label").append(this.id).append(": {").appendLineSeparator();
    }

    boolean notempty = false;


    for (int i = 0; i < stats.size(); i++) {

      Statement st = stats.get(i);

      // A guard printed this exit already; the rest of the sequence became unconditional.
      if (RoundTrip.isConsumedGuardExit(st)) {
        continue;
      }


      // `if (C) { rest } else { continue; }` printed by us as the guard `if (!C) { continue; }
      // rest`: the target's branch lands straight on the exit block, so the branch-then-goto pair
      // the guard form needs is absent. Keep the rest inside the then arm and the exit in an else.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && ifStatement.getIfstat() == null && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && !ifStatement.isPatternMatched()
          && hasContent(stats.subList(i + 1, stats.size()))
          && RoundTrip.selector("elseexit")
          && RoundTrip.exitBranchLandsOn(ifStatement.getHeadexprent(), ifStatement.getIfEdge())) {
        Exprent condition = ifStatement.getHeadexprent().getCondition();
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(condition instanceof FunctionExprent not
            && not.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT
            && not.getLstOperands().size() == 1
          ? not.getLstOperands().get(0)
          : RoundTrip.negateCondition(condition));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        for (int k = i + 1; k < stats.size(); k++) {
          buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
        }
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.appendIndent(indent + 1)
          .append(ifStatement.getIfEdge().getType() == StatEdge.TYPE_BREAK ? "break;" : "continue;")
          .appendLineSeparator();
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        break;
      }

      // `if (C) continue; body` in the source; the decompiler printed its mirror `if (!C) { body }`.
      // The target's branch-then-goto shape and line table prove the continue. The mirror is the
      // loop's whole remaining body, so the guard is exact only when this sequence is the loop
      // body and the if is its last statement; otherwise the continue would skip the tail.
      if (st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isPatternMatched() && !ifStatement.isLabeled() && !st.isLabeled()
          && ifStatement.getIfstat() != null
          && i == stats.size() - 1 && endsLoopBody()
          && RoundTrip.printContinueGuard(ifStatement.getHeadexprent(), this)) {
        Exprent condition = ifStatement.getHeadexprent().getCondition();
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(condition instanceof FunctionExprent not
            && not.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT
            && not.getLstOperands().size() == 1
          ? not.getLstOperands().get(0)
          : RoundTrip.negateCondition(condition));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        buf.appendIndent(indent).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
        notempty = true;
        continue;
      }

      // `if (C) { ...; continue; } rest` in the source; the decompiler kept `rest` as the else
      // arm, so the continue becomes the loop's back edge. The arm's terminal goto to the loop
      // head proves the source closed the branch. Hoisting the arm is exact only when the if
      // ends the loop body: the arm's scope then ends where the else block's did, so a local it
      // declares cannot move, and nothing after the if could depend on the branch.
      if (st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IFELSE && ifStatement.getElsestat() != null
          && !ifStatement.isPatternMatched() && !ifStatement.isLabeled() && !st.isLabeled()
          && ifStatement.getIfstat() != null
          && !RoundTrip.printsNothing(ifStatement.getElsestat())
          && !RoundTrip.declaresLocalToEnd(ifStatement.getIfstat())
          && i == stats.size() - 1 && endsLoopBody()
          && RoundTrip.printContinueElse(ifStatement.getHeadexprent(), this)) {
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(ifStatement.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
        buf.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        buf.appendIndent(indent).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getElsestat(), indent, false));
        notempty = true;
        continue;
      }

      // `while (a && b) { body } return X;` where the exit block sits before the body and the
      // condition's branches target both the exit and the body: the source wrote the guard
      // inside `while (true)`.
      if (i + 1 < stats.size() && st instanceof DoStatement loop
          && loop.getLooptype() == DoStatement.Type.WHILE
          && loop.getConditionExprent() instanceof FunctionExprent and
          && and.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND
          && and.getLstOperands().size() == 2
          && loop.getFirst() != null
          && singleExit(stats.get(i + 1)) != null
          && RoundTrip.guardBranches(and, stats.get(i + 1), loop.getFirst())) {
        Exprent guard = RoundTrip.negateCondition(and);
        buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
        buf.appendIndent(indent + 1).append("if (").append(guard.toJava(indent + 1)).append(") {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 2, true));
        buf.appendIndent(indent + 1).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(loop.getFirst(), indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        i++;
        continue;
      }

      // `while (cond) { body } tail...` where the tail fills the exit block between the condition
      // and the body and the back edge jumps behind it: the source wrote
      // `while (true) { if (!cond) { tail } body }`.
      if (i + 1 < stats.size() && st instanceof DoStatement loop
          && loop.getLooptype() == DoStatement.Type.WHILE
          && loop.getConditionExprent() != null
          && !(loop.getConditionExprent() instanceof FunctionExprent and
               && and.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND)
          && loop.getFirst() != null
          && RoundTrip.guardExitBeforeBody(loop.getConditionExprent(), stats.get(i + 1),
               stats.get(stats.size() - 1), loop.getFirst())) {
        Exprent guard = RoundTrip.negateCondition(loop.getConditionExprent());
        buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
        buf.appendIndent(indent + 1).append("if (").append(guard.toJava(indent + 1)).append(") {").appendLineSeparator();
        for (int k = i + 1; k < stats.size(); k++) {
          buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 2, true));
        }
        buf.appendIndent(indent + 1).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(loop.getFirst(), indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        i = stats.size();
        continue;
      }

      // `if (A) { … exit } if (B) { … exit }` with pattern variables in different slots, the first
      // no longer live where B tests, and B's variable not read afterwards: the source wrote an
      // else-if chain. Sequential ifs let javac reuse the first variable's slot.
      if (i + 1 < stats.size() && st instanceof IfStatement first
          && first.iftype == IfStatement.IFTYPE_IF && first.getElsestat() == null
          && !first.isLabeled() && !stats.get(i + 1).isLabeled()
          && stats.get(i + 1) instanceof IfStatement second
          && second.iftype == IfStatement.IFTYPE_IF && second.getElsestat() == null
          && first.getIfstat() != null && second.getIfstat() != null
          && second.varDefinitions.isEmpty()
          && (second.getFirst() == null || second.getFirst().getExprents() == null
              || second.getFirst().getExprents().isEmpty())
          && exits(first.getIfstat()) && exits(second.getIfstat())
          && patternVar(first) != null && patternVar(second) != null
          && !patternVar(first).getName().equals(patternVar(second).getName())
          && patternSlot(first) >= 0 && patternSlot(second) >= 0
          && patternSlot(first) != patternSlot(second)
          && !aliveAt(first, second)
          && i + 2 < stats.size() && stats.size() == i + 3 && exits(stats.get(i + 2))
          && !usedLater(stats, i + 2, patternVar(second))) {
        buf.append(ExprProcessor.listToJava(first.varDefinitions, indent));
        buf.append(first.getFirst().toJava(indent));
        buf.appendIndent(indent).append(first.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first.getIfstat(), indent + 1, true));
        buf.appendIndent(indent).append("} else ");
        buf.append(second.getFirst().toJava(indent));
        buf.append(second.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(second.getIfstat(), indent + 1, true));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        i++;
        continue;
      }

      // `if (C) { body } rest` where the target's table puts a void return between the condition
      // and the body, before the body's line: the source wrote `if (!C) { rest; return; } body`.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && (!ifStatement.isPatternMatched()
              || ifStatement.getHeadexprent().getCondition() instanceof FunctionExprent patternNot
                 && patternNot.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT)
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          // The exit-first guard of a trailing if is the printer's own; only a rest with content
          // needs this swap, and an empty rest is what that other rule sees.
          && hasContent(stats.subList(i + 1, stats.size()))
          && RoundTrip.voidReturnBeforeBody(ifStatement.getHeadexprent().bytecode, ifStatement.getIfstat()) >= 0) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(
          new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, true));
        // The block's own return prints as a statement when the printer kept it.
        if (!endsWithExit(stats.subList(i + 1, stats.size()))) {
          buf.appendIndent(indent + 1).append("return;").appendLineSeparator();
        }
        buf.appendIndent(indent).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
        notempty = true;
        break;
      }

      // `if (C) { body; return X; } rest` where the target branches to the body first: the source
      // wrote `if (!C) { rest } else { body; return X; }`. Only when neither arm declares a
      // local: moving a declaration across the arms would change its scope.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && !ifStatement.isPatternMatched()
          && ifStatement.getIfstat() != null
          && (endsWithReturn(ifStatement.getIfstat()) || endsWithBreak(ifStatement.getIfstat()))
          && hasContent(stats.subList(i + 1, stats.size()))
          && !RoundTrip.declaresLocal(ifStatement.getIfstat())
          && stats.subList(i + 1, stats.size()).stream().noneMatch(RoundTrip::declaresLocal)
          && RoundTrip.branchesToBody(ifStatement.getHeadexprent(), ifStatement.getIfstat())) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        Statement splitArm = new SequenceStatement(stats.subList(i + 1, stats.size()));
        if (!IfStatement.printSplitIf(buf, head, splitArm, ifStatement.getIfstat(), indent, false)) {
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(splitArm, indent + 1, true));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
        notempty = true;
        break;
      }

      // `if (C) { arm; return; } rest` at the tail: the target jumps to the rest, ends it with a
      // void return and reaches the arm from the condition's own fall-through, so the source wrote
      // `if (!C) { rest; return; } arm`. Both blocks keep their braces, so no local moves.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() instanceof SequenceStatement thenSeq
          && !thenSeq.getStats().isEmpty()
          && bareReturn(thenSeq.getStats().get(thenSeq.getStats().size() - 1)) != null
          && hasContent(stats.subList(i + 1, stats.size()))
          && stats.subList(i + 1, stats.size()).stream().noneMatch(RoundTrip::declaresLocalIn)
          && RoundTrip.guardBeforeTail(ifStatement.getHeadexprent(), stats.get(i + 1), thenSeq)) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        for (int k = i + 1; k < stats.size(); k++) {
          buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
        }
        buf.appendIndent(indent + 1).append("return;").appendLineSeparator();
        buf.appendIndent(indent).append("}").appendLineSeparator();
        List<Statement> hoisted = thenSeq.getStats();
        for (int k = 0; k < hoisted.size() - 1; k++) {
          buf.append(ExprProcessor.jmpWrapper(hoisted.get(k), indent, false));
        }
        notempty = true;
        break;
      }

      // `if (C) { body; return; }` at the method tail under the strict guard layout: the source
      // wrote `if (!C) { return; } body` (goto body / return / body:).
      if (!hasContent(stats.subList(i + 1, stats.size())) && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled()
          && ifStatement.getIfstat() instanceof SequenceStatement thenSeq
          && !thenSeq.getStats().isEmpty()
          && bareReturn(thenSeq.getStats().get(thenSeq.getStats().size() - 1)) != null
          && RoundTrip.guardReturnLayout(ifStatement.getFirst(), ifStatement.getHeadexprent(), thenSeq)) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.appendIndent(indent + 1).append("return;").appendLineSeparator();
        buf.appendIndent(indent).append("}").appendLineSeparator();
        List<Statement> hoisted = thenSeq.getStats();
        for (int k = 0; k < hoisted.size() - 1; k++) {
          buf.append(ExprProcessor.jmpWrapper(hoisted.get(k), indent, false));
        }
        notempty = true;
        break;
      }

      // `if (C) { body } return X;` where the body's last instruction jumps past the return:
      // the source wrote `if (C) { body } else { return X; }`.
      if (i + 1 == stats.size() - 1 && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && !ifStatement.isPatternMatched()
          && ifStatement.getIfstat() != null
          && singleExit(stats.get(i + 1)) != null
          && !RoundTrip.declaresLocal(ifStatement.getIfstat())
          && !RoundTrip.declaresLocal(stats.get(i + 1))
          && RoundTrip.armJumpsPast(ifStatement.getIfstat(), stats.get(i + 1))) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        if (!IfStatement.printSplitIf(buf, head, ifStatement.getIfstat(), stats.get(i + 1), indent, true)) {
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
        notempty = true;
        break;
      }

      // `if (C) { body } return X;` where the target returns X first is a guard on !C.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null && endsWithReturn(ifStatement.getIfstat())) {
        Statement tail = stats.get(i + 1);
        Exprent exit = singleExit(tail);
        if (exit instanceof ExitExprent tailExit
            && !writesAny(java.util.Collections.singletonList(ifStatement.getIfstat()), readLocals(tailExit.getValue()))
            && RoundTrip.returnGuard(ifStatement.getIfstat(), tail)) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          head.setCondition(RoundTrip.negateCondition(head.getCondition()));
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(tail, indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
          notempty = true;
          i++;
          continue;
        }
      }

      // The mirror: the bytecode put `return X` before the rest, but the target's table puts its
      // line last, so the source wrote `if (!C) { rest } return X;`.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          // A pattern variable may only move into the matched arm, which needs the condition to
          // start as a negation so the printed guard is the positive pattern.
          && (!ifStatement.isPatternMatched()
              || ifStatement.getHeadexprent().getCondition() instanceof FunctionExprent patternNot
                 && patternNot.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT)
          && !ifStatement.isLabeled()
          && ifStatement.getIfstat() != null
          // A try-with-resources body that ends in the moved exit cannot complete normally, and
          // the hidden close handler rethrows, so the try statement cannot either: the statement
          // after it becomes unreachable. Plain try/catch and try/finally still complete through
          // their handlers, so the source after them stays reachable.
          && !isResourceBody()
          && !(stats.get(i + 1).getExprents() != null && stats.get(i + 1).getExprents().isEmpty())) {
        Exprent exit = singleExit(ifStatement.getIfstat());
        if (exit instanceof ExitExprent headExit
            && (headExit.getExitType() == ExitExprent.Type.RETURN || headExit.getExitType() == ExitExprent.Type.THROW)
            && !writesAny(stats.subList(i + 1, stats.size()), readLocals(headExit.getValue()))
            && RoundTrip.exitAfterBody(ifStatement.getIfstat(), stats.get(i + 1))) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          head.setCondition(RoundTrip.negateCondition(head.getCondition()));
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(
            new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
          notempty = true;
          break;
        }
      }

      // A block that the table wrote before the parameters was a brace in the source. When such
      // a variable opens the tail after a returning guard and its scope runs to the method's
      // end, the source wrote the tail as the guard's else arm.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && ifStatement.getIfstat() != null && !ifStatement.isLabeled()
          && !ifStatement.isPatternMatched()
          && endsWithReturn(ifStatement.getIfstat())
          && RoundTrip.opensTrailingBlock(stats.get(i + 1))) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        Statement splitTail = new SequenceStatement(stats.subList(i + 1, stats.size()));
        if (!IfStatement.printSplitIf(buf, head, ifStatement.getIfstat(), splitTail, indent, false)) {
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(splitTail, indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
        notempty = true;
        break;
      }

      TextBuffer str = ExprProcessor.jmpWrapper(st, indent, false);

      if (i > 0 && !str.containsOnlyWhitespaces() && notempty) {
        buf.appendLineSeparator();
      }

      buf.append(str);

      notempty = !str.containsOnlyWhitespaces();
    }


    if (islabeled) {
      buf.appendIndent(indent-1).append("}").appendLineSeparator();
    }

    return buf;
  }

  /** The single return or throw of a statement, or null; a throw moves into a guard unharmed. */
  private static Exprent singleExit(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null && exprents.size() == 1
        && exprents.get(0) instanceof ExitExprent exit
        && (exit.getExitType() == ExitExprent.Type.RETURN || exit.getExitType() == ExitExprent.Type.THROW)) {
      return exit;
    }
    return null;
  }

  /** The statement when it is a single bare {@code return;} (no value), else null. */
  private static ExitExprent bareReturn(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null && exprents.size() == 1
        && exprents.get(0) instanceof ExitExprent exit
        && exit.getExitType() == ExitExprent.Type.RETURN && exit.getValue() == null) {
      return exit;
    }
    return null;
  }

  private static java.util.Set<Integer> readLocals(Exprent value) {
    java.util.Set<Integer> indexes = new java.util.HashSet<>();
    if (value != null) {
      for (Exprent exprent : value.getAllExprents(true, true)) {
        if (exprent instanceof VarExprent var && var.getIndex() != 0) {
          indexes.add(var.getIndex());
        }
      }
    }
    return indexes;
  }

  /** True when any of the statements assigns one of the given local slots. */
  private static boolean writesAny(List<Statement> statements, java.util.Set<Integer> indexes) {
    if (indexes.isEmpty()) {
      return false;
    }
    for (Statement statement : statements) {
      for (Exprent exprent : allExprents(statement)) {
        if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assignment
            && assignment.getLeft() instanceof VarExprent left && indexes.contains(left.getIndex())) {
          return true;
        }
        if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent function
            && (function.getFuncType() == FunctionExprent.FunctionType.IPP
                || function.getFuncType() == FunctionExprent.FunctionType.PPI
                || function.getFuncType() == FunctionExprent.FunctionType.IMM
                || function.getFuncType() == FunctionExprent.FunctionType.MMI)
            && function.getLstOperands().get(0) instanceof VarExprent target
            && indexes.contains(target.getIndex())) {
          return true;
        }
      }
    }
    return false;
  }

  private static List<Exprent> allExprents(Statement statement) {
    List<Exprent> out = new ArrayList<>();
    if (statement.getExprents() != null) {
      out.addAll(statement.getExprents());
    }
    out.addAll(statement.getStatExprents());
    for (Statement child : statement.getStats()) {
      out.addAll(allExprents(child));
    }
    return out;
  }

  private static boolean safeReturnValue(Exprent value) {
    if (value == null) {
      return true;
    }
    for (Exprent exprent : value.getAllExprents(true, true)) {
      if (exprent instanceof VarExprent var && var.getIndex() != 0) {
        return false;
      }
    }
    return true;
  }

  /** True when this sequence is the body of a try-with-resources statement. */
  /**
   * Whether this sequence's completion reaches the loop head: it is the last thing every enclosing
   * statement up to the loop runs, so a guard printed at its end skips nothing the loop still needs.
   */
  private boolean endsLoopBody() {
    Statement stat = this;
    for (Statement parent = stat.getParent(); parent != null; parent = stat.getParent()) {
      if (parent instanceof DoStatement) {
        return true;
      }
      if (parent instanceof SequenceStatement sequence) {
        if (sequence.getStats().getLast() != stat) {
          return false;
        }
      }
      else if (parent instanceof IfStatement ifStatement) {
        if (ifStatement.getIfstat() != stat) {
          return false;
        }
      }
      else {
        return false;
      }
      stat = parent;
    }
    return false;
  }

  private boolean isResourceBody() {
    return getParent() instanceof CatchStatement catchStatement && !catchStatement.getResources().isEmpty();
  }

  /** True when any of these statements prints anything. */
  private static boolean hasContent(List<Statement> statements) {
    for (Statement statement : statements) {
      List<Exprent> exprents = statement.getExprents();
      if (exprents != null && !exprents.isEmpty()) {
        return true;
      }
      if (exprents == null && hasContent(statement.getStats())) {
        return true;
      }
    }
    return false;
  }

  /** True when the last of these statements ends in a return or throw. */
  private static boolean endsWithExit(List<Statement> statements) {
    if (statements.isEmpty()) {
      return false;
    }
    Statement last = statements.get(statements.size() - 1);
    List<Exprent> exprents = last.getExprents();
    if (exprents != null) {
      return !exprents.isEmpty() && exprents.get(exprents.size() - 1) instanceof ExitExprent;
    }
    return endsWithExit(last.getStats());
  }

  /** Whether the first if's pattern variable is still in scope where the second if tests. */
  private static boolean aliveAt(IfStatement first, IfStatement second) {
    var method = RoundTrip.currentMethod();
    VarExprent variable = patternVar(first);
    int at = RoundTrip.firstOffset(second);
    if (method == null || variable == null || at < 0) {
      return false;
    }
    org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute table =
      method.getAttribute(org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    return table.getVariables().anyMatch(entry -> entry.getIndex() == variable.getIndex()
      && entry.getStartPC() <= at && at < entry.getStartPC() + entry.getLength());
  }

  /** The instanceof pattern variable this if declares, or null. */
  private static VarExprent patternVar(IfStatement stat) {
    if (stat.getHeadexprent() == null || stat.getHeadexprent().getCondition() == null) {
      return null;
    }
    for (Exprent part : stat.getHeadexprent().getCondition().getAllExprents(true, true)) {
      if (part instanceof FunctionExprent function
          && function.getFuncType() == FunctionExprent.FunctionType.INSTANCEOF
          && function.getLstOperands().size() > 2
          && function.getLstOperands().get(2) instanceof VarExprent variable) {
        return variable;
      }
    }
    return null;
  }

  /** The slot of the instanceof pattern variable this if declares, or -1. */
  private static int patternSlot(IfStatement stat) {
    VarExprent variable = patternVar(stat);
    return variable == null ? -1 : variable.getIndex();
  }

  /** Whether this statement's own body ends with a return or a throw. */
  private static boolean exits(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      if (exprents.isEmpty()) {
        return false;
      }
      Exprent last = exprents.get(exprents.size() - 1);
      return last instanceof ExitExprent exit
        && (exit.getExitType() == ExitExprent.Type.RETURN || exit.getExitType() == ExitExprent.Type.THROW);
    }
    List<Statement> children = stat.getStats();
    return !children.isEmpty() && exits(children.get(children.size() - 1));
  }

  /** Whether a later statement of this sequence still reads that variable. */
  private static boolean usedLater(List<Statement> stats, int from, VarExprent variable) {
    if (variable == null) {
      return false;
    }
    for (int k = from; k < stats.size(); k++) {
      if (readsVariable(stats.get(k), variable.getIndex(), variable.getVersion())) {
        return true;
      }
    }
    return false;
  }

  private static boolean readsVariable(Statement stat, int index, int version) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        for (Exprent part : exprent.getAllExprents(true, true)) {
          if (part instanceof VarExprent variable && variable.getIndex() == index
              && variable.getVersion() == version) {
            return true;
          }
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (readsVariable(child, index, version)) {
        return true;
      }
    }
    return false;
  }

  private static boolean endsWithReturn(Statement stat) {
    Exprent last = lastExprent(stat);
    return last instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN;
  }

  /**
   * True when the arm ends in a plain {@code break} out of the enclosing loop: the arm leaves the
   * statement, so the source could equally have written it as the else arm of the negated test.
   */
  private static boolean endsWithBreak(Statement stat) {
    Statement last = stat;
    while (true) {
      List<Statement> children = last.getStats();
      if (children == null || children.isEmpty()) {
        break;
      }
      last = children.get(children.size() - 1);
    }
    List<StatEdge> edges = last.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    return edges.size() == 1 && edges.get(0).getType() == StatEdge.TYPE_BREAK
      && edges.get(0).explicit && !edges.get(0).labeled;
  }

  private static Exprent lastExprent(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      return exprents.isEmpty() ? null : exprents.get(exprents.size() - 1);
    }
    List<Statement> children = stat.getStats();
    return children.isEmpty() ? null : lastExprent(children.get(children.size() - 1));
  }

  @Override
  public Statement getSimpleCopy() {
    return new SequenceStatement();
  }
}

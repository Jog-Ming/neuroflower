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
import org.jetbrains.java.decompiler.util.TextUtil;

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

    // A labelled block that is really the source's else-if chain, or an if whose two arms were
    // swapped: print the source shape and drop the label the class file needed for the breaks.
    if (islabeled && RoundTrip.selector("elseifchain") && printLabelledChain(buf, indent)) {
      return buf;
    }

    // The rest of an else-if chain the enclosing print is rebuilding: the source wrote these as
    // further `else if` clauses, not as statements after the arm's break.
    if (!islabeled && RoundTrip.selector("elseifchain") && printsAsChainArm()) {
      appendChain(buf, indent);
      return buf;
    }

    // A run of ifs an arm at a time falling into the same exit: once the arms are a chain, the
    // copy of that exit the printer left in each arm is the chain's own end, printed after it.
    if (!islabeled && RoundTrip.selector("elseifchain") && printTailChain(buf, indent)) {
      return buf;
    }

    // `while (true) { while (A && B) { x++; } if (A) break; body }`: both written loops jump back
    // to the same test, so the CFG builder made the body the inner loop's and left the increment
    // outside it. The target's offsets put the increment first, then the guard, then the body, and
    // the guard repeats the first atom of the merged test.
    if (!islabeled && RoundTrip.selector("incrementloop") && printFoldedIncrementLoop(buf, indent)) {
      return buf;
    }

    // A break that closed this block: a local declared here has its scope ending at a goto another
    // jump lands on, and the run leaves only through the break to a switch. javac ends the local's
    // row where the source's closing brace stood, so the source wrote `{ … } break;` and the break
    // is not part of the run.
    if (!islabeled && RoundTrip.selector("bareblock") && RoundTrip.selector("switchbreak")
        && printClosedBlockBreak(buf, indent)) {
      return buf;
    }

    if (islabeled) {
      buf.appendIndent(indent++).append("label").append(this.id).append(": {").appendLineSeparator();
    }

    boolean notempty = false;


    for (int i = 0; i < stats.size(); i++) {

      Statement st = stats.get(i);

      // The caller printed this statement already as part of a wider shape; it is one
      // instruction and must not print twice.
      if (RoundTrip.isStatementSkipped(st)) {
        continue;
      }

      // `if (!C) { return; } B` where B's leading exprents run before the return's own
      // instruction: a guard clause only reaches its following statements after the return, so
      // code laid out before it was the source's then arm. The source wrote `if (C) { B-leading }
      // else { return; } B-rest`, as javac lays a finally block's unlock out.
      if (printInvertedGuard(buf, indent, i)) {
        notempty = true;
        i++;
        continue;
      }

      // The if this run was folded into prints this block after its closing brace: the target
      // laid it out past the branch shell, so the arm ends where the source's brace was.
      if (RoundTrip.isAfterIf(st)) {
        continue;
      }

      // A branch printed this block inside its braces: the target's code lay inside the loop the
      // branch exits, so the source ran it there and the tree only placed it here.
      if (RoundTrip.isPrintedInBranch(st)) {
        continue;
      }

      // A guard printed this exit already; the rest of the sequence became unconditional.
      if (RoundTrip.isConsumedGuardExit(st)) {
        continue;
      }

      // The loop moved this block after its closing brace; the run's first statement printed the
      // break that reaches it, and nothing after a break in the same block can run.
      if (RoundTrip.isDeferredExit(st) && i > 0 && RoundTrip.isDeferredExit(stats.get(i - 1))) {
        continue;
      }

      // A negated pattern guard: `instanceof; ifeq/ifne T; …checkcast; astore…; goto U` with T
      // exactly the instruction after that goto and U the code the source ran after the if. The
      // tree kept the test positively with U as its then arm and the arm at T as the statement
      // after it; print the source's order back — the negated test around the arm at T, U after
      // it. That arm's own return was folded into the method's end when it was the last thing the
      // printer wrote, so print the target's return again here; a value return is the tree's to
      // print, and without one the shape stays as printed.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          && !hasContent(stats.subList(i + 2, stats.size()))) {
        int exit = RoundTrip.negatedPatternGuard(ifStatement.getHeadexprent(),
          ifStatement.getIfstat(), stats.get(i + 1));
        boolean printedExit = exits(stats.get(i + 1));
        if (exit >= 0 && RoundTrip.exitsAt(exit) && (printedExit || RoundTrip.isVoidReturn(exit))) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          head.setCondition(RoundTrip.negateCondition(head.getCondition()));
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          for (int k = i + 1; k < stats.size(); k++) {
            buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
          }
          if (!printedExit) {
            TextBuffer returnLine = new TextBuffer();
            returnLine.appendIndent(indent + 1).append("return;").appendLineSeparator();
            RoundTrip.mapSynthesizedLine(returnLine, exit);
            buf.append(returnLine);
          }
          buf.appendIndent(indent).append("}").appendLineSeparator();
          // The arm prints last here; its trailing return may be the method's own final return,
          // which the source did not write and the closing brace stands for.
          Runnable restoreReturn = RoundTrip.hideImplicitFinalReturn(ifStatement.getIfstat());
          try {
            buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
          }
          finally {
            if (restoreReturn != null) {
              restoreReturn.run();
            }
          }
          notempty = true;
          break;
        }
      }

      // A `||` arm with its body left after it: print the test positively and the body as its arm.
      if (printDisjunctiveArm(buf, indent, i)) {
        notempty = true;
        break;
      }

      // A local whose scope the target's table proves ended at this block's boundary: the slot is
      // handed to a later local, which a source can only do by closing the block the first one
      // lived in. Print `{ … }` around the run of exprents that starts at the declaration and ends
      // where the table says its scope did. Both ends are exprent boundaries — the declaration's
      // own store and the last instruction of the run's last statement — so the braces land
      // exactly where javac closed the source's block.
      if (RoundTrip.selector("bareblock")) {
        int[] run = RoundTrip.handoverRun(stats, i, RoundTrip.blockEnd(this));
        // Closing the block takes every local it declares out of scope: a use past the boundary
        // has to land in the row that takes its slot over at a store, which the printer writes as
        // a declaration. Anything else and the brace would name a variable that is gone.
        if (run != null && splittable(stats.get(run[0]))
            && (run[3] < 0 || splittable(stats.get(run[2])))
            && RoundTrip.closesCleanly(run[5], run[6])) {
          int openExp = run[1];
          int closeExp = run[3];
          List<Exprent> leading = RoundTrip.leadingExprents(stats.get(run[0]));
          if (openExp > 0) {
            // The declarations before the block's own stay outside it.
            buf.append(ExprProcessor.listToJava(leading.subList(0, openExp), indent));
          }
          RoundTrip.armSplitDeclarations(run[5], run[6]);
          buf.appendIndent(indent).append("{").appendLineSeparator();
          // A block nested in this run that ends where this one does closes on the same brace;
          // the source's single brace is this one.
          int previousEnd = RoundTrip.handoverEnd(run[6]);
          try {
            if (run[2] == run[0] && closeExp < 0) {
              printFrom(stats.get(run[0]), openExp, indent + 1, buf);
              buf.appendIndent(indent).append("}").appendLineSeparator();
            } else if (run[2] == run[0]) {
              buf.append(ExprProcessor.listToJava(leading.subList(openExp, closeExp + 1), indent + 1));
              buf.appendIndent(indent).append("}").appendLineSeparator();
              printAfter(stats.get(run[0]), closeExp, indent, buf);
            } else {
              printFrom(stats.get(run[0]), openExp, indent + 1, buf);
              for (int j = run[0] + 1; j < run[2]; j++) {
                buf.append(ExprProcessor.jmpWrapper(stats.get(j), indent + 1, true));
              }
              List<Statement> childSplit = run.length > 9 && run[9] >= 0
                ? ((SequenceStatement) stats.get(run[2])).getStats() : null;
              if (childSplit != null) {
                // The boundary is between two of the closing sequence's statements: its print
                // splits there, and the rest runs after the brace.
                for (int k = 0; k <= run[9]; k++) {
                  buf.append(ExprProcessor.jmpWrapper(childSplit.get(k), indent + 1, true));
                }
                buf.appendIndent(indent).append("}").appendLineSeparator();
                for (int k = run[9] + 1; k < childSplit.size(); k++) {
                  buf.append(ExprProcessor.jmpWrapper(childSplit.get(k), indent, true));
                }
              } else if (closeExp < 0) {
                buf.append(ExprProcessor.jmpWrapper(stats.get(run[2]), indent + 1, true));
                buf.appendIndent(indent).append("}").appendLineSeparator();
              } else {
                List<Exprent> tail = RoundTrip.leadingExprents(stats.get(run[2]));
                buf.append(ExprProcessor.listToJava(tail.subList(0, closeExp + 1), indent + 1));
                buf.appendIndent(indent).append("}").appendLineSeparator();
                printAfter(stats.get(run[2]), closeExp, indent, buf);
              }
            }
          } finally {
            RoundTrip.restoreHandoverEnd(previousEnd);
          }
          notempty = true;
          i = run[2];
          continue;
        }
      }
      // A local whose row ends at a statement boundary inside this block, without a handover to
      // prove it — a loop's head variable is the common case. Closing the block there keeps the
      // scope javac recorded; the printer still has no `for` for the loop it belongs to.
      if (RoundTrip.selector("bareblock")) {
        int windowEnd = i + 1 < stats.size()
          ? Math.max(RoundTrip.blockEnd(st), RoundTrip.firstOffset(stats.get(i + 1)) - 1)
          : RoundTrip.blockEnd(st);
        int[] scope = RoundTrip.nestedBlockScope(st, windowEnd, RoundTrip.blockEnd(this));
        // The local has to be declared by this statement itself, and the block it lived in has to
        // reach past it; otherwise the run is just this statement and the braces buy nothing.
        if (scope != null && scope[0] <= RoundTrip.blockEnd(st)) {
          int close = -1;
          for (int j = i; j < stats.size(); j++) {
            int end = RoundTrip.blockEnd(stats.get(j));
            // The closing brace sits right after the run's last instruction; the back edge that
            // ends the statement may add up to a few bytes past the last exprent offset.
            if (Math.abs(end - scope[1]) <= 5) {
              close = j;
              break;
            }
            if (end > scope[1]) {
              break;
            }
          }
          boolean exact = close > i;
          // Closing the block moves everything after it out of the local's scope: allowed only
          // when nothing there reads the local. Where the target hands the slot to a later local,
          // the scope provably ended and no read can follow; that also bounds the block for a run
          // whose last statement ends well before the scope does (a loop's back edge).
          VarExprent declared = declaredAt(st, scope[0], scope[2]);
          boolean reusable = declared != null && RoundTrip.slotReusedAfter(scope[2], scope[1]);
          boolean basicBlock = st.getExprents() != null && !st.getExprents().isEmpty();
          if (!exact && basicBlock) {
            for (int j = i; j < stats.size(); j++) {
              int end = RoundTrip.blockEnd(stats.get(j));
              boolean atBoundary = j + 1 >= stats.size()
                || RoundTrip.statementStart(stats.get(j + 1)) >= scope[1];
              if (end <= scope[1] + 5 && atBoundary) {
                close = j;
                break;
              }
              if (end > scope[1] + 5) {
                break;
              }
            }
            // A loop's own variable opens at the loop's head; its declaration belongs to the for
            // statement, not to a block in front of it.
            if (close > i && loopHeadReads(stats.get(close), scope[0], scope[2])) {
              close = -1;
              basicBlock = false;
            }
          }
          boolean closedEarly = exact
            ? !RoundTrip.slotUsedFrom(stats, close + 1, scope[2])
            : close > i && basicBlock
              && (!RoundTrip.slotUsedFrom(stats, close + 1, scope[2])
                  || reusable && !usedLater(stats, close + 1, declared));
          if (close > i && close < stats.size() - 1 && closedEarly) {
            int split = RoundTrip.exprentAtOffset(st, scope[0]);
            List<Exprent> exprents = st.getExprents();
            if (split < 0 && exprents != null && !exprents.isEmpty()) {
              // The declaration's store can sit past every exprent's recorded offsets; the block's
              // last exprent is the one that declares it.
              split = exprents.size() - 1;
            }
            if (exprents != null && split > 0) {
              // The declaration is one exprent of this block: the exprents before it stay outside.
              buf.append(ExprProcessor.listToJava(exprents.subList(0, split), indent));
            }
            buf.appendIndent(indent).append("{").appendLineSeparator();
            if (exprents != null && split >= 0) {
              buf.append(ExprProcessor.listToJava(exprents.subList(split, exprents.size()), indent + 1));
            } else {
              buf.append(ExprProcessor.jmpWrapper(st, indent + 1, true));
            }
            for (int j = i + 1; j <= close; j++) {
              buf.append(ExprProcessor.jmpWrapper(stats.get(j), indent + 1, true));
            }
            buf.appendIndent(indent).append("}").appendLineSeparator();
            notempty = true;
            i = close;
            continue;
          }
        }
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
        if (!RoundTrip.holdsDeferredBreak(ifStatement)) {
          // The enclosing arm prints the break after its closing brace: the target's block closed
          // before the break's jump, so the source wrote no else here.
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.appendIndent(indent + 1)
            .append(ifStatement.getIfEdge().getType() == StatEdge.TYPE_BREAK ? "break;" : "continue;")
            .appendLineSeparator();
        }
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        break;
      }

      // `if (C) continue; body` in the source; the decompiler printed its mirror `if (!C) { body }`.
      // The target's branch-then-goto shape and line table prove the continue. The mirror is the
      // loop's whole remaining body, so the guard is exact only when this sequence is the loop
      // body and the if is its last statement; otherwise the continue would skip the tail.
      // A run of such guards merged into one test splits back at the continue jumps the target
      // records for each statement, exactly as the same shape does when the if prints itself
      // (IfStatement's mirror): each guard's goto ends where the next test begins.
      if (st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isPatternMatched() && !ifStatement.isLabeled() && !st.isLabeled()
          && ifStatement.getIfstat() != null
          && i == stats.size() - 1 && endsLoopBody()
          && RoundTrip.printContinueGuard(ifStatement.getHeadexprent(), this)) {
        Exprent condition = ifStatement.getHeadexprent().getCondition();
        Exprent source = condition instanceof FunctionExprent not
            && not.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT
            && not.getLstOperands().size() == 1
          ? not.getLstOperands().get(0)
          : RoundTrip.negateCondition(condition);
        List<Exprent> ors = IfStatement.orOperands(source);
        List<List<Exprent>> groups = RoundTrip.guardGroups(ifStatement.getHeadexprent(), ors, this);
        if (groups == null) {
          groups = java.util.Collections.singletonList(java.util.Collections.singletonList(source));
        }
        // Each guard compiles the printed `continue;` to the goto the target's table puts on the
        // line the source wrote it on; the line alignment has to see that jump to place it. A
        // cut-out group's jump sits right before the next group's first instruction, and the
        // head's own test is the one the if's last branch belongs to.
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        for (int groupIndex = 0; groupIndex < groups.size(); groupIndex++) {
          List<Exprent> group = groups.get(groupIndex);
          int gotoOffset = groupIndex + 1 < groups.size()
            ? RoundTrip.continueGotoBefore(groups.get(groupIndex + 1).get(0), this)
            : RoundTrip.continueGoto(ifStatement.getHeadexprent());
          IfExprent guard = (IfExprent) ifStatement.getHeadexprent().copy();
          guard.setCondition(IfStatement.orOf(group));
          buf.appendIndent(indent).append(guard.toJava(indent)).append(" {").appendLineSeparator();
          TextBuffer continueLine = new TextBuffer();
          continueLine.appendIndent(indent + 1).append("continue;").appendLineSeparator();
          if (gotoOffset >= 0) {
            continueLine.addStartBytecodeMapping(gotoOffset);
          }
          buf.append(continueLine);
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
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
          // An if/else whose last branch lands on the arm the tree prints as then has its arms
          // the wrong way round: the jump between them is the join, not a written continue.
          && !RoundTrip.swapIfArmsByLastTarget(ifStatement.getHeadexprent(), ifStatement.getIfstat())
          && i == stats.size() - 1 && endsLoopBody()
          && RoundTrip.printContinueElse(ifStatement.getHeadexprent(), this)) {
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(ifStatement.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
        TextBuffer continueLine = new TextBuffer();
        continueLine.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        if (RoundTrip.continueElseSite() >= 0) {
          continueLine.addStartBytecodeMapping(RoundTrip.continueElseSite());
        }
        buf.append(continueLine);
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

      // `if (A) { …exit } if (B b) { … } rest` where B's pattern variable took a slot below a
      // local the first arm declares and the second arm ends in a copy of the method's final
      // return that the arm jumps over the rest to: javac hoists an else-if chain's binding
      // above the first arm (the target's table proves it by the slot order), and a jump that
      // skips the rest to the return the tail prints is the else the source wrote around it.
      if (i + 2 < stats.size() && st instanceof IfStatement first
          && first.iftype == IfStatement.IFTYPE_IF && first.getElsestat() == null
          && !first.isLabeled() && first.getIfstat() != null
          && first.getIfstat().getExprents() != null
          && stats.get(i + 1) instanceof IfStatement second
          && second.iftype == IfStatement.IFTYPE_IF && second.getElsestat() == null
          && !second.isLabeled() && !stats.get(i + 1).isLabeled() && !isLabeled()
          && second.getIfstat() != null && second.getFirst() != null
          && RoundTrip.selector("elseifelse")
          && exits(first.getIfstat())
          && patternSlot(second) >= 0 && firstDeclaredSlot(first.getIfstat()) > patternSlot(second)) {
        Statement arm = second.getIfstat();
        Statement copy = arm instanceof SequenceStatement seq && !seq.getStats().isEmpty()
          ? seq.getStats().getLast() : arm;
        int target = RoundTrip.firstOffset(copy);
        int elseStart = RoundTrip.lastBranchTarget(second.getHeadexprent());
        int from = RoundTrip.lastEnd(first.getIfstat());
        int tailEnd = RoundTrip.lastEnd(stats.get(stats.size() - 1));
        if (target > 0 && elseStart > 0 && from >= 0 && from <= elseStart
            && RoundTrip.isTailReturnCopy(copy)
            && RoundTrip.statementStart(stats.get(i + 2)) >= elseStart
            && tailEnd > 0 && tailEnd < target
            && RoundTrip.jumpsOnto(from, elseStart, target)
            && exits(stats.get(stats.size() - 1))) {
          // The copy stands for the jump the arm's own closing brace carries; printing it here
          // would emit a second return.
          List<Statement> dropped = List.of();
          if (copy != arm) {
            dropped = List.of(copy);
            ((SequenceStatement) arm).getStats().removeWithKey(copy.id);
          }
          try {
            buf.append(ExprProcessor.listToJava(first.varDefinitions, indent));
            buf.append(first.getFirst().toJava(indent));
            buf.appendIndent(indent).append(first.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
            buf.append(ExprProcessor.jmpWrapper(first.getIfstat(), indent + 1, true));
            buf.appendIndent(indent).append("} else ");
            buf.append(second.getFirst().toJava(indent));
            buf.append(second.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
            buf.append(ExprProcessor.jmpWrapper(arm, indent + 1, true));
            // The target's table puts the else's first statement on the closing brace's line:
            // the jump over the else takes that line, and a statement line of its own would add
            // an entry the target does not have.
            buf.appendIndent(indent).append("} else { ");
            TextBuffer lead = ExprProcessor.jmpWrapper(stats.get(i + 2), indent + 1, true);
            lead.setStart(TextUtil.getIndentString(indent + 1).length());
            buf.append(lead);
            for (int k = i + 3; k < stats.size(); k++) {
              buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 3));
            }
            buf.appendIndent(indent).append("}").appendLineSeparator();
          }
          finally {
            for (Statement stat : dropped) {
              arm.getStats().addWithKey(stat, stat.id);
            }
          }
          notempty = true;
          i = stats.size() - 1;
          continue;
        }
      }

      // `if (A) { … } T …` where the condition's false branch lands on T and a jump inside the arm
      // lands on the far side of T: the target's then arm jumps straight over the else content, so
      // the source wrote `if (A) { … } else { T }`. A guard's arm can only fall through to T; a
      // jump that skips T is what proves the else arm.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && !isLabeled()
          && ifStatement.getIfstat() != null
          && RoundTrip.selector("elseover")
          && RoundTrip.lastBranchTarget(ifStatement.getHeadexprent()) >= 0
          && RoundTrip.lastBranchTarget(ifStatement.getHeadexprent()) <= RoundTrip.statementStart(stats.get(i + 1))) {
        Statement arm = ifStatement.getIfstat();
        int from = i > 0 ? RoundTrip.lastEnd(stats.get(i - 1)) : RoundTrip.statementStart(ifStatement);
        int elseStart = RoundTrip.lastBranchTarget(ifStatement.getHeadexprent());
        int elseEnd = -1;
        int previousEnd = -1;
        for (int k = i + 1; k < stats.size(); k++) {
          int end = RoundTrip.lastEnd(stats.get(k));
          if (end < 0 || end <= previousEnd) {
            break;
          }
          previousEnd = end;
          if (from >= 0 && RoundTrip.jumpsOnto(from, elseStart, end)) {
            elseEnd = k;
            break;
          }
          // The writer folded a void return the source ended the else with into the method's
          // exit; the jump over the else lands past that return, not at the last exprent.
          int withReturn = endWithDroppedReturn(stats.get(k), end);
          if (withReturn != end && from >= 0 && RoundTrip.jumpsOnto(from, elseStart, withReturn)) {
            elseEnd = k;
            break;
          }
        }
        int elseStop = elseEnd < 0 ? -1
          : endWithDroppedReturn(stats.get(elseEnd), RoundTrip.lastEnd(stats.get(elseEnd)));
        // A sequence arm may carry the join it jumps to as its own last statement; the sequence
        // holds the same statements after the if, so print those once and leave the arm's copy out.
        int bodyEnd = arm.getStats().size();
        boolean finalReturnTail = false;
        // The dropped tail that this print itself has to print after the else: the arm ended on
        // the join, and nothing here or in the enclosing flow would print it otherwise.
        List<Statement> joinTail = List.of();
        if (elseStop > 0 && bodyEnd > 0 && RoundTrip.firstOffset(arm.getStats().get(bodyEnd - 1)) >= elseStop) {
          while (bodyEnd > 0 && RoundTrip.firstOffset(arm.getStats().get(bodyEnd - 1)) >= elseStop) {
            bodyEnd--;
            if (RoundTrip.isTailReturnCopy(arm.getStats().get(bodyEnd))) {
              finalReturnTail = true;
            }
          }
          // The join has to be printed exactly once after the else: by the next statement here,
          // by the enclosing flow when the copy is the method's own final return, or by this
          // print when the dropped tail itself begins at the join.
          int join;
          if (elseEnd + 1 < stats.size()) {
            join = RoundTrip.firstOffset(stats.get(elseEnd + 1));
          } else if (finalReturnTail) {
            // The copy's own instruction is the method's last return, which the enclosing flow
            // prints; when that return is not the next thing this sequence would print (an
            // enclosing else prints between them), the copy's offset still names the join.
            join = RoundTrip.selector("elsejoin")
              ? RoundTrip.firstOffset(arm.getStats().get(bodyEnd)) : RoundTrip.printedAfter(this);
            if (join != elseStop) {
              int enclosing = RoundTrip.printedAfter(this);
              join = enclosing == elseStop ? enclosing : join;
            }
          } else if (bodyEnd < arm.getStats().size()
              && RoundTrip.firstOffset(arm.getStats().get(bodyEnd)) == elseStop) {
            join = elseStop;
            joinTail = new ArrayList<>(arm.getStats().subList(bodyEnd, arm.getStats().size()));
          } else {
            join = -1;
          }
          if (bodyEnd == 0 || join != elseStop) {
            elseEnd = -1;
          }
        }
        // The arm's last basic block may hold the join as trailing exprents instead: the block
        // starts before the else and ends on the join's own instruction, which only code after
        // the if/else can own. Split them off so the arm prints without them. The arm itself is
        // that block when the whole then-arm is one basic block.
        List<Exprent> joinExprents = null;
        Statement joinExprentHost = null;
        if (elseEnd > i && elseStop > 0 && joinTail.isEmpty()
            && elseEnd + 1 >= stats.size()) {
          Statement lastArm = bodyEnd > 0 ? arm.getStats().get(bodyEnd - 1) : arm;
          List<Exprent> exprents = lastArm.getExprents();
          if (exprents != null && exprents.size() > 1) {
            int split = -1;
            for (int k = 0; k < exprents.size(); k++) {
              Exprent e = exprents.get(k);
              int start = e.bytecode == null || e.bytecode.isEmpty() ? -1 : e.bytecode.nextSetBit(0);
              if (start >= elseStop) {
                split = k;
                break;
              }
            }
            if (split > 0) {
              joinExprents = new ArrayList<>(exprents.subList(split, exprents.size()));
              joinExprentHost = lastArm;
            }
          }
        }
        // A pattern-matched if joins this rule only when the split below proves its then arm
        // ended on the join; otherwise the pattern printers own the shape.
        boolean printElseOver = elseEnd > i && elseStart >= 0 && elseStop > elseStart
            && (bodyEnd > 0 || joinExprents != null)
            && (!ifStatement.isPatternMatched() || joinExprents != null)
            && !fallsInto(arm, elseStart, elseStop)
            && !breaksOut(arm, elseStop);
        if (printElseOver && joinExprents != null
            && !RoundTrip.hoistJoinDeclarations(ifStatement, arm, joinExprents)) {
          // A local the moved code reads is declared where the arm held it and cannot move:
          // print the arm whole instead, as before the rule existed.
          joinExprents = null;
          joinExprentHost = null;
          printElseOver = bodyEnd > 0 && !ifStatement.isPatternMatched();
        }
        if (printElseOver) {
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(ifStatement.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
          if (arm instanceof SequenceStatement armSeq) {
            // Print the arm through its own statement so its printer rules still apply, without
            // the join it absorbed: the sequence prints that once, after the else.
            List<Statement> tail = new ArrayList<>(
              armSeq.getStats().subList(Math.min(bodyEnd, armSeq.getStats().size()), armSeq.getStats().size()));
            for (Statement dropped : tail) {
              armSeq.getStats().removeWithKey(dropped.id);
            }
            List<Exprent> savedExprents = null;
            if (joinExprentHost != null) {
              savedExprents = joinExprentHost.getExprents();
              joinExprentHost.setExprents(new ArrayList<>(
                savedExprents.subList(0, savedExprents.size() - joinExprents.size())));
            }
            try {
              RoundTrip.pushJoinOffset(elseStop);
              buf.append(ExprProcessor.jmpWrapper(armSeq, indent + 1, true));
            } finally {
              RoundTrip.popJoinOffset();
              if (savedExprents != null) {
                joinExprentHost.setExprents(savedExprents);
              }
              for (Statement dropped : tail) {
                armSeq.getStats().addWithKey(dropped, dropped.id);
              }
            }
          } else {
            // The arm's trailing jump is the loop's own continue: the else arm's end carries it.
            Statement previous = RoundTrip.suppressJump(arm);
            List<Exprent> savedExprents = null;
            if (joinExprentHost != null) {
              savedExprents = joinExprentHost.getExprents();
              joinExprentHost.setExprents(new ArrayList<>(
                savedExprents.subList(0, savedExprents.size() - joinExprents.size())));
            }
            try {
              RoundTrip.pushJoinOffset(elseStop);
              buf.append(ExprProcessor.jmpWrapper(arm, indent + 1, true));
            } finally {
              RoundTrip.popJoinOffset();
              RoundTrip.restoreJump(previous);
              if (savedExprents != null) {
                joinExprentHost.setExprents(savedExprents);
              }
            }
          }
          if (!(elseEnd == i + 1 && IfStatement.printElseIfArm(buf, indent, stats.get(i + 1)))) {
            buf.appendIndent(indent).append("} else {").appendLineSeparator();
            for (int k = i + 1; k <= elseEnd; k++) {
              buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
            }
            // The source may have ended the else with a void return the writer folded into the
            // method's exit; the target's instruction ending where the join starts proves it.
            int joinStart = joinExprents != null && !joinExprents.isEmpty()
              ? RoundTrip.exprentStart(joinExprents.get(0))
              : elseEnd + 1 < stats.size() ? RoundTrip.firstOffset(stats.get(elseEnd + 1)) : -1;
            if (!RoundTrip.printsVoidReturn(stats.get(elseEnd))) {
              RoundTrip.appendVoidReturnEnding(buf, joinStart, indent + 1);
            }
            buf.appendIndent(indent).append("}").appendLineSeparator();
          }
          // The join the arm absorbed prints here, once, where the source wrote it.
          for (Statement dropped : joinTail) {
            buf.append(ExprProcessor.jmpWrapper(dropped, indent, false));
          }
          if (joinExprents != null) {
            buf.append(ExprProcessor.listToJava(joinExprents, indent));
          }
          notempty = true;
          i = elseEnd;
          continue;
        }
      }

      // `if (A) { … return; } rest` where A declares an instanceof pattern variable and the first
      // local declared after the if takes a fresh slot: javac keeps the pattern variable's slot
      // alive through an else arm, so a local that does not reuse it proves the source wrote one.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && ifStatement.isPatternMatched() && ifStatement.getIfstat() != null
          && ifStatement.getHeadexprent() != null
          && !(ifStatement.getHeadexprent().getCondition() instanceof FunctionExprent negated
               && negated.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT)
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled() && !isLabeled()
          && !(stats.get(i + 1) instanceof IfStatement next && patternVar(next) != null)
          && RoundTrip.selector("elsechain")
          && exits(ifStatement.getIfstat())) {
        int pattern = patternSlot(ifStatement);
        int fresh = pattern < 0 ? -1 : firstDeclaredSlot(stats.get(i + 1));
        if (fresh >= 0 && fresh != pattern) {
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(ifStatement.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          for (int k = i + 1; k < stats.size(); k++) {
            buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
          }
          buf.appendIndent(indent).append("}").appendLineSeparator();
          notempty = true;
          i = stats.size();
          continue;
        }
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
        List<Statement> afterIf = RoundTrip.afterShell(ifStatement.getIfstat(), stats.subList(i + 1, stats.size()),
          RoundTrip.lastEnd(ifStatement.getIfstat()));
        RoundTrip.markAfterIf(afterIf);
        if (!IfStatement.printSplitIf(buf, head, splitArm, ifStatement.getIfstat(), indent, false)) {
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(splitArm, indent + 1, true));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
        for (Statement after : afterIf) {
          // The block's own jump edge is the flow into the statement the if's parent prints
          // next, so only its content moves here.
          buf.append(after.toJava(indent));
        }
        RoundTrip.releaseAfterIf(afterIf);
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

      // `if (C) { A; rest; return Y; } return X;` where the target's then-arm ends on A with a goto
      // over the returning else block: the source wrote `if (C) { A } else { return X; } rest`.
      if (i + 1 == stats.size() - 1 && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && !ifStatement.isPatternMatched()
          && ifStatement.getIfstat() != null
          // The else block only has to end in an exit; it may carry statements of its own before it.
          && endsWithExit(java.util.Collections.singletonList(stats.get(i + 1)))
          && !RoundTrip.declaresLocal(stats.get(i + 1))) {
        SequenceStatement thenSeq = ifStatement.getIfstat() instanceof SequenceStatement seq ? seq : null;
        int split = thenSeq != null ? RoundTrip.thenArmSplit(thenSeq, stats.get(i + 1)) : -1;
        List<Statement> rest = split >= 0
          ? thenSeq.getStats().subList(split + 1, thenSeq.getStats().size())
          : List.of();
        if (split >= 0 && rest.stream().noneMatch(RoundTrip::declaresLocalIn)) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          for (int k = 0; k <= split; k++) {
            buf.append(ExprProcessor.jmpWrapper(thenSeq.getStats().get(k), indent + 1, k == 0));
          }
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          for (int k = 0; k < rest.size(); k++) {
            buf.append(ExprProcessor.jmpWrapper(rest.get(k), indent, k == 0));
          }
          notempty = true;
          break;
        }
        // The same shape with the arm's statements held as exprents of one basic block.
        List<Exprent> armExprents = ifStatement.getIfstat().getExprents();
        int exprentSplit = armExprents == null ? -1 : RoundTrip.thenExprentSplit(armExprents, stats.get(i + 1));
        if (exprentSplit >= 0
            && armExprents.subList(exprentSplit + 1, armExprents.size()).stream()
               .noneMatch(e -> e instanceof VarExprent v && v.isDefinition())) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.listToJava(armExprents.subList(0, exprentSplit + 1), indent + 1));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          buf.append(ExprProcessor.listToJava(armExprents.subList(exprentSplit + 1, armExprents.size()), indent));
          notempty = true;
          break;
        }
        // The split falls inside the arm's first statement: the target's then-arm ends on the
        // prelude the decompiler attached to the following if's head (`x = …;` before `if (…)`).
        if (split < 0 && thenSeq != null && !thenSeq.getStats().isEmpty()
            && thenSeq.getStats().get(0) instanceof IfStatement firstIf) {
          int gotoStart = RoundTrip.gotoBeforeTail(stats.get(i + 1));
          List<Exprent> headExprents = firstIf.getFirst().getExprents();
          if (gotoStart >= 0 && headExprents != null && !headExprents.isEmpty()
              && RoundTrip.headExprentsEnd(firstIf) == gotoStart) {
            IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
            buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
            buf.append(ifStatement.getFirst().toJava(indent));
            buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
            buf.append(ExprProcessor.listToJava(headExprents, indent + 1));
            buf.appendIndent(indent).append("} else {").appendLineSeparator();
            buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 1, true));
            buf.appendIndent(indent).append("}").appendLineSeparator();
            List<Exprent> saved = firstIf.getFirst().getExprents();
            firstIf.getFirst().setExprents(new java.util.ArrayList<>());
            try {
              for (int k = 0; k < thenSeq.getStats().size(); k++) {
                buf.append(ExprProcessor.jmpWrapper(thenSeq.getStats().get(k), indent, k == 0));
              }
            } finally {
              firstIf.getFirst().setExprents(saved);
            }
            notempty = true;
            break;
          }
        }
      }

      // `if (C) { break; } rest` where the target's branch lands straight on the loop exit: the
      // source wrote `if (!C) { rest } else { break; }`. The guard form would have compiled a
      // branch over a jump to the exit, and the scan would have recorded that pair.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && ifStatement.getIfstat() == null && !ifStatement.isLabeled() && !st.isLabeled()
          && !ifStatement.isPatternMatched()
          && hasContent(stats.subList(i + 1, stats.size()))
          && stats.subList(i + 1, stats.size()).stream().noneMatch(RoundTrip::declaresLocal)
          && RoundTrip.breakBranchLandsOnExit(ifStatement.getHeadexprent(), ifStatement)) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(
          new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, true));
        if (!RoundTrip.holdsDeferredBreak(ifStatement)) {
          // The break this arm stood for is the one the enclosing arm prints after its brace: the
          // source closed the arm there and wrote no else.
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.appendIndent(indent + 1).append("break;").appendLineSeparator();
        }
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        break;
      }

      // `if (!C) continue; rest` where rest is the method's whole exit and the target's branch
      // lands on the loop's back edge: the source wrote `if (C) { rest }` and let control fall
      // back to the head. A written continue would have jumped over a goto to the head instead.
      if (i + 2 == stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && ifStatement.getIfstat() == null && !ifStatement.isLabeled() && !st.isLabeled()
          && !ifStatement.isPatternMatched()
          && singleExit(stats.get(i + 1)) instanceof ExitExprent
          && ifStatement.getIfEdge() != null
          && ifStatement.getIfEdge().getType() == StatEdge.TYPE_CONTINUE
          && ifStatement.getIfEdge().explicit
          && RoundTrip.branchFallsToBackEdge(ifStatement.getHeadexprent(), ifStatement)) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 1, true));
        buf.appendIndent(indent).append("}").appendLineSeparator();
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
          if (RoundTrip.gotoJumpsOverArm(ifStatement.getIfstat(), tail)) {
            buf.appendIndent(indent).append("} else {").appendLineSeparator();
            buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
            buf.appendIndent(indent).append("}").appendLineSeparator();
          } else {
            buf.appendIndent(indent).append("}").appendLineSeparator();
            buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
          }
          notempty = true;
          i++;
          continue;
        }
      }

      // `if (!C) { E } rest…` where the target's branch lands on E and a join jump inside the
      // statements printed after the guard skips E: the source wrote `if (C) { rest… } else { E }`.
      // E is the arm the source wrote as its else and ends the path; printing it as a guard would
      // run the source's then arm on E's path as well.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          && hasContent(stats.subList(i + 1, stats.size()))) {
        java.util.List<Statement> run = stats.subList(i + 1, stats.size());
        int continuation = RoundTrip.realElseContinuation(ifStatement.getHeadexprent(),
          ifStatement.getIfstat(), run);
        if (continuation >= 0) {
          // The statements starting before the join are the source's then arm; a basic block that
          // straddles the join keeps its exprents before it in the arm and prints the rest after.
          int end = i + 1;
          while (end < stats.size() && RoundTrip.statementOffset(stats.get(end)) < continuation) {
            end++;
          }
          Statement lastThen = stats.get(end - 1);
          java.util.List<Exprent> thenExprents = lastThen.getExprents();
          int cut = thenExprents == null ? -1 : thenExprents.size();
          if (thenExprents != null) {
            for (int k = 0; k < thenExprents.size(); k++) {
              if (RoundTrip.firstExprentOffset(thenExprents.get(k)) >= continuation) {
                cut = k;
                break;
              }
            }
          }
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          head.setCondition(RoundTrip.negateCondition(head.getCondition()));
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          for (int k = i + 1; k < end - 1; k++) {
            buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
          }
          if (thenExprents == null) {
            buf.append(ExprProcessor.jmpWrapper(lastThen, indent + 1, end - 1 == i + 1));
          } else if (cut == thenExprents.size()) {
            buf.append(ExprProcessor.jmpWrapper(lastThen, indent + 1, end - 1 == i + 1));
          } else if (cut > 0) {
            buf.append(ExprProcessor.listToJava(thenExprents.subList(0, cut), indent + 1));
          }
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          if (thenExprents != null && cut < thenExprents.size()) {
            buf.append(ExprProcessor.listToJava(thenExprents.subList(cut, thenExprents.size()), indent));
          }
          for (int k = end; k < stats.size(); k++) {
            buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent, k == end));
          }
          notempty = true;
          break;
        }
      }

      // `if (C) { A } rest…` where the target's branch lands on the first statement after the
      // guard and A ends with a join jump over all of them: the source wrote `if (C) { A }
      // else { rest… }`. A written guard has no such jump: its branch skips the arm.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          && hasContent(stats.subList(i + 1, stats.size()))
          && RoundTrip.guardThenArm(ifStatement.getHeadexprent(), ifStatement.getIfstat(),
               stats.subList(i + 1, stats.size()))) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        Statement arm = ifStatement.getIfstat();
        // The arm ends with a copy of the method's final return; the joined flow prints that
        // return once after the whole if, so the copy must not print inside the arm.
        Statement armCopy = null;
        if (arm instanceof SequenceStatement armSeq && !armSeq.getStats().isEmpty()) {
          Statement lastChild = armSeq.getStats().get(armSeq.getStats().size() - 1);
          if (RoundTrip.tailReturnCopyOffset(lastChild) >= 0) {
            armCopy = lastChild;
          }
        }
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        if (armCopy != null) {
          ((SequenceStatement) arm).getStats().removeWithKey(armCopy.id);
        }
        try {
          buf.append(ExprProcessor.jmpWrapper(arm, indent + 1, true));
        } finally {
          if (armCopy != null) {
            ((SequenceStatement) arm).getStats().addWithKey(armCopy, armCopy.id);
          }
        }
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(
          new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, true));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        break;
      }

      // `if (C) { A } return X;` where the target's then-arm ends with a jump over the returning
      // block: the source wrote `if (C) { A } else { return X; }`, and only the false path returns.
      // Without that jump the arm falls into the return and the trailing print is the faithful one.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          && singleExit(stats.get(i + 1)) instanceof ExitExprent elseExit
          && elseExit.getExitType() == ExitExprent.Type.RETURN
          && RoundTrip.gotoPastsExit(ifStatement.getIfstat(), stats.get(i + 1))) {
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(ifStatement.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(stats.get(i + 1), indent + 1, true));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        i++;
        continue;
      }

      // `if (C) { A } else { B }` where A falls through: our arm is B and the statements after it
      // are A, which the bytecode places *before* it — a guard always keeps its arm first. Print
      // the source's two arms back in that order.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          && armLeaves(ifStatement.getIfstat())
          && stats.subList(i + 1, stats.size()).stream().noneMatch(RoundTrip::declaresLocalIn)
          && RoundTrip.restPrecedesArm(stats.get(i + 1), ifStatement.getIfstat())
          && RoundTrip.soleEntry(ifStatement.getIfstat())
          && RoundTrip.swapIfArmsByTarget(ifStatement.getHeadexprent(), ifStatement.getIfstat(), stats.get(i + 1))) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        // The rest runs only up to the branch shell; the target laid the statements past it out
        // after the if, and the arm's jump went over them to the exit block. The split decides
        // what stays in the arm before the arm's declarations print: a variable the moved block
        // reads has its declaration printed above the if.
        int shellEnd = RoundTrip.lastEnd(ifStatement.getIfstat());
        List<Statement> restStats = stats.subList(i + 1, stats.size());
        List<Statement> afterIf = RoundTrip.afterShell(ifStatement.getIfstat(), restStats, shellEnd);
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        Statement rest = new SequenceStatement(restStats);
        // One basic block can hold exprents from both sides of the shell: the ones at or past it
        // ran after the arm, so print them after the brace and keep only the head inside.
        Statement straddle = null;
        List<Exprent> shellTail = java.util.Collections.emptyList();
        if (afterIf.isEmpty() && !restStats.isEmpty()) {
          Statement last = restStats.get(restStats.size() - 1);
          shellTail = RoundTrip.exprentsAfterShell(last, ifStatement.getIfstat(), restStats, shellEnd);
          if (!shellTail.isEmpty()) {
            straddle = last;
          }
        }
        // Both arms may end with a copy of the method's final return: the jumps go there, and the
        // enclosing flow prints the return once after the whole if, so the copies fall out.
        Statement elseArm = ifStatement.getIfstat();
        Statement elseCopy = elseArm instanceof SequenceStatement elseSeq && !elseSeq.getStats().isEmpty()
          ? elseSeq.getStats().get(elseSeq.getStats().size() - 1) : null;
        int exitStart = elseCopy == null ? -1 : RoundTrip.tailReturnCopyOffset(elseCopy);
        boolean joinAfterArms = exitStart >= 0
          && (RoundTrip.joinOffset() == exitStart || RoundTrip.printedAfter(this) == exitStart);
        if (!joinAfterArms && !restStats.isEmpty()) {
          exitStart = RoundTrip.tailReturnCopyOffset(restStats.get(restStats.size() - 1));
          joinAfterArms = exitStart >= 0
            && (RoundTrip.joinOffset() == exitStart || RoundTrip.printedAfter(this) == exitStart);
        }
        Statement restCopy = joinAfterArms && !restStats.isEmpty()
            && RoundTrip.isTailReturnCopy(restStats.get(restStats.size() - 1))
          ? restStats.get(restStats.size() - 1) : null;
        if (restCopy != null) {
          rest = new SequenceStatement(restStats.subList(0, restStats.size() - 1));
        }
        RoundTrip.markAfterIf(afterIf);
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        List<Exprent> savedExprents = straddle == null ? null : straddle.getExprents();
        if (straddle != null) {
          straddle.setExprents(new ArrayList<>(savedExprents.subList(0, savedExprents.size() - shellTail.size())));
        }
        try {
          RoundTrip.pushJoinOffset(exitStart);
          buf.append(ExprProcessor.jmpWrapper(rest, indent + 1, true));
        } finally {
          RoundTrip.popJoinOffset();
          if (straddle != null) {
            straddle.setExprents(savedExprents);
          }
        }
        // The target's local table can prove the source wrote this arm flat, as statements the
        // enclosing block ran after the then arm, and never as an else block: its declarations
        // then live in the enclosing block, and a brace here would move their scope.
        boolean flatArm = RoundTrip.armWasFlat(elseArm);
        buf.appendIndent(indent).append(flatArm ? "}" : "} else {").appendLineSeparator();
        if (elseCopy != null && joinAfterArms && RoundTrip.isTailReturnCopy(elseCopy)) {
          ((SequenceStatement) elseArm).getStats().removeWithKey(elseCopy.id);
        }
        try {
          RoundTrip.pushJoinOffset(exitStart);
          buf.append(ExprProcessor.jmpWrapper(elseArm, flatArm ? indent : indent + 1, true));
        } finally {
          RoundTrip.popJoinOffset();
          if (elseCopy != null && joinAfterArms && RoundTrip.isTailReturnCopy(elseCopy)) {
            ((SequenceStatement) elseArm).getStats().addWithKey(elseCopy, elseCopy.id);
          }
        }
        if (!flatArm) {
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
        if (!shellTail.isEmpty()) {
          buf.append(ExprProcessor.listToJava(shellTail, indent));
        }
        for (Statement after : afterIf) {
          buf.append(after.toJava(indent));
        }
        RoundTrip.releaseAfterIf(afterIf);
        notempty = true;
        break;
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
            && RoundTrip.exitAfterBody(ifStatement.getIfstat(), stats.get(i + 1))
            // Only the mirror form's condition branches onto the exit block: the guard
            // `if (C) { …; return X; } rest` branches past the arm to the rest, and its exit
            // block is a loop exit or a plain return that the line table cannot tell apart.
            && RoundTrip.branchesToBody(ifStatement.getHeadexprent(), ifStatement.getIfstat())) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          head.setCondition(RoundTrip.negateCondition(head.getCondition()));
          Statement movedRest = new SequenceStatement(stats.subList(i + 1, stats.size()));
          boolean asElse = RoundTrip.gotoJumpsOverArm(ifStatement.getIfstat(), movedRest)
            || RoundTrip.jumpsOnto(RoundTrip.firstOffset(movedRest),
                 RoundTrip.lastEnd(ifStatement.getIfstat()), RoundTrip.lastEnd(ifStatement.getIfstat()));
          // The rest runs only up to the branch shell; the target laid the statements past it
          // out after the if, and the arm's jump went over them to the exit block. The split
          // decides what stays in the arm before the arm's declarations print: a variable the
          // moved block reads has its declaration printed above the if.
          List<Statement> afterIf = RoundTrip.afterShell(ifStatement.getIfstat(), stats.subList(i + 1, stats.size()),
            RoundTrip.lastEnd(ifStatement.getIfstat()));
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          // The arms' copies of the method's final return stand for the jump the source took
          // there; the enclosing flow prints that return once, so the arms fall out to it.
          int exitStart = headExit.bytecode == null ? -1 : headExit.bytecode.nextSetBit(0);
          boolean joinAfterArms = asElse && exitStart >= 0
            && (RoundTrip.joinOffset() == exitStart || RoundTrip.printedAfter(this) == exitStart);
          List<Statement> restAll = new ArrayList<>(stats.subList(i + 1, stats.size()));
          if (joinAfterArms && !restAll.isEmpty()
              && RoundTrip.isTailReturnCopy(restAll.get(restAll.size() - 1))) {
            restAll.remove(restAll.size() - 1);
            movedRest = new SequenceStatement(restAll);
          }
          Statement elseArm = ifStatement.getIfstat();
          Statement elseCopy = null;
          if (joinAfterArms && elseArm instanceof SequenceStatement elseSeq && !elseSeq.getStats().isEmpty()) {
            Statement lastElse = elseSeq.getStats().get(elseSeq.getStats().size() - 1);
            if (RoundTrip.isTailReturnCopy(lastElse)) {
              elseCopy = lastElse;
            }
          }
          RoundTrip.markAfterIf(afterIf);
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(movedRest, indent + 1, true));
          if (asElse) {
            buf.appendIndent(indent).append("} else {").appendLineSeparator();
            if (elseCopy != null) {
              ((SequenceStatement) elseArm).getStats().removeWithKey(elseCopy.id);
            }
            try {
              RoundTrip.pushJoinOffset(exitStart);
              buf.append(ExprProcessor.jmpWrapper(elseArm, indent + 1, true));
            } finally {
              RoundTrip.popJoinOffset();
              if (elseCopy != null) {
                ((SequenceStatement) elseArm).getStats().addWithKey(elseCopy, elseCopy.id);
              }
            }
            buf.appendIndent(indent).append("}").appendLineSeparator();
          } else {
            buf.appendIndent(indent).append("}").appendLineSeparator();
            buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
          }
          for (Statement after : afterIf) {
            buf.append(after.toJava(indent));
          }
          RoundTrip.releaseAfterIf(afterIf);
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
          && RoundTrip.opensTrailingBlock(stats.get(i + 1), elseArmEnd())) {
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

      // `int i = 0; for (int size = …; i < size; i++)` where the target gives `i` a scope that
      // opens at the loop's head and closes with the loop: the source declared both in the for
      // init, and the hoisted form makes the next loop's variable take another slot.
      if (i + 1 < stats.size() && st.type == Statement.StatementType.BASIC_BLOCK
          && st.getExprents() != null && !st.getExprents().isEmpty()
          && stats.get(i + 1) instanceof DoStatement loop
          && loop.getLooptype() == DoStatement.Type.FOR
          && loop.getInitExprent() instanceof AssignmentExprent init
          && init.getLeft() instanceof VarExprent initVar
          && loop.getConditionExprent() != null && loop.getIncExprent() != null
          && RoundTrip.forInitContinues(st.getExprents().get(st.getExprents().size() - 1), loop, init,
               i + 2 < stats.size() ? RoundTrip.firstOffset(stats.get(i + 2)) : -1)) {
        Exprent declaration = st.getExprents().get(st.getExprents().size() - 1);
        buf.append(ExprProcessor.listToJava(st.varDefinitions, indent));
        for (int k = 0; k < st.getExprents().size() - 1; k++) {
          buf.appendIndent(indent).append(st.getExprents().get(k).toJava(indent)).append(";").appendLineSeparator();
        }
        buf.appendIndent(indent).append("for (").append(declaration.toJava(indent))
          .append(", ").append(initVar.getName()).append(" = ").append(init.getRight().toJava(indent))
          .append("; ").append(loop.getConditionExprent().toJava(indent))
          .append("; ").append(loop.getIncExprent().toJava(indent)).append(") {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(loop.getFirst(), indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        notempty = true;
        i++;
        continue;
      }

      // `if (C) { A; return; } rest` where the return is not the arm's own: the target jumped
      // over the rest to it, and its instruction is the method's last, so the source wrote
      // `if (C) { A } else { rest }` and let the closing brace close the method. Printing the
      // return inside the arm would turn the else into an early exit.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !stats.get(i + 1).isLabeled()
          && ifStatement.getIfstat() != null
          // A pattern-matched if joins on the arm's goto over the rest to the method's return;
          // otherwise the pattern printers own the shape.
          && (!ifStatement.isPatternMatched()
              || RoundTrip.armJumpsOverRestToFinalReturn(ifStatement.getIfstat(), stats.get(i + 1)))
          && RoundTrip.returnsPastRest(ifStatement.getIfstat(), stats.get(i + 1),
               stats.get(stats.size() - 1))) {
        List<Exprent> armExprents = ifStatement.getIfstat().getExprents();
        Exprent foldedReturn = armExprents.remove(armExprents.size() - 1);
        try {
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(ifStatement.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(
            new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
        } finally {
          armExprents.add(foldedReturn);
        }
        notempty = true;
        break;
      }

      // `if (C) { rest } tail`: the target's last condition branch lands on the rest, which javac
      // only does for the arm the source wrote after the test, so the source wrote the negated
      // test with the tail first: `if (!C) { tail } rest`. Both arms have to leave on their own —
      // otherwise one printed form falls into the other arm the other does not reach — and no
      // local the tail declares may be read after it, since its scope ends at the brace.
      if (i + 1 < stats.size() && st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isLabeled() && !ifStatement.isPatternMatched()
          && ifStatement.getIfstat() != null && cannotComplete(ifStatement.getIfstat())
          && hasContent(stats.subList(i + 1, stats.size()))
          && RoundTrip.swapIfArmsByLastTarget(ifStatement.getHeadexprent(), ifStatement.getIfstat())) {
        Statement tail = new SequenceStatement(stats.subList(i + 1, stats.size()));
        if (cannotComplete(tail) && !tailLocalsUsedAfter(tail, ifStatement.getIfstat())) {
          IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
          head.setCondition(RoundTrip.negateCondition(head.getCondition()));
          buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
          buf.append(ifStatement.getFirst().toJava(indent));
          buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
          for (int k = i + 1; k < stats.size(); k++) {
            buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
          }
          buf.appendIndent(indent).append("}").appendLineSeparator();
          // As a try body's print, the trailing return's own instruction may sit past the
          // protected range: the source wrote it after the try/catch, and the try prints it.
          if (RoundTrip.deferTryReturn(ifStatement.getIfstat()) == null) {
            buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent, false));
          }
          notempty = true;
          break;
        }
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

  /**
   * Prints a labelled block back as the source shape it encodes. javac labels a block only when a
   * jump leaves it from the middle; a run of ifs whose arms all leave the block, and one if whose
   * inverted arm the printer could not place against the arm the source wrote, are both source
   * shapes with no label at all. False, printing nothing, for any other block.
   */
  private boolean printLabelledChain(TextBuffer buf, int indent) {
    return stats.size() >= 2
      && (printChainArms(buf, indent) || printFlippedArms(buf, indent) || printLabelledElse(buf, indent));
  }

  /**
   * Prints a labelled block whose first if's arm jumps over the statements after it as the if/else
   * the source wrote. The arm's own completion leaving the block is a jump a written
   * {@code if (C) { arm } rest} cannot produce — that form falls into rest — so the source wrote
   * an else arm there. The target's last condition branch says which arm the source printed
   * first: landing on the tree's arm means the source wrote the negated test with that arm last.
   */
  private boolean printLabelledElse(TextBuffer buf, int indent) {
    if (!RoundTrip.selector("elsearm") || stats.size() != 2
        || !(stats.get(0) instanceof IfStatement branch) || !isPlainIf(branch)) {
      return false;
    }
    Statement arm = branch.getIfstat();
    Statement rest = stats.get(1);
    StatEdge exit = terminalExit(arm);
    if (exit == null || !exit.explicit || exit.getType() != StatEdge.TYPE_BREAK || exit.closure != this) {
      return false;
    }
    if (breaksToLabelCount(arm, this) != 1) {
      return false;
    }
    boolean fallsToRest = false;
    for (StatEdge edge : branch.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() == rest) {
        fallsToRest = true;
      }
    }
    if (!fallsToRest || !hasContent(stats.subList(1, stats.size()))) {
      return false;
    }
    // The statements after the branch reach the block's end without a jump of their own — anywhere
    // in their own flow, not only at its top: a break to this label inside them is a jump the
    // source wrote there, and hiding the label would re-shape the block around it.
    for (int i = 1; i < stats.size(); i++) {
      if (breaksToLabel(stats.get(i), this)) {
        return false;
      }
    }
    if (!terminalExitsOnly(this, this) || !labelConfined()) {
      return false;
    }
    boolean flipped = RoundTrip.swapIfArmsByLastTarget(branch.getHeadexprent(), arm)
      || (RoundTrip.swapIfArmsByLine(arm, rest)
          && !RoundTrip.polaritySelfConsistent(branch.getHeadexprent(), arm, rest));
    IfExprent head = (IfExprent) branch.getHeadexprent().copy();
    if (flipped) {
      head.setCondition(RoundTrip.negateCondition(head.getCondition()));
    }
    Statement thenArm = flipped ? rest : arm;
    Statement elseArm = flipped ? arm : rest;
    if (!RoundTrip.isHeadConsumed(branch)) {
      buf.append(branch.getFirst().toJava(indent));
    }
    buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
    Statement previous = RoundTrip.hideClosure(this);
    try {
      appendElseArm(buf, indent, thenArm == rest ? null : thenArm);
      buf.appendIndent(indent).append("} else {").appendLineSeparator();
      appendElseArm(buf, indent, elseArm == rest ? null : elseArm);
      buf.appendIndent(indent).append("}").appendLineSeparator();
    }
    finally {
      RoundTrip.restoreClosure(previous);
    }
    return true;
  }

  /** The number of explicit jumps under this statement that leave the block through its label. */
  private static int breaksToLabelCount(Statement stat, Statement closure) {
    int count = 0;
    for (StatEdge edge : stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.explicit && edge.getType() != StatEdge.TYPE_REGULAR && edge.closure == closure) {
        count++;
      }
    }
    for (Statement child : stat.getStats()) {
      count += breaksToLabelCount(child, closure);
    }
    return count;
  }

  /** True when any explicit jump under this statement leaves the block through its label. */
  private static boolean breaksToLabel(Statement stat, Statement closure) {
    for (StatEdge edge : stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.explicit && edge.getType() != StatEdge.TYPE_REGULAR && edge.closure == closure) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (breaksToLabel(child, closure)) {
        return true;
      }
    }
    return false;
  }

  /** Prints one arm: a single statement, or the block's run when it is the statements after the if. */
  private void appendElseArm(TextBuffer buf, int indent, Statement arm) {
    if (arm != null) {
      buf.append(ExprProcessor.jmpWrapper(arm, indent + 1, true));
      return;
    }
    for (int i = 1; i < stats.size(); i++) {
      buf.append(ExprProcessor.jmpWrapper(stats.get(i), indent + 1, i == 1));
    }
  }

  /**
   * Prints a labelled run of ifs as the source's {@code else if} chain. Every arm leaves the block
   * through the same break, so the arms are the chain's arms: each one that is not taken runs the
   * next test, and the label only exists because the compiler could not link the last branch to
   * the block's end. The break edges are the chain's own exits and print nothing.
   */
  private boolean printChainArms(TextBuffer buf, int indent) {
    if (!isChainOf(this, this) || !terminalExitsOnly(this, this) || !labelConfined()) {
      return false;
    }
    Statement previous = RoundTrip.hideClosure(this);
    try {
      appendChain(buf, indent);
    }
    finally {
      RoundTrip.restoreClosure(previous);
    }
    return true;
  }

  /**
   * Whether the block is a run of ifs whose arms all leave through the same break: the clauses of
   * the source's {@code else if} chain. The last arm may instead fall out of the block, which is
   * the chain's own end.
   */
  private static boolean isChainOf(SequenceStatement sequence, Statement closure) {
    List<Statement> stats = sequence.stats;
    if (stats.size() < 3) {
      return false;
    }
    for (Statement stat : stats) {
      if (!isPlainIf(stat)) {
        return false;
      }
    }
    for (int i = 0; i < stats.size() - 1; i++) {
      StatEdge exit = terminalExit(stats.get(i));
      if (exit == null || !exit.explicit || exit.getType() != StatEdge.TYPE_BREAK || exit.closure != closure) {
        return false;
      }
    }
    StatEdge last = terminalExit(stats.get(stats.size() - 1));
    return last == null || last.getType() == StatEdge.TYPE_BREAK && last.closure == closure;
  }

  /**
   * Prints a run of ifs whose arms each end by re-running the exit that follows them as the
   * source's {@code else if} chain and the one exit after it. An arm that leaves through that
   * exit can only do so by skipping every arm below it, which is what a chain's arm does; the
   * exit itself is the same instruction in the class file, so it prints once, at the end.
   */
  private boolean printTailChain(TextBuffer buf, int indent) {
    if (stats.size() < 2 || RoundTrip.hiddenClosure() == null) {
      return false;
    }
    Statement tail = stats.get(stats.size() - 1);
    if (!isSingleExit(tail)) {
      return false;
    }
    boolean duplicated = false;
    for (int i = 0; i < stats.size() - 1; i++) {
      Statement arm = stats.get(i);
      if (!(arm instanceof IfStatement clause) || !isPlainIf(clause)) {
        return false;
      }
      duplicated |= sameExit(tailStatement(clause.getIfstat()), tail);
    }
    if (!duplicated) {
      return false;
    }
    boolean open = false;
    for (int i = 0; i < stats.size() - 1; i++) {
      Statement arm = stats.get(i);
      Statement copy = tailStatement(((IfStatement) arm).getIfstat());
      Statement previous = sameExit(copy, tail) ? RoundTrip.skipStatement(copy) : null;
      try {
        open = appendArm(buf, indent, arm, i + 1 < stats.size() - 1, i == 0, open);
      }
      finally {
        RoundTrip.restoreStatement(previous);
      }
    }
    buf.append(ExprProcessor.jmpWrapper(tail, indent, true));
    return true;
  }

  /** The statement's last exprent, when the whole statement is a lone return or throw. */
  private static boolean isSingleExit(Statement stat) {
    if (stat == null) {
      return false;
    }
    List<Exprent> exprents = stat.getExprents();
    return exprents != null && exprents.size() == 1 && exprents.get(0) instanceof ExitExprent;
  }

  /** The statement the body ends with on the printed tail path, or null. */
  private static Statement tailStatement(Statement stat) {
    while (stat != null) {
      List<Statement> children = stat.getStats();
      if (children == null || children.isEmpty()) {
        return isSingleExit(stat) ? stat : null;
      }
      stat = children.get(children.size() - 1);
    }
    return null;
  }

  /**
   * Whether the two statements print the same exit instruction. The class file keeps one
   * {@code return} where the tree holds a copy per arm; the offset is what says so.
   */
  private static boolean sameExit(Statement first, Statement second) {
    if (!isSingleExit(first) || !isSingleExit(second)) {
      return false;
    }
    Exprent a = first.getExprents().get(0);
    Exprent b = second.getExprents().get(0);
    if (a.bytecode == null || b.bytecode == null || a.bytecode.isEmpty() || b.bytecode.isEmpty()
        || a.getClass() != b.getClass()) {
      return false;
    }
    return a.bytecode.nextSetBit(0) == b.bytecode.nextSetBit(0);
  }

  /**
   * Prints the run inside braces and the break after them when the target's table proves the
   * source closed this block before the break: a local declared in the run has its scope ending
   * at a goto another jump lands on, and the run leaves only through a break out of a switch.
   * The statement holding the edge keeps its print; the break is printed here, after the brace.
   */
  private boolean printClosedBlockBreak(TextBuffer buf, int indent) {
    if (stats.isEmpty() || !varDefinitions.isEmpty() || getParent() instanceof SwitchStatement
        || isLabeled()) {
      return false;
    }
    Statement last = stats.get(stats.size() - 1);
    List<StatEdge> exits = last.getAllSuccessorEdges();
    if (exits.size() != 1 || exits.get(0).getType() != StatEdge.TYPE_BREAK
        || !exits.get(0).explicit || exits.get(0).labeled
        || !(exits.get(0).closure instanceof SwitchStatement)) {
      return false;
    }
    int close = RoundTrip.blockClosingBreak(this);
    if (close <= 0) {
      return false;
    }
    buf.appendIndent(indent).append("{").appendLineSeparator();
    Statement previous = RoundTrip.deferBreakTo(exits.get(0).closure);
    try {
      for (Statement stat : stats) {
        buf.append(ExprProcessor.jmpWrapper(stat, indent + 1, true));
      }
    } finally {
      RoundTrip.restoreDeferredBreak(previous);
    }
    buf.appendIndent(indent).append("}").appendLineSeparator();
    TextBuffer line = new TextBuffer();
    line.appendIndent(indent);
    int at = line.length();
    line.append("break;").appendLineSeparator();
    line.addBytecodeMappingAt(at, close, null, null);
    buf.append(line);
    return true;
  }

  /** Appends the arms as {@code if (a) { … } else if (b) { … } …,} the source's chain. */
  private void appendChain(TextBuffer buf, int indent) {
    boolean open = false;
    for (int i = 0; i < stats.size(); i++) {
      open = appendArm(buf, indent, stats.get(i), i + 1 < stats.size(), i == 0, open);
    }
  }

  /**
   * Appends one arm of a chain — {@code if} for the first and {@code else if} for the rest — and
   * reports whether it left its closing brace for the next arm's {@code else} line, which is how
   * the source writes {@code } else if (c) {} on one line.
   */
  private static boolean appendArm(TextBuffer buf, int indent, Statement arm, boolean more,
                                   boolean first, boolean previousOpen) {
    Statement previous = more ? RoundTrip.openArm(arm) : null;
    TextBuffer content;
    boolean open = false;
    try {
      content = ExprProcessor.jmpWrapper(arm, indent, false);
    }
    finally {
      open = more && RoundTrip.closeArm(previous);
    }
    if (first) {
      buf.append(content);
    }
    else {
      buf.appendIndent(indent).append(previousOpen ? "} else " : "else ");
      content.setStart(TextUtil.getIndentString(indent).length());
      buf.append(content);
    }
    return open;
  }

  /**
   * The closing offset of this sequence when it is an if's else arm: a guard's own else inside
   * it ends at the same brace, and the table records that scope end. -1 otherwise.
   */
  private int elseArmEnd() {
    return getParent() instanceof IfStatement parent && parent.getElsestat() == this
      ? RoundTrip.lastEnd(this) : -1;
  }

  /**
   * Whether this unlabelled block is the rest of the else-if chain the enclosing print is
   * rebuilding: its arms leave through the block the caller is unwrapping, so the source wrote
   * them as further {@code else if} clauses rather than as statements after an arm.
   */
  public boolean printsAsChainArm() {
    Statement closure = RoundTrip.hiddenClosure();
    return closure != null && stats.size() >= 2 && varDefinitions.isEmpty()
      && isChainOf(this, closure);
  }

  /**
   * Prints a labelled block whose first if is inverted against the source. The arm ends with the
   * break that leaves the block, so it never runs the statements after it: those are the source's
   * other arm, and the printed form is {@code if (!C) { rest } else { chain }} written the way
   * the source wrote it — every arm of the chain is embedded in the if, so swapping them changes
   * nothing but the branch targets the compiler picked.
   */
  private boolean printFlippedArms(TextBuffer buf, int indent) {
    // Two statements are the printer's own if/else; a third means the arm the source wrote after
    // the block really was a run of statements, which is what makes the swap the source's shape.
    if (stats.size() < 3 || !(stats.get(0) instanceof IfStatement branch) || !isPlainIf(branch)) {
      return false;
    }
    Statement chain = branch.getIfstat();
    Statement rest = stats.get(1);
    StatEdge exit = terminalExit(chain);
    if (exit == null || !exit.explicit || exit.getType() != StatEdge.TYPE_BREAK || exit.closure != this) {
      return false;
    }
    boolean fallsToRest = false;
    for (StatEdge edge : branch.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() == rest) {
        fallsToRest = true;
      }
    }
    if (!fallsToRest) {
      return false;
    }
    // Swapping the arms is only the source's order when the block the printer took as the then
    // arm comes after the one it left outside: the target's lines say which arm ran first.
    if (!RoundTrip.swapIfArmsByLine(chain, rest)) {
      return false;
    }
    // The statements after the branch reach the block's end without a jump of their own; a break
    // among them would be one the swap loses.
    for (int i = 1; i < stats.size(); i++) {
      for (StatEdge edge : stats.get(i).getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
        if (edge.explicit && edge.getType() != StatEdge.TYPE_REGULAR && edge.closure == this) {
          return false;
        }
      }
    }
    if (!terminalExitsOnly(this, this) || !labelConfined()) {
      return false;
    }
    IfExprent head = (IfExprent) branch.getHeadexprent().copy();
    head.setCondition(RoundTrip.negateCondition(branch.getHeadexprent().getCondition()));
    // The statements that ran before the test live on the head block; the flip prints the if
    // itself, so they have to be printed here or they are lost.
    if (!RoundTrip.isHeadConsumed(branch)) {
      buf.append(branch.getFirst().toJava(indent));
    }
    buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
    for (int i = 1; i < stats.size(); i++) {
      buf.append(ExprProcessor.jmpWrapper(stats.get(i), indent + 1, i == 1));
    }
    buf.appendIndent(indent).append("} else {").appendLineSeparator();
    Statement previous = RoundTrip.hideClosure(this);
    try {
      buf.append(ExprProcessor.jmpWrapper(chain, indent + 1, false));
    }
    finally {
      RoundTrip.restoreClosure(previous);
    }
    buf.appendIndent(indent).append("}").appendLineSeparator();
    return true;
  }

  /** An if with a single arm, no label and no pattern: a clause an else-if chain can be made of. */
  private static boolean isPlainIf(Statement stat) {
    return stat instanceof IfStatement arm
      && arm.iftype == IfStatement.IFTYPE_IF
      && arm.getElsestat() == null
      && arm.getIfstat() != null
      && !arm.isLabeled()
      && !arm.isPatternMatched()
      && arm.getHeadexprent() != null
      && arm.getHeadexprent().getCondition() != null;
  }

  /**
   * The jump the statement's last printed statement ends with, or null. Walks the tail path the
   * same way the printer does, so the edge found is the one that will be printed last.
   */
  private static StatEdge terminalExit(Statement stat) {
    while (true) {
      List<StatEdge> edges = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
      if (edges.size() == 1 && edges.get(0).getType() != StatEdge.TYPE_REGULAR) {
        return edges.get(0);
      }
      List<Statement> children = stat.getStats();
      if (children == null || children.isEmpty()) {
        return null;
      }
      stat = children.get(children.size() - 1);
    }
  }

  /**
   * Whether every explicit jump to the closure under this statement is that statement's only
   * successor, so it is an arm's own exit and prints nothing once the label is gone.
   */
  private static boolean terminalExitsOnly(Statement stat, Statement closure) {
    List<StatEdge> edges = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    for (StatEdge edge : edges) {
      if (edge.explicit && edge.getType() != StatEdge.TYPE_REGULAR && edge.closure == closure
          && edges.size() != 1) {
        return false;
      }
    }
    for (Statement child : stat.getStats()) {
      if (!terminalExitsOnly(child, closure)) {
        return false;
      }
    }
    return true;
  }

  /** Whether nothing outside this block jumps to its label, so the label has no printed use. */
  private boolean labelConfined() {
    Statement root = this;
    while (root.getParent() != null) {
      root = root.getParent();
    }
    return !breaksTo(root, this);
  }

  private static boolean breaksTo(Statement stat, Statement closure) {
    if (stat == closure) {
      return false;
    }
    for (StatEdge edge : stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.closure == closure) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (breaksTo(child, closure)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Prints a {@code ||} arm of an else-if chain back as the source's positive test. A disjunction
   * compiles as two branch blocks that both lead into the same arm, so the arm's body is one of the
   * condition's branch targets; a simple test or a conjunction only branches to its skip target,
   * which is where the next arm begins. The compiler saw the arm's second incoming edge as a join,
   * so this block holds the chain inverted with the arm's body after it; the class file's branch
   * target is what proves the source wrote the test positively. Prints
   * {@code if (C) { body; break label; }} and then the rest of the chain, the source's else-if
   * shape. False, printing nothing, when the block is not this shape.
   */
  private boolean printDisjunctiveArm(TextBuffer buf, int indent, int i) {
    if (i + 1 >= stats.size() || !(stats.get(i) instanceof IfStatement arm)
        || arm.iftype != IfStatement.IFTYPE_IF || arm.getElsestat() != null || arm.getIfstat() == null
        || arm.isLabeled() || arm.isPatternMatched()
        || arm.getHeadexprent() == null || arm.getHeadexprent().getCondition() == null) {
      return false;
    }
    List<Statement> after = stats.subList(i + 1, stats.size());
    Statement lastBody = stats.get(stats.size() - 1);
    List<StatEdge> bodyExit = lastBody.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    StatEdge exit = terminalBreak(arm.getIfstat());
    // The body's own printed break is the flip's break when the printer kept it explicit; when it
    // did not, the flip prints one, and it has to print a labeled jump. A body that ends in a
    // return or throw never reaches the chain, so no break is needed and none may be printed.
    boolean needsBreak = !bodyExit.isEmpty() && !bodyExit.get(0).explicit && !cannotComplete(lastBody);
    // The body moves into the then arm and the chain out of it: a local declared in either would
    // end its scope somewhere else, and a slot the target hands out again would move.
    if (!hasContent(after) || exit == null || exit.closure == null
        || after.stream().anyMatch(RoundTrip::declaresLocal)
        || RoundTrip.declaresLocal(arm.getIfstat())
        // The chain has to leave the block on its own break. A regular edge into the statements
        // that follow would mean they run after the chain too, which the flip would lose.
        || flowsInto(arm.getIfstat(), after)
        // The body has to leave the same way; anything else is a different flow.
        || !bodyLeaves(bodyExit, lastBody, exit)
        || (needsBreak && !exit.labeled)
        // The statement's own condition carries the offsets of the instructions that built it, and
        // its range start includes them; a first-offset walk misses them once they are in the head.
        || !disjunctiveTest(arm.getHeadexprent(), after.get(0).getStartEndRange().start)) {
      return false;
    }
    IfExprent head = (IfExprent) arm.getHeadexprent().copy();
    head.setCondition(RoundTrip.negateCondition(arm.getHeadexprent().getCondition()));
    // The declarations that ran before the test live on the head block; the flip prints the if
    // itself, so they have to be printed here or they are lost.
    buf.append(ExprProcessor.listToJava(arm.varDefinitions, indent));
    buf.append(arm.getFirst().toJava(indent));
    buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
    for (int k = i + 1; k < stats.size(); k++) {
      buf.append(ExprProcessor.jmpWrapper(stats.get(k), indent + 1, k == i + 1));
    }
    if (needsBreak) {
      buf.appendIndent(indent + 1).append("break label").append(exit.closure.id).append(";").appendLineSeparator();
    }
    buf.appendIndent(indent).append("}").appendLineSeparator();
    // As a try body's print, the trailing arm's return may sit past the protected range: the
    // source wrote it after the try/catch, and the try prints it there.
    if (RoundTrip.deferTryReturn(arm.getIfstat()) == null) {
      buf.append(ExprProcessor.jmpWrapper(arm.getIfstat(), indent, false));
    }
    return true;
  }

  /**
   * Whether the class file proves the if's test is a disjunction with the following statement as
   * its arm: every operand contributes exactly one branch, and the branches land on two different
   * targets, one of them the arm. A simple test has a single branch (an early-return guard's one
   * branch lands on the rest without a second target), and a conjunction's branches all land on the
   * same skip target. An operand that is itself a short-circuit keeps its own branches, so the
   * printed form has to be a plain conjunction as well.
   */
  private static boolean disjunctiveTest(IfExprent head, int bodyStart) {
    Exprent condition = head.getCondition();
    if (!(condition instanceof FunctionExprent and)
        || and.getFuncType() != FunctionExprent.FunctionType.BOOLEAN_AND) {
      return false;
    }
    List<Exprent> operands = new ArrayList<>();
    if (!plainOperands(and, operands)) {
      return false;
    }
    int[] targets = RoundTrip.branchTargets(head);
    if (targets.length < 2 || targets.length != operands.size()) {
      return false;
    }
    int other = -1;
    boolean toBody = false;
    for (int target : targets) {
      if (target == bodyStart) {
        toBody = true;
      } else if (other < 0) {
        other = target;
      } else if (other != target) {
        return false;
      }
    }
    return toBody && other >= 0;
  }

  /** The operands of a conjunction, flattened; false when one of them is itself a disjunction. */
  private static boolean plainOperands(Exprent condition, List<Exprent> out) {
    if (condition instanceof FunctionExprent function
        && function.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND
        && function.getLstOperands().size() == 2) {
      return plainOperands(function.getLstOperands().get(0), out)
        && plainOperands(function.getLstOperands().get(1), out);
    }
    for (Exprent part : condition.getAllExprents(true, true)) {
      if (part instanceof FunctionExprent function
          && function.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_OR) {
        return false;
      }
    }
    out.add(condition);
    return true;
  }

  /**
   * The break edge the arm's last printed statement ends with, or null. The flip has to leave the
   * block by the same break the inverted arm used, so the label comes from that edge.
   */
  private static StatEdge terminalBreak(Statement stat) {
    while (true) {
      List<StatEdge> edges = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
      if (edges.size() == 1 && edges.get(0).getType() != StatEdge.TYPE_REGULAR && edges.get(0).explicit) {
        return edges.get(0);
      }
      List<Statement> children = stat.getStats();
      if (children == null || children.isEmpty()) {
        return null;
      }
      stat = children.get(children.size() - 1);
    }
  }

  /**
   * Whether the body leaves the block the way the flipped arm does: through the same break, or
   * with an exit of its own when it has no edge. Anything else — a regular edge, a break to a
   * different label — is a different flow, and the print it already has is kept.
   */
  private static boolean bodyLeaves(List<StatEdge> bodyExit, Statement lastBody, StatEdge exit) {
    if (bodyExit.isEmpty()) {
      return exits(lastBody);
    }
    return bodyExit.size() == 1 && bodyExit.get(0).getType() == StatEdge.TYPE_BREAK
      && bodyExit.get(0).closure == exit.closure;
  }

  /**
   * Whether the statement cannot complete normally, so a statement printed after it would be
   * unreachable: a block ending in a return or throw, an if with both arms like that, or a
   * sequence whose last statement is. A statement printed last before a jump can also not fall
   * into it after an explicit break; that case prints its own jump and adds nothing.
   */
  private static boolean cannotComplete(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      return !exprents.isEmpty() && exprents.get(exprents.size() - 1) instanceof ExitExprent;
    }
    if (stat instanceof IfStatement ifStatement) {
      return ifStatement.getElsestat() != null && ifStatement.getIfstat() != null
        && cannotComplete(ifStatement.getIfstat()) && cannotComplete(ifStatement.getElsestat());
    }
    if (stat instanceof SequenceStatement || stat instanceof RootStatement) {
      List<Statement> children = stat.getStats();
      return !children.isEmpty() && cannotComplete(children.get(children.size() - 1));
    }
    return false;
  }

  /** Whether any statement under the root has a direct edge into one of these statements. */
  private static boolean flowsInto(Statement root, List<Statement> targets) {
    for (StatEdge edge : root.getAllDirectSuccessorEdges()) {
      if (targets.contains(edge.getDestination())) {
        return true;
      }
    }
    for (Statement child : root.getStats()) {
      if (flowsInto(child, targets)) {
        return true;
      }
    }
    return false;
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
        // The else arm is the loop's last work when the enclosing if ends the loop body: the
        // sibling's guard hoists the arm out of the block, and everything in it then runs last
        // (ProjectileUtil's exact-hit guard lives in the raider-style guard's else arm).
        if (ifStatement.getIfstat() != stat
            && !(ifStatement.getElsestat() == stat && RoundTrip.endsLoopBody(ifStatement))) {
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

  /**
   * Whether this loop's own head declares the local that opens at that offset: the variable the
   * for statement owns, which the printer binds to the loop rather than to a block before it.
   */
  private static boolean loopHeadReads(Statement stat, int start, int slot) {
    if (!(stat instanceof DoStatement loop)) {
      return false;
    }
    for (Exprent exprent : new Exprent[]{loop.getConditionExprent(), loop.getIncExprent()}) {
      if (exprent == null) {
        continue;
      }
      for (Exprent part : exprent.getAllExprents(true, true)) {
        if (part instanceof VarExprent variable && variable.getLVT() != null
            && variable.getLVT().getStartPC() == start && variable.getLVT().getIndex() == slot) {
          return true;
        }
      }
    }
    return false;
  }

  /** The definition of the local this statement declares at that offset and slot, or null. */
  private static VarExprent declaredAt(Statement stat, int start, int slot) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents == null) {
      return null;
    }
    for (Exprent exprent : exprents) {
      for (Exprent part : exprent.getAllExprents(true, true)) {
        if (part instanceof VarExprent variable && variable.isDefinition() && variable.getLVT() != null
            && variable.getLVT().getStartPC() == start && variable.getLVT().getIndex() == slot) {
          return variable;
        }
      }
    }
    return null;
  }

  /** Whether this statement's print can be cut at an exprent boundary without losing an edge. */
  private static boolean splittable(Statement stat) {
    if (stat == null || stat.getExprents() == null && !(stat instanceof IfStatement)) {
      return false;
    }
    if (stat instanceof IfStatement ifstat) {
      if (!ifstat.getVarDefinitions().isEmpty()) {
        return false;
      }
      Statement head = ifstat.getFirst();
      if (head == null || head.getExprents() == null) {
        return false;
      }
    }
    List<StatEdge> successors = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (successors.size() == 1) {
      StatEdge edge = successors.get(0);
      // A trailing break or continue is printed by the wrapper this path does not call.
      return edge.getType() == StatEdge.TYPE_REGULAR || !edge.explicit;
    }
    return true;
  }

  /**
   * Whether a block closing at this statement's end would be a block of its own: a sequence prints
   * no brace around its statements, but a loop body, an arm or a try already does.
   */
  private static boolean printsOwnEnd(Statement stat) {
    if (!(stat.getParent() instanceof SequenceStatement sequence)) {
      return false;
    }
    Statement above = sequence.getParent();
    return above == null || !(above instanceof DoStatement || above instanceof IfStatement
      || above instanceof CatchAllStatement || above instanceof CatchStatement
      || above instanceof SynchronizedStatement);
  }

  /** Prints a statement from its exprent {@code from} on, followed by its own body. */
  private static void printFrom(Statement stat, int from, int indent, TextBuffer buf) {
    List<Exprent> exprents = stat.getExprents();
    boolean closeAtEnd = exprents != null && printsOwnEnd(stat);
    if (exprents != null) {
      buf.append(RoundTrip.withBlocks(exprents, from, exprents.size(), indent, closeAtEnd));
      return;
    }
    List<Exprent> head = RoundTrip.leadingExprents(stat);
    buf.append(RoundTrip.withBlocks(head, from, head.size(), indent, closeAtEnd));
    RoundTrip.consumeHead(stat);
    buf.append(ExprProcessor.jmpWrapper(stat, indent, true));
  }

  /** Prints what a split statement's head still owes after exprent {@code after}. */
  private static void printAfter(Statement stat, int after, int indent, TextBuffer buf) {
    List<Exprent> exprents = stat.getExprents();
    boolean closeAtEnd = exprents != null && printsOwnEnd(stat);
    if (exprents != null) {
      buf.append(RoundTrip.withBlocks(exprents, after + 1, exprents.size(), indent, closeAtEnd));
      return;
    }
    List<Exprent> head = RoundTrip.leadingExprents(stat);
    buf.append(RoundTrip.withBlocks(head, after + 1, head.size(), indent, closeAtEnd));
    RoundTrip.consumeHead(stat);
    buf.append(ExprProcessor.jmpWrapper(stat, indent, true));
  }

  /**
   * The two statements the target wrote as a small counting loop and a break guard, folded into
   * one loop by the shared test: {@code while (A && B) { x++; } if (A) break; body}. The tree has
   * the test's negation as the inner loop's condition with the body inside it, the break as a
   * leading guard whose arm is the loop's exit, and the increment as the outer body's tail. The
   * class file proves the order: the increment's instructions, then the guard's test, then the
   * body's, and the guard's test is the merged condition's first atom.
   */
  private boolean printFoldedIncrementLoop(TextBuffer buf, int indent) {
    if (stats.size() != 2 || !varDefinitions.isEmpty()) {
      return false;
    }
    if (!(getParent() instanceof DoStatement outer) || outer.getLooptype() != DoStatement.Type.INFINITE) {
      return false;
    }
    if (!(stats.get(0) instanceof DoStatement inner) || inner.getLooptype() != DoStatement.Type.WHILE
        || inner.isLabeled() || !inner.getVarDefinitions().isEmpty()
        || !(inner.getFirst() instanceof SequenceStatement body) || !body.getVarDefinitions().isEmpty()
        || body.getStats().size() < 2) {
      return false;
    }
    if (!(body.getStats().get(0) instanceof IfStatement guard) || guard.getElsestat() != null
        || guard.getIfstat() == null || guard.getHeadexprent() == null) {
      return false;
    }
    IfExprent guardHead = guard.getHeadexprent();
    Exprent condition = inner.getConditionExprent();
    if (!(condition instanceof FunctionExprent merged)
        || merged.getFuncType() != FunctionExprent.FunctionType.BOOLEAN_OR
        || merged.getLstOperands().size() != 2) {
      return false;
    }
    Exprent atom = merged.getLstOperands().get(0);
    Exprent test = guardHead.getCondition();
    // The guard re-tests the value the loop's own test computed, so the two are different
    // instructions with the same source expression; the printed form is what proves they agree.
    if (!test.toString().equals(atom.toString())) {
      return false;
    }
    List<Exprent> exitExprents = guard.getIfstat().getExprents();
    if (exitExprents == null || exitExprents.size() != 1
        || !(exitExprents.get(0) instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() == null) {
      return false;
    }
    List<Exprent> increments = stats.get(1).getExprents();
    if (increments == null || increments.size() != 1
        || !(increments.get(0) instanceof FunctionExprent increment) || !increment.getFuncType().isPPMM()) {
      return false;
    }
    int incrementStart = RoundTrip.firstOffset(stats.get(1));
    // The guard's arm holds the loop's exit, far past the body; the test's own branch is the
    // offset that proves the guard sits between the increment and the body.
    int guardStart = test.bytecode == null ? -1 : test.bytecode.nextSetBit(0);
    int restStart = RoundTrip.firstOffset(body.getStats().get(1));
    if (incrementStart < 0 || guardStart < 0 || restStart < 0
        || incrementStart >= guardStart || guardStart >= restStart) {
      return false;
    }
    buf.appendIndent(indent).append("while (")
      .append(RoundTrip.negateCondition(condition).toJava(indent)).append(") {").appendLineSeparator();
    buf.append(ExprProcessor.listToJava(increments, indent + 1));
    buf.appendIndent(indent).append("}").appendLineSeparator();
    buf.appendIndent(indent).append("if (").append(test.toJava(indent)).append(") {").appendLineSeparator();
    buf.appendIndent(indent + 1).append("break;").appendLineSeparator();
    buf.appendIndent(indent).append("}").appendLineSeparator();
    for (int i = 1; i < body.getStats().size(); i++) {
      buf.append(ExprProcessor.jmpWrapper(body.getStats().get(i), indent, true));
    }
    // The guard's arm is the loop's exit; the source wrote it as the `return …;` after the loop.
    RoundTrip.deferIncrementLoopExit(guard.getIfstat());
    return true;
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

  /** The target's slot for the first local this statement declares, or -1. */
  private static int firstDeclaredSlot(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents == null) {
      return -1;
    }
    int start = -1;
    int slot = -1;
    for (Exprent exprent : exprents) {
      for (Exprent part : exprent.getAllExprents(true, true)) {
        if (part instanceof VarExprent variable && variable.isDefinition() && variable.getLVT() != null) {
          int declared = variable.getLVT().getStartPC();
          if (start < 0 || declared < start) {
            start = declared;
            slot = variable.getLVT().getIndex();
          }
        }
      }
    }
    return slot;
  }

  /**
   * Prints `if (!C) { return; } B` back as the source's `if (C) { B-leading } else { return; }
   * B-rest` when B's leading exprents are laid out before the return's own instruction. A guard
   * clause reaches its following statements only after the return, so code before that
   * instruction was the then arm, as javac lays out a finally block's unlock.
   */
  private boolean printInvertedGuard(TextBuffer buf, int indent, int i) {
    if (i + 1 >= stats.size() || !(stats.get(i) instanceof IfStatement ifs)
        || ifs.iftype != IfStatement.IFTYPE_IF || ifs.getElsestat() != null
        || ifs.isLabeled() || ifs.isPatternMatched() || ifs.getIfstat() == null
        || ifs.getHeadexprent() == null
        || !(ifs.getHeadexprent().getCondition() instanceof FunctionExprent not)
        || not.getFuncType() != FunctionExprent.FunctionType.BOOL_NOT
        || not.getLstOperands().size() != 1) {
      return false;
    }
    Statement block = stats.get(i + 1);
    if (!(block instanceof BasicBlockStatement) || block.isLabeled()
        || !block.getVarDefinitions().isEmpty() || !block.getStats().isEmpty()
        || block.getExprents() == null || block.getExprents().size() < 2) {
      return false;
    }
    List<Exprent> armExprents = ifs.getIfstat().getExprents();
    if (armExprents == null || armExprents.size() != 1
        || !(armExprents.get(0) instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() != null) {
      return false;
    }
    int exitOffset = RoundTrip.exprentStart(exit);
    List<Exprent> exprents = block.getExprents();
    int split = 0;
    while (split < exprents.size()) {
      int start = RoundTrip.exprentStart(exprents.get(split));
      if (start < 0 || start >= exitOffset) {
        break;
      }
      if (definesLocal(exprents.get(split)) || RoundTrip.printedEnd(exprents.get(split)) > exitOffset) {
        // A declaration would leave its scope with the brace, and code straddling the return
        // cannot move to either side.
        return false;
      }
      split++;
    }
    if (split == 0) {
      return false;
    }
    IfExprent head = (IfExprent) ifs.getHeadexprent().copy();
    head.setCondition(not.getLstOperands().get(0));
    buf.append(ExprProcessor.listToJava(ifs.getVarDefinitions(), indent));
    buf.append(ifs.getFirst().toJava(indent));
    buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
    buf.append(ExprProcessor.listToJava(exprents.subList(0, split), indent + 1));
    buf.appendIndent(indent).append("} else {").appendLineSeparator();
    buf.append(ExprProcessor.jmpWrapper(ifs.getIfstat(), indent + 1, true));
    buf.appendIndent(indent).append("}").appendLineSeparator();
    buf.append(ExprProcessor.listToJava(exprents.subList(split, exprents.size()), indent));
    return true;
  }

  /** Whether this exprent declares a local, which cannot move into a brace. */
  private static boolean definesLocal(Exprent exprent) {
    if (exprent instanceof VarExprent var && var.isDefinition()) {
      return true;
    }
    return exprent instanceof AssignmentExprent assignment
      && assignment.getLeft() instanceof VarExprent left && left.isDefinition();
  }

  /**
   * The end offset an arm really has: the last exprent's instruction, plus the void return the
   * writer folded into the method's exit when the target records one right after it. The dropped
   * return is part of the arm, and a jump to the join lands past it.
   */
  private static int endWithDroppedReturn(Statement stat, int end) {
    if (end < 0 || RoundTrip.printsVoidReturn(stat)) {
      return end;
    }
    return RoundTrip.voidReturnEndingAt(end + 1) == end ? end + 1 : end;
  }

  /**
   * Whether the arm leaves by a break to the join: a chain of guards that each break out of a
   * shared block, or a loop arm that breaks out of the loop, which other rules already print.
   */
  private static boolean breaksOut(Statement arm, int join) {
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    queue.add(arm);
    while (!queue.isEmpty()) {
      Statement stat = queue.poll();
      for (StatEdge edge : stat.getAllDirectSuccessorEdges()) {
        Statement destination = edge.getDestination();
        if (edge.getType() == StatEdge.TYPE_BREAK && destination != null
            && !arm.containsStatementStrict(destination) && destination != arm
            && !(destination instanceof DummyExitStatement)
            && RoundTrip.firstOffset(destination) >= join) {
          return true;
        }
      }
      queue.addAll(stat.getStats());
    }
    return false;
  }

  /**
   * Whether any edge out of this arm lands inside that byte range: an arm that falls into the
   * code after it never skipped it, so the code is not an else arm.
   */
  private static boolean fallsInto(Statement arm, int from, int to) {
    for (StatEdge edge : arm.getAllDirectSuccessorEdges()) {
      Statement destination = edge.getDestination();
      if (destination == null || arm.containsStatementStrict(destination)) {
        continue;
      }
      int start = RoundTrip.firstOffset(destination);
      if (start >= from && start < to) {
        return true;
      }
    }
    return false;
  }

  /** Whether the first if's pattern variable is still in scope where the second if tests. */
  private static boolean aliveAt(IfStatement first, IfStatement second) {
    var method = RoundTrip.currentMethod();
    int slot = patternSlot(first);
    int at = RoundTrip.firstOffset(second);
    if (method == null || slot < 0 || at < 0) {
      return false;
    }
    org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute table =
      method.getAttribute(org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    return table.getVariables().anyMatch(entry -> entry.getIndex() == slot
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

  /** The target's slot for the instanceof pattern variable this if declares, or -1. */
  private static int patternSlot(IfStatement stat) {
    VarExprent variable = patternVar(stat);
    if (variable == null) {
      return -1;
    }
    // A pattern the tree rebuilt from a cast store carries a decompiler-assigned index; the
    // target's local table names the slot javac actually used.
    if (variable.getLVT() != null) {
      return variable.getLVT().getIndex();
    }
    return variable.getIndex();
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

  /** True when a local the tail declares is read by the statement printed after the guard. */
  private static boolean tailLocalsUsedAfter(Statement tail, Statement after) {
    for (Exprent exprent : allExprents(tail)) {
      if (exprent instanceof VarExprent variable && variable.isDefinition()
          && readsVariable(after, variable.getIndex(), variable.getVersion())) {
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

  /**
   * True when this arm leaves the site at its end: a return or throw, or a break or continue edge
   * on its last statement. The decompiler marks the break it synthesized itself as implicit, so the
   * edge's flags are not part of the test.
   */
  private static boolean armLeaves(Statement stat) {
    if (exits(stat)) {
      return true;
    }
    Statement last = stat;
    while (true) {
      List<Statement> children = last.getStats();
      if (children == null || children.isEmpty()) {
        break;
      }
      last = children.get(children.size() - 1);
    }
    for (StatEdge edge : last.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL)) {
      if (edge.getType() == StatEdge.TYPE_BREAK || edge.getType() == StatEdge.TYPE_CONTINUE) {
        return true;
      }
    }
    return false;
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

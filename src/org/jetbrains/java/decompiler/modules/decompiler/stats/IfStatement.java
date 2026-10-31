// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.match.IMatchable;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.struct.match.MatchNode;
import org.jetbrains.java.decompiler.util.StartEndPair;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.TextUtil;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;


public class IfStatement extends Statement {

  public static final int IFTYPE_IF = 0;
  public static final int IFTYPE_IFELSE = 1;

  public int iftype;

  // *****************************************************************************
  // private fields
  // *****************************************************************************

  private Statement ifstat;
  private Statement elsestat;

  private StatEdge ifedge;
  private StatEdge elseedge;

  private boolean negated = false;
  private boolean patternMatched = false;

  private final List<Exprent> headexprent = new ArrayList<>(1); // contains IfExprent

  /**
   * The arm statements an enclosing print is putting behind `} else ` right now. A statement in
   * this set has its own braces as the only ones around it, so a rewrite that must stay inside an
   * else may print it as the chain's else; a sibling the enclosing print hoists after its brace
   * is not in the set and keeps the hoisted reading.
   */
  private static final ThreadLocal<java.util.Set<Statement>> ELSE_IF_ARM =
    ThreadLocal.withInitial(() -> java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>()));

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected IfStatement() {
    super(StatementType.IF);

    headexprent.add(null);
  }

  protected IfStatement(Statement head, int regedges, Statement postst) {

    this();

    first = head;
    stats.addWithKey(head, head.id);

    List<StatEdge> lstHeadSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);

    switch (regedges) {
      case 0:
        ifstat = null;
        elsestat = null;

        break;
      case 1:
        ifstat = null;
        elsestat = null;

        StatEdge edgeif = lstHeadSuccs.get(1);
        if (edgeif.getType() != StatEdge.TYPE_REGULAR) {
          post = lstHeadSuccs.get(0).getDestination();
        }
        else {
          post = edgeif.getDestination();
          negated = true;
        }
        break;
      case 2:
        elsestat = lstHeadSuccs.get(0).getDestination();
        ifstat = lstHeadSuccs.get(1).getDestination();

        List<StatEdge> lstSucc = ifstat.getSuccessorEdges(StatEdge.TYPE_REGULAR);
        List<StatEdge> lstSucc1 = elsestat.getSuccessorEdges(StatEdge.TYPE_REGULAR);

        if (ifstat.getPredecessorEdges(StatEdge.TYPE_REGULAR).size() > 1 || lstSucc.size() > 1) {
          post = ifstat;
        }
        else if (elsestat.getPredecessorEdges(StatEdge.TYPE_REGULAR).size() > 1 || lstSucc1.size() > 1) {
          post = elsestat;
        }
        else {
          if (lstSucc.size() == 0) {
            post = elsestat;
          }
          else if (lstSucc1.size() == 0) {
            post = ifstat;
          }
        }

        if (ifstat == post) {
          if (elsestat != post) {
            ifstat = elsestat;
            negated = true;
          }
          else {
            ifstat = null;
          }
          elsestat = null;
        }
        else if (elsestat == post) {
          elsestat = null;
        }
        else {
          post = postst;
        }

        if (elsestat == null) {
          regedges = 1;  // if without else
        }
    }

    ifedge = lstHeadSuccs.get(negated ? 0 : 1);
    elseedge = (regedges == 2) ? lstHeadSuccs.get(negated ? 1 : 0) : null;

    iftype = (regedges == 2) ? IFTYPE_IFELSE : IFTYPE_IF;

    if (iftype == IFTYPE_IF) {
      if (regedges == 0) {
        StatEdge edge = lstHeadSuccs.get(0);
        head.removeSuccessor(edge);
        edge.setSource(this);
        this.addSuccessor(edge);
      }
      else if (regedges == 1) {
        StatEdge edge = lstHeadSuccs.get(negated ? 1 : 0);
        head.removeSuccessor(edge);
      }
    }

    if (ifstat != null) {
      stats.addWithKey(ifstat, ifstat.id);
    }

    if (elsestat != null) {
      stats.addWithKey(elsestat, elsestat.id);
    }

    if (post == head) {
      post = this;
    }
  }


  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {

    if (head instanceof BasicBlockStatement && head.getLastBasicType() == LastBasicType.IF) {
      int regsize = head.getSuccessorEdges(StatEdge.TYPE_REGULAR).size();

      Statement p = null;

      boolean ok = (regsize < 2);
      if (!ok) {
        List<Statement> lst = new ArrayList<>();
        if (DecHelper.isChoiceStatement(head, lst)) {
          p = lst.remove(0);

          for (Statement st : lst) {
            if (st.isMonitorEnter()) {
              return null;
            }
          }

          ok = DecHelper.checkStatementExceptions(lst);
        }
      }

      if (ok) {
        return new IfStatement(head, regsize, p);
      }
    }

    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    // A merged head block stays where the arm printed it; only the test and arms moved.
    if (!RoundTrip.isHeadConsumed(this)) {
      buf.append(first.toJava(indent));
    }

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    Exprent condition = headexprent.get(0);
    // NEUROFLOWER_GUARD_DEBUG=<method name> dumps every if head's guard evidence: the selector
    // exists because a refused guard leaves no trace in the output, only a flattened mirror.
    if (System.getenv("NEUROFLOWER_GUARD_DEBUG") != null && RoundTrip.currentMethod() != null
        && System.getenv("NEUROFLOWER_GUARD_DEBUG").equals(RoundTrip.currentMethod().getName())) {
      Exprent dbgCond = condition instanceof IfExprent h ? h.getCondition() : null;
      IfExprent dbgHead = condition instanceof IfExprent h ? h : null;
      System.err.println("guardshape ifstat=" + (ifstat != null) + " else=" + (elsestat != null)
        + " patternMatched=" + isPatternMatched() + " labeled=" + isLabeled()
        + " declaresPattern=" + (dbgCond != null && declaresPattern(dbgCond))
        + " endsLoopBody=" + RoundTrip.endsLoopBody(this)
        + " headLen=" + (dbgHead == null || dbgHead.bytecode == null ? -1 : dbgHead.bytecode.length())
        + " headCard=" + (dbgHead == null || dbgHead.bytecode == null ? -1 : dbgHead.bytecode.cardinality())
        + " condLen=" + (dbgCond == null || dbgCond.bytecode == null ? -1 : dbgCond.bytecode.length())
        + " condCard=" + (dbgCond == null || dbgCond.bytecode == null ? -1 : dbgCond.bytecode.cardinality())
        + " cond=" + (dbgCond == null ? "null" : dbgCond.toJava(0).toString().replace('\n', ' '))
        + " continueGuard=" + (dbgHead != null && RoundTrip.printContinueGuard(dbgHead, this))
        + (ifstat == null ? "" : " thenFirst=" + RoundTrip.firstOffset(ifstat) + " thenLast=" + RoundTrip.lastEnd(ifstat))
        + (elsestat == null ? "" : " elseFirst=" + RoundTrip.firstOffset(elsestat) + " elseLast=" + RoundTrip.lastEnd(elsestat)));
    }
    // An empty arm prints as `if (C) { ; } else { body }`; when the target returns between the
    // condition and the body, the source wrote the guard `if (C) { return; } body`.
    Statement guardBody;
    if (elsestat == null) {
      guardBody = ifstat;
    } else if (RoundTrip.printsNothing(ifstat)) {
      guardBody = elsestat;
    } else if (RoundTrip.printsNothing(elsestat)) {
      guardBody = ifstat;
    } else {
      guardBody = null;
    }
    Exprent guardCondition = guardBody != null && condition instanceof IfExprent ifHead
      ? RoundTrip.guardCondition(ifHead, guardBody) : null;
    if (guardCondition != null) {
      IfExprent guard = (IfExprent) ((IfExprent) condition).copy();
      guard.setCondition(guardCondition);
      buf.appendIndent(indent);
      buf.append(guard.toJava(indent)).append(" {").appendLineSeparator();
      buf.appendIndent(indent + 1).append("return;").appendLineSeparator();
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(guardBody, indent, false));
      return buf;
    }

    // `if (!(x instanceof T t)) <abrupt arm>` followed by the body: the target's branch lands on
    // the abrupt arm and the pattern bind in front of it ends in a goto to the body, where a real
    // `if (!(x instanceof T t)) { arm } else { body }` branches to the else with the bind at its
    // start and no such goto. The bind belongs to the test, so the guard prints with the tree's
    // negated condition and the body follows the braces as the source's next statements.
    if (ifstat != null && elsestat != null && !isLabeled()
        && condition instanceof IfExprent ifHead
        && RoundTrip.guardArmFirst(ifHead, ifstat, elsestat)) {
      buf.appendIndent(indent).append(ifHead.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(elsestat, indent, false));
      return buf;
    }

    // `if (G1) continue; if (G2) continue; …` merged into one test whose body is the loop's own
    // end: every guard but a redundant last one leaves a branch-then-goto pair behind, and the
    // condition the merge built to shortcut through them splits back apart at those points. The
    // merge reads each written test as the condition for reaching the next statement, so the
    // groups print negated; where the head's own branch is the continue instead, the condition
    // already is the guards and every group prints as written. The same shape occurs with
    // `break;` guards, whose jump leaves the enclosing loop or switch instead of returning to its
    // head; the edge tells which keyword the guard printed.
    if (ifstat == null && elsestat == null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && !declaresPattern(ifHead.getCondition())
        && ifedge != null
        && (ifedge.getType() == StatEdge.TYPE_CONTINUE || ifedge.getType() == StatEdge.TYPE_BREAK)
        // An explicit jump edge carries the continue or break; a labeled one is `continue outer;`
        // and does not print here.
        && (!ifedge.explicit || !ifedge.labeled)
        && printMergedGuards(buf, ifHead, indent)) {
      return buf;
    }

    // `if (!C) break;` at the end of a loop body: the tree kept the branch condition as
    // `if (C) continue;` with the loop's exit as the fall-through edge. The target's first
    // condition branch lands on that exit, where a written continue would send it back to the
    // loop's head, so the source wrote the negated test with the break inside it. The edge's
    // break is what the printed body carries; the wrapper must not print it again.
    if (ifstat == null && elsestat == null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && ifedge != null && ifedge.getType() == StatEdge.TYPE_CONTINUE && ifedge.explicit && !ifedge.labeled
        && printBreakGuardByTarget(buf, ifHead, indent)) {
      RoundTrip.markBreakPrinted(this);
      return buf;
    }

    // `if (C) continue; body`: the loop printed the mirror `if (!C) { body }` as its body.
    // The target's branch-then-goto shape and line table prove the continue; the printed
    // condition may be any expression, and its negation is what the source wrote.
    if (ifstat != null && elsestat == null && condition instanceof IfExprent ifHead
        && (getParent() instanceof DoStatement
            // The same mirror one level in: `if (!C) { rest }` printed as the loop body's tail.
            // A pattern if's head can also span a nested condition of its own, and then its guard
            // belongs to that inner test; a condition that declares a pattern variable is accepted
            // only when its own bytes end flush with the head's, so the head is exactly this test.
            // Otherwise the head's length is a fallback: a condition the decompiler built itself
            // carries no offsets, and refusing those would lose every compound guard. A test that
            // is a boolean call or field access is simplified to the call itself, which drops the
            // comparison wrapper along with the branch offsets, so its bytes end flush against a
            // lone branch: the branch then consumes exactly the value the condition computes and
            // the printed condition is the whole test.
            // The same holds for the else arm of an if that ends the loop body: the arm is the
            // loop's tail too once its sibling hoisted the arm out of the block (Raid keeps
            // `if (tickCount <= 600) continue;` as the else arm of the raider guard).
            || RoundTrip.endsLoopBody(this)
               && ifHead.bytecode != null
               && (declaresPattern(ifHead.getCondition())
                   ? ifHead.getCondition().bytecode != null
                      && ifHead.getCondition().bytecode.length() == ifHead.bytecode.length()
                   : ifHead.getCondition().bytecode == null
                      || ifHead.getCondition().bytecode.length() == ifHead.bytecode.length()
                      || loneBranch(ifHead)
                         && !ifHead.getCondition().bytecode.isEmpty()
                         && ifHead.getCondition().bytecode.length() == ifHead.bytecode.nextSetBit(0)))
        && RoundTrip.printContinueGuard(ifHead, this)) {
      Exprent printed = ifHead.getCondition();
      Exprent source = printed instanceof FunctionExprent not
          && not.getFuncType() == FunctionType.BOOL_NOT
          && not.getLstOperands().size() == 1
        ? not.getLstOperands().get(0)
        : RoundTrip.negateCondition(printed);
      // Two guards merged into one `||`: the target records a goto back to the loop head for each
      // operand, so the source wrote one `if (C) continue;` per test.
      List<Exprent> ors = orOperands(source);
      List<List<Exprent>> groups = RoundTrip.guardGroups(ifHead, ors, this);
      if (groups == null) {
        groups = java.util.Collections.singletonList(java.util.Collections.singletonList(source));
      }
      // A single guard compiles the printed `continue;` to the goto the target's table puts on the
      // line the source wrote it on; the line alignment has to see that jump to place it.
      int gotoOffset = groups.size() == 1 ? RoundTrip.continueGoto(ifHead) : -1;
      for (List<Exprent> group : groups) {
        IfExprent guard = (IfExprent) ifHead.copy();
        guard.setCondition(orOf(group));
        buf.appendIndent(indent);
        buf.append(guard.toJava(indent)).append(" {").appendLineSeparator();
        TextBuffer continueLine = new TextBuffer();
        continueLine.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        if (gotoOffset >= 0) {
          continueLine.addStartBytecodeMapping(gotoOffset);
        }
        buf.append(continueLine);
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
      return buf;
    }

    // The same mirror inside a try-with-resources that ends the loop body: the target's branch
    // skips the synthetic close() and the goto after it, so the branch-then-goto pair the path
    // above needs is broken. The close's normal exit is where the source's continue compiled to;
    // the guard and the body print inside the try, so the close still runs on the guard's path.
    if (ifstat != null && elsestat == null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && ifHead.bytecode != null
        && (declaresPattern(ifHead.getCondition())
            ? ifHead.getCondition().bytecode != null
               && ifHead.getCondition().bytecode.length() == ifHead.bytecode.length()
            : ifHead.getCondition().bytecode == null
               || ifHead.getCondition().bytecode.length() == ifHead.bytecode.length()
               || loneBranch(ifHead)
                  && !ifHead.getCondition().bytecode.isEmpty()
                  && ifHead.getCondition().bytecode.length() == ifHead.bytecode.nextSetBit(0))
        && RoundTrip.printContinueThroughClose(ifHead, this)) {
      Exprent printed = ifHead.getCondition();
      Exprent source = printed instanceof FunctionExprent not
          && not.getFuncType() == FunctionType.BOOL_NOT
          && not.getLstOperands().size() == 1
        ? not.getLstOperands().get(0)
        : RoundTrip.negateCondition(printed);
      List<Exprent> ors = orOperands(source);
      List<List<Exprent>> groups = RoundTrip.guardGroups(ifHead, ors, this);
      if (groups == null) {
        // A run of guards whose continues each run through the close: the target records every
        // branch as an else guard, and the next statement starts at the branch's target.
        groups = RoundTrip.closeGuardGroups(ifHead, ors, this);
      }
      if (groups == null) {
        groups = java.util.Collections.singletonList(java.util.Collections.singletonList(source));
      }
      for (int groupIndex = 0; groupIndex < groups.size(); groupIndex++) {
        List<Exprent> group = groups.get(groupIndex);
        IfExprent guard = (IfExprent) ifHead.copy();
        guard.setCondition(orOf(group));
        buf.appendIndent(indent);
        buf.append(guard.toJava(indent)).append(" {").appendLineSeparator();
        TextBuffer continueLine = new TextBuffer();
        continueLine.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        // Each guard compiles its `continue;` to the jump the target records for it: the next
        // group's site for an earlier guard, the head's own last branch for the last group.
        int gotoOffset = groupIndex + 1 < groups.size()
          ? RoundTrip.continueCloseSiteBefore(groups.get(groupIndex + 1).get(0), this)
          : RoundTrip.continueCloseSite();
        if (gotoOffset >= 0) {
          continueLine.addStartBytecodeMapping(gotoOffset);
        }
        buf.append(continueLine);
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
      return buf;
    }

    // `if (!C) break; arm` where the tree kept the break as the if's trailing edge and the arm as
    // its then branch: javac branches into the arm and falls through to a jump to the break, which
    // only the written guard lays out that way. The plain `if (C) { arm } break;` branches past the
    // arm to the break instead, so the target's branch target and the jump right after it prove
    // which form the source had. The arm leaves on its own, so printing it after the brace keeps
    // the flow; the break it reaches is the guard the source wrote, printed inside the test.
    java.util.List<StatEdge> breakSuccs = getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    boolean breakEdge = breakSuccs.size() == 1 && breakSuccs.get(0).getType() == StatEdge.TYPE_BREAK
        && breakSuccs.get(0).explicit && !breakSuccs.get(0).labeled;
    if (ifstat != null && elsestat == null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && breakEdge
        && endsWithExit(ifstat) && !RoundTrip.declaresBlockLocal(ifstat)
        && RoundTrip.breakGuardEntersArm(ifHead, ifstat, breakSuccs.get(0).getDestination())) {
      Exprent printed = ifHead.getCondition();
      Exprent source = printed instanceof FunctionExprent not
          && not.getFuncType() == FunctionType.BOOL_NOT
          && not.getLstOperands().size() == 1
        ? not.getLstOperands().get(0)
        : RoundTrip.negateCondition(printed);
      IfExprent guard = (IfExprent) ifHead.copy();
      guard.setCondition(source);
      buf.appendIndent(indent).append(guard.toJava(indent)).append(" {").appendLineSeparator();
      buf.appendIndent(indent + 1).append("break;").appendLineSeparator();
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
      RoundTrip.markBreakPrinted(this);
      return buf;
    }

    // `if (!C) { } else <arm>`: the target jumps into the arm on C being true and falls through
    // to a jump out of it — the empty then block's exit, which a written `if (C) { <arm> }` does
    // not have. The tree dropped the empty arm and kept the source's else as the then, so the
    // test prints negated with the arm after the brace, as the chain's first clause when it is
    // itself an if.
    if (ifstat != null && elsestat == null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && RoundTrip.emptyThenArm(ifHead, ifstat)) {
      // The jump after the branch lands on the loop's head: the empty arm the source wrote was a
      // `continue;` and the tree's arm is the statement after it, not an else. The arm keeps the
      // block its own table rows close with, or prints in the open when they run on.
      if (RoundTrip.printContinueGuardAtHead(ifHead, this)) {
        IfExprent head = (IfExprent) ifHead.copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        TextBuffer continueLine = new TextBuffer();
        continueLine.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        int gotoOffset = RoundTrip.continueGoto(ifHead);
        if (gotoOffset >= 0) {
          continueLine.addStartBytecodeMapping(gotoOffset);
        }
        buf.append(continueLine);
        buf.appendIndent(indent).append("}").appendLineSeparator();
        boolean braces = RoundTrip.closesAtOwnEnd(ifstat);
        if (braces) {
          buf.appendIndent(indent).append("{").appendLineSeparator();
        }
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent + (braces ? 1 : 0), false));
        if (braces) {
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
        return buf;
      }
      // The jump after the branch lands on a break's destination instead of past the arm: the
      // empty arm the source wrote held the break, and the tree's arm is its else. Printing the
      // plain empty then arm would drop the jump and fall through to the join.
      java.util.List<StatEdge> emptyExits = getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
      if (emptyExits.size() == 1 && emptyExits.get(0).getType() == StatEdge.TYPE_BREAK
          && emptyExits.get(0).explicit && !emptyExits.get(0).labeled
          && RoundTrip.breakGuardEntersArm(ifHead, ifstat, emptyExits.get(0).getDestination())) {
        Exprent printed = ifHead.getCondition();
        Exprent source = printed instanceof FunctionExprent not
            && not.getFuncType() == FunctionType.BOOL_NOT
            && not.getLstOperands().size() == 1
          ? not.getLstOperands().get(0)
          : RoundTrip.negateCondition(printed);
        IfExprent guard = (IfExprent) ifHead.copy();
        guard.setCondition(source);
        buf.appendIndent(indent).append(guard.toJava(indent)).append(" {").appendLineSeparator();
        buf.appendIndent(indent + 1).append("break;").appendLineSeparator();
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        RoundTrip.markBreakPrinted(this);
        return buf;
      }
      IfExprent head = (IfExprent) ifHead.copy();
      head.setCondition(RoundTrip.negateCondition(head.getCondition()));
      buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
      if (!printElseIfArm(buf, indent, ifstat)) {
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
      return buf;
    }

    // The same source shape with the rest of the body as the else arm: `if (C) { ...; continue; }
    // rest`. The arm's terminal goto to the loop head proves the continue; the arm always exits,
    // so the rest runs exactly where the else arm did. Hoisting is exact only when the if ends the
    // loop body: the arm's scope then ends where the else block's did, so a local it declares
    // cannot move, and nothing after the if could depend on the branch.
    if (ifstat != null && elsestat != null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && !RoundTrip.printsNothing(elsestat)
        && !RoundTrip.declaresLocalToEnd(ifstat)
        // An if/else whose last branch lands on the arm the tree prints as then has its arms the
        // wrong way round: the jump between the arms is the join, not a continue the source wrote
        // (TripWireHookBlock's tripwire test). Let the swap below print it as the if/else it is.
        && !RoundTrip.swapIfArmsByLastTarget(ifHead, ifstat)
        && endsLoopBody(this)
        && RoundTrip.printContinueElse(ifHead, this, ifstat)) {
      buf.appendIndent(indent).append(ifHead.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
      appendContinueLine(buf, indent);
      if (printedAsElseIfArm()) {
        // The enclosing if prints this statement as its `else if`, whose only braces are this
        // statement's own: the rest hoisted after them would leave the enclosing else and join
        // the flow the enclosing test branches past. Keep it as the chain's else — javac compiles
        // both readings alike, and the else stays inside the enclosing arm.
        if (!printElseIfArm(buf, indent, elsestat)) {
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(elsestat, indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
        }
      } else {
        buf.appendIndent(indent).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(elsestat, indent, false));
      }
      return buf;
    }

    // The same shape with the arms the other way round: the tree's else arm is the one the
    // target prints as the then (its last branch lands on ifstat), so the arm to hoist is
    // elsestat. The continue is that arm's terminal jump to the loop head; the rest of the body
    // is ifstat and runs after the braces exactly as it did in the else.
    if (ifstat != null && elsestat != null && !isLabeled() && !isPatternMatched()
        && condition instanceof IfExprent ifHead
        && !RoundTrip.printsNothing(elsestat)
        && !RoundTrip.declaresLocalToEnd(elsestat)
        && RoundTrip.swapIfArmsByLastTarget(ifHead, ifstat)
        && endsLoopBody(this)
        && RoundTrip.printContinueElse(ifHead, this, elsestat)) {
      IfExprent source = (IfExprent) ifHead.copy();
      source.setCondition(RoundTrip.negateCondition(source.getCondition()));
      buf.appendIndent(indent).append(source.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(elsestat, indent + 1, true));
      appendContinueLine(buf, indent);
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
      return buf;
    }

    // `if (C) A else B` and `if (!C) B else A` are the same program in different bytes; the target's
    // branch opcode, the arms' lines, or the last condition branch says which one was written. A
    // last branch that lands on the arm the tree prints as then contradicts the test printed there
    // whenever the condition is a disjunction, so the arms come back the other way round; an else-if
    // chain takes the same repair, its nested if being just this test's else arm.
    if (ifstat != null && elsestat != null
        && condition instanceof IfExprent ifHead
        && ((!isLabeled() && !isPatternMatched() && !declaresPattern(ifHead.getCondition())
              && RoundTrip.swapIfArmsByLastTarget(ifHead, ifstat))
            || RoundTrip.swapIfArms(ifHead)
            || (RoundTrip.swapIfArmsByLine(ifstat, elsestat)
                && !RoundTrip.polaritySelfConsistent(ifHead, ifstat, elsestat))
            // The target skipped a pattern arm with a goto and branched to it on the negated test:
            // the source wrote `if (!(x instanceof T t)) { arm } else { rest }`, and the tree's
            // positive test with the arms the other way round is the same program in other bytes.
            || RoundTrip.negatedPatternGuard(ifHead, ifstat, elsestat) >= 0)) {
      IfExprent head = (IfExprent) ifHead.copy();
      head.setCondition(RoundTrip.negateCondition(head.getCondition()));
      // The arm the swap prints second was declared in the method body, so the source closed
      // the branch before it and wrote the other arm as a guard.
      boolean targetReturn = targetVoidReturn(elsestat, ifstat);
      boolean guard = (endsWithExit(elsestat) || targetReturn)
        && RoundTrip.startsWithMethodScopeLocal(ifstat);
      buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(elsestat, indent + 1, true));
      appendArmContinue(buf, elsestat, ifstat, indent + 1);
      appendVoidArmReturn(buf, elsestat, ifstat, indent + 1);
      if (guard) {
        buf.appendIndent(indent).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
      } else if (appendFlatElse(buf, indent, elsestat, ifstat, false)) {
        // The table proves the source wrote the second arm flat after the first.
      } else if (!printElseIfArm(buf, indent, ifstat)) {
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
      return buf;
    }

    // A guard whose else was declared in the method body: the table writes the else's first
    // local after the parameters, so the original source closed the branch before it. The slots
    // can still prove the opposite — an else-if's binding hoisted into the if's prefix reads like
    // a method-scope local's row, but its slot precedes the one it would have reused.
    if (ifstat != null && elsestat != null
        && condition != null && !isLabeled()
        && (endsWithExit(ifstat) || targetVoidReturn(ifstat, elsestat))
        && RoundTrip.startsWithMethodScopeLocal(elsestat)
        && !RoundTrip.elseChainSlots(this, elsestat)) {
      buf.appendIndent(indent).append(condition.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
      appendVoidArmReturn(buf, ifstat, elsestat, indent + 1);
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(elsestat, indent, false));
      return buf;
    }

    // `if (a) { if (b) { body } }` is folded into `if (a && b) { body }`: the same instructions,
    // but javac marks a nested if statement's start and never marks the start of a boolean
    // operand that only inherits the expression's line. When the target's table has an entry at
    // an operand's first instruction, on a line later than the one before it ends, the source
    // wrote the statements nested; print that run of ifs back.
    if (ifstat != null && !isLabeled() && condition instanceof IfExprent ifHead
        && printSplitIf(buf, ifHead, ifstat, elsestat, indent, false)) {
      return buf;
    }

    buf.appendIndent(indent);
    // Condition can be null in early processing stages
    if (condition != null) {
      buf.append(condition.toJava(indent));
    } else {
      buf.append("if <null condition>");
    }
    buf.append(" {").appendLineSeparator();

    if (ifstat == null) {
      boolean semicolon = false;
      if (ifedge.explicit && !RoundTrip.isClosureHidden(ifedge)) {
        semicolon = true;
        // A labelled continue whose jump lands on an enclosing loop's own end through another
        // goto is the source's `break label;` of that loop.
        Statement trampolineBreak = ifedge.getType() == StatEdge.TYPE_CONTINUE
          ? RoundTrip.trampolineBreakLoop(ifedge, this, RoundTrip.droppedJumpOffset(this)) : null;
        if (trampolineBreak != null && !RoundTrip.printsLabel(trampolineBreak)) {
          trampolineBreak = null;
        }
        if (trampolineBreak != null) {
          buf.appendIndent(indent + 1).append("break label").append(trampolineBreak.id);
        } else {
          if (ifedge.getType() == StatEdge.TYPE_BREAK) {
            // A break and a continue compile alike where the break's target is the loop's back
            // edge; the goto the head carries says whether the source's jump went to the loop's
            // head, where only a written `continue` lands.
            boolean continues = !ifedge.labeled && condition instanceof IfExprent ifHead
              && RoundTrip.printContinueGuardAtHead(ifHead, this);
            buf.appendIndent(indent + 1).append(continues ? "continue" : "break");
          }
          else {
            // continue
            buf.appendIndent(indent + 1).append("continue");
          }

          if (ifedge.labeled) {
            buf.append(" label").append(ifedge.closure == null ? "<unknownclosure>" : Integer.toString(ifedge.closure.id));
          }
        }
      }
      if(semicolon) {
        buf.append(";").appendLineSeparator();
      }
    }
    else {
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
      appendArmContinue(buf, ifstat, elsestat, indent + 1);
      appendVoidArmReturn(buf, ifstat, elsestat, indent + 1);
    }

    appendElse(buf, indent);

    return buf;
  }

  /**
   * Prints the then arm's closing brace and the else arm flat after the if when the target's table
   * proves the source wrote the arm flat: the arm's first local closes with the enclosing block,
   * and every row that opened before the arm was written after it. A real else closes its own
   * block first and writes the arm's rows ahead of every enclosing row. The then arm has to leave
   * on its own, or the source's flat form would run into the statements after the test; a continue
   * the arm's print folded into its edge is written here, and a plain break is left as an else
   * because the arm's print may owe it to an enclosing switch, where a written break is illegal.
   * False, printing nothing, when the else stays.
   *
   * @param printJump whether the caller has not already printed the then arm's terminal jump
   */
  private boolean appendFlatElse(TextBuffer buf, int indent, Statement thenArm, Statement elseArm, boolean printJump) {
    if (!RoundTrip.selector("elseflat") || RoundTrip.isArmOpen(this)
        || elseArm instanceof IfStatement
        || !RoundTrip.armWasFlat(elseArm)) {
      return false;
    }
    boolean armExits = endsWithExit(thenArm) || endsWithYield(thenArm);
    StatEdge exitEdge = armExits ? null : SequenceStatement.terminalExit(thenArm);
    boolean continues = exitEdge != null
      && (exitEdge.getType() == StatEdge.TYPE_CONTINUE
          || exitEdge.getType() == StatEdge.TYPE_BREAK && exitEdge.getDestination() instanceof DoStatement);
    if (!armExits && !continues) {
      return false;
    }
    if (continues && printJump) {
      buf.appendIndent(indent + 1).append("continue;").appendLineSeparator();
    }
    buf.appendIndent(indent).append("}").appendLineSeparator();
    buf.append(ExprProcessor.jmpWrapper(elseArm, indent, false));
    return true;
  }

  /**
   * True when the target ends the arm with a void return the writer dropped: its last instruction
   * is a return exactly where the other arm begins, and the arm's print does not already carry
   * one. The source closed the branch there, so the other arm prints after the if, not as an else.
   */
  private static boolean targetVoidReturn(Statement arm, Statement next) {
    if (arm == null || next == null || endsWithVoidReturn(arm)) {
      return false;
    }
    return RoundTrip.voidReturnEndingAt(RoundTrip.firstOffset(next)) >= 0;
  }

  /**
   * Prints the void return the source ended this arm with, when the target's last instruction
   * before the other arm is one: the arm then falls through to the code printed after the if, so
   * the return is not redundant in the source and the writer, which folded it into the method's
   * end, dropped it. Pinned to its instruction so the line alignment keeps the line.
   */
  private static void appendVoidArmReturn(TextBuffer buf, Statement arm, Statement next, int indent) {
    if (arm == null || next == null || endsWithVoidReturn(arm)) {
      return;
    }
    int exit = RoundTrip.voidReturnEndingAt(RoundTrip.firstOffset(next));
    if (exit < 0) {
      return;
    }
    TextBuffer line = new TextBuffer();
    line.appendIndent(indent).append("return;").appendLineSeparator();
    RoundTrip.mapSynthesizedLine(line, exit);
    buf.append(line);
  }

  /** True when the arm's last exprent is a {@code yield}, which leaves its switch expression. */
  private static boolean endsWithYield(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (int i = exprents.size() - 1; i >= 0; i--) {
        if (exprents.get(i) != null) {
          return exprents.get(i).type == Exprent.Type.YIELD;
        }
      }
      return false;
    }
    List<Statement> children = stat.getStats();
    return !children.isEmpty() && endsWithYield(children.get(children.size() - 1));
  }

  /** True when the statement's print already ends with a bare `return;`. */
  private static boolean endsWithVoidReturn(Statement stat) {
    if (stat == null) {
      return false;
    }
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (int i = exprents.size() - 1; i >= 0; i--) {
        if (exprents.get(i) != null) {
          return exprents.get(i) instanceof ExitExprent exit
            && exit.getExitType() == ExitExprent.Type.RETURN && exit.getValue() == null;
        }
      }
      return false;
    }
    if (!stat.getStats().isEmpty()) {
      return endsWithVoidReturn(stat.getStats().get(stat.getStats().size() - 1));
    }
    return false;
  }

  /**
   * Prints the continue the source ended this arm with when the target keeps a goto from the
   * arm's end to the loop head while the else arm follows it: the jump skips the else, so the
   * arm cannot reach the loop by falling through, and the tree folded the written continue into
   * the loop's own edge.
   */
  private static void appendArmContinue(TextBuffer buf, Statement arm, Statement elseArm, int indent) {
    int site = RoundTrip.armContinueSite(arm, elseArm);
    if (site < 0) {
      return;
    }
    TextBuffer line = new TextBuffer();
    line.appendIndent(indent).append("continue;").appendLineSeparator();
    line.addStartBytecodeMapping(site);
    buf.append(line);
  }

  /** Prints the continue that ends a hoisted arm, pinned to the jump the target records. */
  private static void appendContinueLine(TextBuffer buf, int indent) {
    TextBuffer line = new TextBuffer();
    line.appendIndent(indent + 1).append("continue;").appendLineSeparator();
    int site = RoundTrip.continueElseSite();
    if (site >= 0) {
      line.addStartBytecodeMapping(site);
    }
    buf.append(line);
  }

  /** Prints the closing brace of the then arm and the else arm, if any, at this indent. */
  private void appendElse(TextBuffer buf, int indent) {
    boolean elseif = false;

    if (elsestat != null) {
      if (appendFlatElse(buf, indent, ifstat, elsestat, true)) {
        return;
      }
      // The target's table can prove the else arm closed early: a local the arm declares has a
      // row ending at the first instruction of a trailing return or throw, so the source's brace
      // stood there and the return ran after the if/else. The flat print would keep the local
      // alive through the return instead.
      int split = RoundTrip.isArmOpen(this) ? -1 : RoundTrip.armScopeSplit(elsestat);
      if (split > 0) {
        List<Statement> children = elsestat.getStats();
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        for (int k = 0; k < split; k++) {
          buf.append(ExprProcessor.jmpWrapper(children.get(k), indent + 1, k == 0));
        }
        buf.appendIndent(indent).append("}").appendLineSeparator();
        for (int k = split; k < children.size(); k++) {
          buf.append(ExprProcessor.jmpWrapper(children.get(k), indent, k == split));
        }
        // The brace this arm ends with was printed above, before the trailing statements.
        return;
      }
      if (printElseIfArm(buf, indent, elsestat, this)) {
        elseif = true;
      }
      else {
        TextBuffer content = ExprProcessor.jmpWrapper(elsestat, indent + 1, false);

        if (content.length() > 0) {
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(content);
        }
      }
    }

    if (!elseif) {
      // A chain prints this arm's closing brace together with the next `else` on one line, the
      // way the source wrote it.
      if (RoundTrip.isArmOpen(this)) {
        RoundTrip.armClosed();
      }
      else {
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
    }
  }

  /**
   * Prints `if (!C) break;` when the target proves that a continue-shaped if was really the
   * source's break guard: the guard is the statement's only exit and the condition's first test
   * lands on the loop's exit. False, printing nothing, otherwise.
   */
  private boolean printBreakGuardByTarget(TextBuffer buf, IfExprent ifHead, int indent) {
    java.util.List<StatEdge> successors = getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (successors.size() != 1 || successors.get(0).getType() != StatEdge.TYPE_BREAK
        || !successors.get(0).explicit || successors.get(0).labeled) {
      return false;
    }
    if (!RoundTrip.breakGuardByTarget(ifHead, this)) {
      return false;
    }
    Exprent printed = ifHead.getCondition();
    Exprent source = printed instanceof FunctionExprent not
        && not.getFuncType() == FunctionType.BOOL_NOT && not.getLstOperands().size() == 1
      ? not.getLstOperands().get(0)
      : RoundTrip.negateCondition(printed);
    IfExprent guard = (IfExprent) ifHead.copy();
    guard.setCondition(source);
    buf.appendIndent(indent).append(guard.toJava(indent)).append(" {").appendLineSeparator();
    buf.appendIndent(indent + 1).append("break;").appendLineSeparator();
    buf.appendIndent(indent).append("}").appendLineSeparator();
    return true;
  }

  /** Prints an `else if` arm's content, recording that the arm is being printed as one. */
  private static TextBuffer printElseIfArmContent(Statement arm, int indent) {
    ELSE_IF_ARM.get().add(arm);
    try {
      return ExprProcessor.jmpWrapper(arm, indent, false);
    } finally {
      ELSE_IF_ARM.get().remove(arm);
    }
  }

  /**
   * True when the enclosing if prints this statement as its `else if` arm: the arm's own braces
   * are the only ones around its text, so anything this statement prints after them leaves the
   * enclosing else and joins the flow the enclosing test branches past.
   */
  private boolean printedAsElseIfArm() {
    return ELSE_IF_ARM.get().contains(this);
  }

  /**
   * The same, for an else arm printed by its owner: a sequence that opens with a plain if is the
   * source's chain when the target's slots prove it ({@link RoundTrip#elseChainSlots}), and its
   * remaining statements are the chain's final else.
   */
  static boolean printElseIfArm(TextBuffer buf, int indent, Statement arm, IfStatement owner) {
    if (printElseIfArm(buf, indent, arm)) {
      return true;
    }
    if (owner == null || !RoundTrip.selector("elseifchain")
        || !(arm instanceof SequenceStatement sequence)
        || !sequence.varDefinitions.isEmpty() || sequence.getStats().size() < 2) {
      return false;
    }
    Statement lead = sequence.getStats().get(0);
    if (!(lead instanceof IfStatement elseIf) || elseIf.iftype != IFTYPE_IF
        || elseIf.getElsestat() != null || elseIf.getIfstat() == null
        || elseIf.isLabeled() || !elseIf.varDefinitions.isEmpty()
        || elseIf.getHeadexprent() == null || elseIf.getHeadexprent().getCondition() == null
        // A clause has to open with its own `if`: a head block with exprents prints statements
        // ahead of the test, which cannot follow an `else` keyword.
        || elseIf.getFirst() == null || elseIf.getFirst().getExprents() == null
        || !elseIf.getFirst().getExprents().isEmpty()) {
      return false;
    }
    // The chain's own slots: the else binding is hoisted above the shared subject temp, where a
    // written `else { if … }` declares it behind the inner test's own temp. Only a pattern test
    // has that evidence.
    if (!RoundTrip.patternChainArm(owner, sequence)) {
      return false;
    }
    // The else keyword can only take the rest of the block when the arm leaves on its own: a path
    // from the then into the rest would run those statements on both branches.
    if (reachesAny(elseIf.getIfstat(), sequence.getStats(), 1)) {
      return false;
    }
    Statement previous = RoundTrip.openArm(elseIf);
    TextBuffer content;
    boolean open;
    try {
      content = printElseIfArmContent(elseIf, indent);
    } finally {
      open = RoundTrip.closeArm(previous);
    }
    buf.appendIndent(indent).append("} else ");
    content.setStart(TextUtil.getIndentString(indent).length());
    buf.append(content);
    // The arm withheld its closing brace for this line: `} else {` closes the inner if.
    buf.appendIndent(indent).append(open ? "} else {" : "else {").appendLineSeparator();
    List<Statement> rest = sequence.getStats();
    for (int i = 1; i < rest.size(); i++) {
      buf.append(ExprProcessor.jmpWrapper(rest.get(i), indent + 1, i == 1));
    }
    buf.appendIndent(indent).append("}").appendLineSeparator();
    return true;
  }

  /**
   * Whether any statement of this subtree jumps to one of the statements at or after {@code from}
   * in the list: such a path falls into the code the caller prints behind the next brace.
   */
  private static boolean reachesAny(Statement stat, List<Statement> stats, int from) {
    if (stat == null) {
      return false;
    }
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      Statement destination = edge.getDestination();
      for (int i = from; i < stats.size(); i++) {
        if (stats.get(i) == destination) {
          return true;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (reachesAny(child, stats, from)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Prints `} else ` and the nested if when the arm still qualifies as an else-if chain, leaving
   * the closing brace to the caller; false, printing nothing, otherwise.
   */
  static boolean printElseIfArm(TextBuffer buf, int indent, Statement arm) {
    if (arm instanceof SequenceStatement sequence && RoundTrip.selector("elseifchain")
        && sequence.printsAsChainArm()) {
      buf.appendIndent(indent).append("} else ");
      TextBuffer content = printElseIfArmContent(arm, indent);
      content.setStart(TextUtil.getIndentString(indent).length());
      buf.append(content);
      return true;
    }
    if (arm instanceof IfStatement
        && arm.varDefinitions.isEmpty() && (arm.getFirst().getExprents() != null && arm.getFirst().getExprents().isEmpty()) &&
        !arm.isLabeled() &&
        (arm.getSuccessorEdges(STATEDGE_DIRECT_ALL).isEmpty()
         || !arm.getSuccessorEdges(STATEDGE_DIRECT_ALL).get(0).explicit)) { // else if
      buf.appendIndent(indent).append("} else ");

      TextBuffer content = printElseIfArmContent(arm, indent);
      content.setStart(TextUtil.getIndentString(indent).length());
      buf.append(content);
      return true;
    }
    return false;
  }

  /**
   * Whether this statement is the last thing every enclosing statement up to the loop runs, so a
   * guard printed at its end skips nothing the loop still needs and hoisting an arm into it keeps
   * every scope's end where it was.
   */
  private static boolean endsLoopBody(Statement stat) {
    for (Statement parent = stat.getParent(); parent != null; parent = stat.getParent()) {
      if (parent instanceof DoStatement) {
        return true;
      }
      if (parent instanceof SequenceStatement sequence) {
        if (sequence.getStats().getLast() != stat) {
          return false;
        }
      } else if (parent instanceof IfStatement ifStatement) {
        // The else arm is the loop's last work when the enclosing if ends the loop body: the
        // sibling's guard hoists the arm out of the block and everything in it then runs last.
        if (ifStatement.getIfstat() != stat
            && !(ifStatement.getElsestat() == stat && RoundTrip.endsLoopBody(ifStatement))) {
          return false;
        }
      } else {
        return false;
      }
      stat = parent;
    }
    return false;
  }

  /**
   * Where a `&&` condition splits back into nested ifs, as operand indices, or an empty list.
   * A pattern variable declared by a later operand lives to the end of the same statement in the
   * flat form; nesting puts its declaration inside a block, and javac then numbers local slots
   * differently, so those stay flat — unless the target proves the operand began a statement of
   * its own: a continue guard's goto ends exactly where it starts, which no boolean operand of a
   * shared condition can have.
   */
  static List<Integer> nestedIfGroups(IfExprent head, Statement arm) {
    List<Exprent> operands = booleanOperands(head.getCondition());
    if (operands.size() < 2) {
      return java.util.Collections.emptyList();
    }
    List<Integer> groups = new ArrayList<>();
    groups.add(0);
    for (int i = 1; i < operands.size(); i++) {
      // A pattern operand the table records after the earlier operands' last binding in the same
      // scope and pass was written in the same condition: a nested source writes the inner
      // block's binding first. Keep it in the condition whatever the line marks say.
      if (RoundTrip.patternBindingFollows(andOf(operands, 0, i), operands.get(i))) {
        continue;
      }
      int afterStart = RoundTrip.exprentStart(operands.get(i));
      int afterEnd = i + 1 < operands.size() ? RoundTrip.exprentStart(operands.get(i + 1))
        : head.bytecode == null ? -1 : head.bytecode.length();
      // A nested test's false exit is chained past the inner test to the final destination beyond
      // the arm, so the branch before the operand lands farther than the operand's own; one `&&`
      // chain sends both to the same target.
      boolean chained = RoundTrip.chainedIfTests(head, afterStart, afterEnd);
      boolean starts = chained || RoundTrip.operandStartsStatement(andOf(operands, 0, i), operands.get(i));
      if (declaresPattern(operands.get(i))
          && !chained
          && (!starts
              || !RoundTrip.continuesBefore(operands.get(i), arm)
                 && !RoundTrip.patternSlotReused(operands.get(i)))) {
        // A pattern variable the flat condition declares stays where it is: nesting a later
        // operand would move its declaration into a block of its own, and javac then numbers the
        // slots differently. The later boundaries still split — a pattern variable in the prefix
        // is in scope for the rest of the source's condition either way.
        continue;
      }
      if (starts) {
        groups.add(i);
      }
    }
    return groups.size() > 1 ? groups : java.util.Collections.emptyList();
  }

  /**
   * Prints the condition split back into the nested ifs the target's table proves, the guarded
   * arm inside them, and the flat form's else arm after the outermost brace. An else arm only
   * moves out when the guarded arm always exits: the flat form jumps over the else, so an arm
   * that can fall through would otherwise run it. An else that declares a local stays inside
   * braces as well, since a statement outside them would keep the local alive longer. False,
   * printing nothing, when nothing splits.
   */
  static boolean printSplitIf(TextBuffer buf, IfExprent head, Statement arm, Statement elseArm,
                              int indent, boolean elseSemicolon) {
    List<Integer> groups = nestedIfGroups(head, arm);
    if (groups.isEmpty()
        || (elseArm != null && (!endsWithExit(arm) || RoundTrip.declaresLocal(elseArm)))) {
      return false;
    }
    if (printNestedIfs(buf, head, arm, groups, indent, elseArm == null)) {
      buf.appendIndent(indent).append("}").appendLineSeparator();
    }
    if (elseArm != null) {
      buf.append(ExprProcessor.jmpWrapper(elseArm, indent, elseSemicolon));
    }
    return true;
  }

  /**
   * Prints one `if` header per group and the arm the innermost guards, leaving the outermost brace
   * open: the caller closes it, and appends the else arm when there is one. A group the target
   * compiled as {@code if (C) continue;} prints as a closed guard and the groups after it return to
   * the guard's own level; a run of written guards prints as a run of closed tests. When the first
   * group is a guard no brace is left open.
   */
  static boolean printNestedIfs(TextBuffer buf, IfExprent head, Statement arm, List<Integer> groups, int indent,
                                boolean allowContinueGuard) {
    List<Exprent> operands = booleanOperands(head.getCondition());
    boolean guards = allowContinueGuard && RoundTrip.endsLoopBody(arm);
    int open = 0;
    boolean firstGuard = false;
    for (int group = 0; group < groups.size(); group++) {
      int to = group + 1 < groups.size() ? groups.get(group + 1) : operands.size();
      Exprent printed = andOf(operands, groups.get(group), to);
      // A run of written `if (C) continue;` statements: each guard's jump ends where the next
      // group's own test begins (the last one's at the head's end), so every group can be one.
      boolean guard = guards && (group + 1 < groups.size()
        ? RoundTrip.continuesBefore(operands.get(groups.get(group + 1)), arm)
        : RoundTrip.printContinueGuard(head, arm));
      IfExprent nested = (IfExprent) head.copy();
      if (guard) {
        nested.setCondition(printed instanceof FunctionExprent not
            && not.getFuncType() == FunctionType.BOOL_NOT
            && not.getLstOperands().size() == 1
          ? not.getLstOperands().get(0)
          : RoundTrip.negateCondition(printed));
        buf.appendIndent(indent + open).append(nested.toJava(indent + open))
          .append(" {").appendLineSeparator();
        buf.appendIndent(indent + open + 1).append("continue;").appendLineSeparator();
        buf.appendIndent(indent + open).append("}").appendLineSeparator();
        if (group == 0) {
          firstGuard = true;
        }
      } else {
        nested.setCondition(printed);
        buf.appendIndent(indent + open).append(nested.toJava(indent + open))
          .append(" {").appendLineSeparator();
        open++;
      }
    }
    buf.append(ExprProcessor.jmpWrapper(arm, indent + open, true));
    // The caller closes the outermost brace (and prints the else arm after it) unless the first
    // group was a guard: then every test here is closed and the arm already returned to its level.
    for (int level = open - 1; level >= (firstGuard ? 0 : 1); level--) {
      buf.appendIndent(indent + level).append("}").appendLineSeparator();
    }
    return !firstGuard;
  }

  /**
   * Prints a condition that folded a run of `if (G) continue;` statements back as one guard per
   * group; the loop's own end follows the last group, so nothing is printed after them. False,
   * printing nothing, when the condition does not split.
   */
  private boolean printMergedGuards(TextBuffer buf, IfExprent head, int indent) {
    boolean breaks = ifedge.getType() == StatEdge.TYPE_BREAK;
    // A break guard is a separate shape from the continue's; the selector keeps it switchable.
    if (breaks && !RoundTrip.selector("breakguard")) {
      return false;
    }
    // A break guard's jump is a statement of its own behind a test of its own; an edge that keeps
    // no jump is not that shape, and the complement path below is the continue's own.
    if (breaks && !ifedge.explicit) {
      return false;
    }
    // The head's edge to the continue decides which way the merge read the written tests: a jump
    // is the continue itself, so each test prints as written; a fall-through is the continue, so
    // the merge kept the test for reaching the next statement and each group needs its complement.
    boolean written = ifedge.explicit;
    List<Exprent> operands = written ? orOperands(head.getCondition()) : booleanOperands(head.getCondition());
    RoundTrip.GuardSplit split = RoundTrip.mergedGuards(head, operands, this, breaks);
    if (split == null) {
      // A run of guards whose continues each run through a try-with-resources close: the target
      // records every branch as an else guard at the close's goto, and the next statement begins
      // at the branch's target. Split the run there and print one guard per group.
      List<List<Exprent>> closeGroups = written && !breaks
        ? RoundTrip.closeGuardGroups(head, operands, this) : null;
      if (closeGroups == null) {
        return false;
      }
      for (int i = 0; i < closeGroups.size(); i++) {
        IfExprent guard = (IfExprent) head.copy();
        guard.setCondition(orOf(closeGroups.get(i)));
        buf.appendIndent(indent);
        buf.append(guard.toJava(indent)).append(" {").appendLineSeparator();
        TextBuffer continueLine = new TextBuffer();
        continueLine.appendIndent(indent + 1).append("continue;").appendLineSeparator();
        int site = i + 1 < closeGroups.size()
          ? RoundTrip.continueCloseSiteBefore(closeGroups.get(i + 1).get(0), this)
          : RoundTrip.continueCloseSiteForHead(head);
        if (site >= 0) {
          continueLine.addStartBytecodeMapping(site);
        }
        buf.append(continueLine);
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
      return true;
    }
    // With the continue as the fall-through the head's branch is the last guard's whole test, so a
    // head group that branch does not send to the loop would print a guard the target lacks.
    if (!written && !RoundTrip.headBranchContinues(head, this)) {
      return false;
    }
    String keyword = breaks ? "break;" : "continue;";
    // The merge folded each written guard as the test for reaching the next statement, so a group
    // it closed prints its complement; the head's own test was never folded and keeps its polarity.
    for (int i = 0; i < split.groups.size(); i++) {
      List<Exprent> group = split.groups.get(i);
      Exprent test = written ? orOf(group) : andOf(group, 0, group.size());
      IfExprent guard = (IfExprent) head.copy();
      guard.setCondition(written || i == split.headGroup ? test : complement(test));
      buf.appendIndent(indent);
      buf.append(guard.toJava(indent)).append(" {").appendLineSeparator();
      buf.appendIndent(indent + 1).append(keyword).appendLineSeparator();
      buf.appendIndent(indent).append("}").appendLineSeparator();
    }
    return true;
  }

  /**
   * The complement of a printed test as the source wrote it: a `!` the merge left is dropped and
   * anything else is wrapped in one. The wrapper stays literal on purpose — De Morgan would print
   * an equivalent test whose jumps javac lays out differently.
   */
  private static Exprent complement(Exprent exprent) {
    if (exprent instanceof FunctionExprent not && not.getFuncType() == FunctionType.BOOL_NOT
        && not.getLstOperands().size() == 1) {
      return not.getLstOperands().get(0);
    }
    return new FunctionExprent(FunctionType.BOOL_NOT, exprent, null);
  }

  /** One operand, or the operands joined by `||` again, as a guard condition prints it. */
  static Exprent orOf(List<Exprent> operands) {
    if (operands.size() == 1) {
      return operands.get(0);
    }
    Exprent left = orOf(operands.subList(0, operands.size() - 1));
    List<Exprent> pair = new ArrayList<>(2);
    pair.add(left);
    pair.add(operands.get(operands.size() - 1));
    return new FunctionExprent(FunctionType.BOOLEAN_OR, pair, null);
  }

  /** The operands of a boolean-or condition, flattened; a single expression comes back alone. */
  static List<Exprent> orOperands(Exprent condition) {
    List<Exprent> operands = new ArrayList<>();
    collectOrOperands(condition, operands);
    return operands;
  }

  private static void collectOrOperands(Exprent condition, List<Exprent> out) {
    if (condition instanceof FunctionExprent function
        && function.getFuncType() == FunctionType.BOOLEAN_OR
        && function.getLstOperands().size() >= 2) {
      for (Exprent operand : function.getLstOperands()) {
        collectOrOperands(operand, out);
      }
    } else {
      out.add(condition);
    }
  }

  /** The operands of a boolean-and condition in the order the source wrote them. */
  private static List<Exprent> booleanOperands(Exprent condition) {
    List<Exprent> operands = new ArrayList<>();
    collectOperands(condition, operands);
    return operands;
  }

  private static void collectOperands(Exprent condition, List<Exprent> out) {
    if (condition instanceof FunctionExprent function
        && function.getFuncType() == FunctionType.BOOLEAN_AND
        && function.getLstOperands().size() >= 2) {
      // The fold nests to the right (the bytecode's three branches to one target), so every
      // side has to be flattened or a nested test stays hidden inside a later operand. A
      // merge may also fold into a single n-ary node.
      for (Exprent operand : function.getLstOperands()) {
        collectOperands(operand, out);
      }
    } else {
      out.add(condition);
    }
  }

  /** Whether the expression declares a pattern variable of its own. */
  private static boolean declaresPattern(Exprent exprent) {
    for (Exprent part : exprent.getAllExprents(true, true)) {
      if (part instanceof FunctionExprent function
          && function.getFuncType() == FunctionType.INSTANCEOF
          && function.getLstOperands().size() > 2) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the head's bytes are exactly the three bytes of one branch instruction. A head that
   * merged a nested if carries that if's branch as well, and then its condition is not this
   * branch's test alone.
   */
  private static boolean loneBranch(IfExprent head) {
    BitSet bits = head.bytecode;
    return bits.cardinality() == 3 && bits.nextSetBit(0) + 3 == bits.length();
  }

  /** One operand, or the operands joined by `&&` again, as an if condition prints it. */
  private static Exprent andOf(List<Exprent> operands, int from, int to) {
    if (to - from == 1) {
      return operands.get(from);
    }
    List<Exprent> pair = new ArrayList<>(2);
    pair.add(andOf(operands, from, to - 1));
    pair.add(operands.get(to - 1));
    return new FunctionExprent(FunctionType.BOOLEAN_AND, pair, null);
  }

  private static boolean endsWithExit(Statement stat) {
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
    return !children.isEmpty() && endsWithExit(children.get(children.size() - 1));
  }

  @Override
  public void initExprents() {
    IfExprent ifexpr = (IfExprent)first.getExprents().remove(first.getExprents().size() - 1);

    if (negated) {
      ifexpr = (IfExprent)ifexpr.copy();
      ifexpr.negateIf();
    }

    headexprent.set(0, ifexpr);
  }

  @Override
  public List<Exprent> getStatExprents() {
    return new ArrayList<>(headexprent);
  }

  @Override
  public void replaceExprent(Exprent oldexpr, Exprent newexpr) {
    if (headexprent.get(0) == oldexpr) {
      headexprent.set(0, newexpr);
    }
  }

  @Override
  public void replaceStatement(Statement oldstat, Statement newstat) {
    super.replaceStatement(oldstat, newstat);

    if (ifstat == oldstat) {
      ifstat = newstat;
    }

    if (elsestat == oldstat) {
      elsestat = newstat;
    }

    List<StatEdge> lstSuccs = first.getSuccessorEdges(STATEDGE_DIRECT_ALL);

    if (iftype == IFTYPE_IF) {
      ifedge = lstSuccs.get(0);
      elseedge = null;
    }
    else {
      StatEdge edge0 = lstSuccs.get(0);
      StatEdge edge1 = lstSuccs.get(1);
      if (edge0.getDestination() == ifstat) {
        ifedge = edge0;
        elseedge = edge1;
      }
      else {
        ifedge = edge1;
        elseedge = edge0;
      }
    }
  }

  @Override
  public boolean hasBasicSuccEdge() {
    return iftype == IFTYPE_IF;
  }

  @Override
  public Statement getSimpleCopy() {
    IfStatement is = new IfStatement();
    is.iftype = this.iftype;
    is.negated = this.negated;

    return is;
  }

  @Override
  public void initSimpleCopy() {
    first = stats.get(0);

    List<StatEdge> lstSuccs = first.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    ifedge = lstSuccs.get((iftype == IFTYPE_IF || negated) ? 0 : 1);
    if (stats.size() > 1) {
      ifstat = stats.get(1);
    }

    if (iftype == IFTYPE_IFELSE) {
      elseedge = lstSuccs.get(negated ? 1 : 0);
      elsestat = stats.get(2);
    }
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public Statement getElsestat() {
    return elsestat;
  }

  public void setElsestat(Statement elsestat) {
    this.elsestat = elsestat;
  }

  public Statement getIfstat() {
    return ifstat;
  }

  public void setIfstat(Statement ifstat) {
    this.ifstat = ifstat;
  }

  public boolean isNegated() {
    return negated;
  }

  public void setNegated(boolean negated) {
    this.negated = negated;
  }

  public List<Exprent> getHeadexprentList() {
    return headexprent;
  }

  public IfExprent getHeadexprent() {
    return (IfExprent)headexprent.get(0);
  }

  public void setElseEdge(StatEdge elseedge) {
    this.elseedge = elseedge;
  }

  public void setIfEdge(StatEdge ifedge) {
    this.ifedge = ifedge;
  }

  public StatEdge getIfEdge() {
    return ifedge;
  }

  public StatEdge getElseEdge() {
    return elseedge;
  }

  public boolean isPatternMatched() {
    return patternMatched;
  }

  public void setPatternMatched(boolean patternMatched) {
    this.patternMatched = patternMatched;
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>();

    List<Exprent> conditionList = getHeadexprent().getCondition().getAllExprents(true);
    conditionList.add(getHeadexprent().getCondition());

    for (Exprent condition : conditionList) {
      if (condition instanceof FunctionExprent func) {
        // Pattern match variable is implicitly defined
        if (func.getFuncType() == FunctionType.INSTANCEOF && func.getLstOperands().size() > 2) {
          vars.addAll(((Pattern) func.getLstOperands().get(2)).getPatternVars());
        }
      }
    }

    return vars;
  }

  @Override
  public StartEndPair getStartEndRange() {
    return StartEndPair.join(super.getStartEndRange(),
      ifstat != null ? ifstat.getStartEndRange() : null,
      elsestat != null ? elsestat.getStartEndRange(): null);
  }

  // *****************************************************************************
  // IMatchable implementation
  // *****************************************************************************

  @Override
  public IMatchable findObject(MatchNode matchNode, int index) {
    IMatchable object = super.findObject(matchNode, index);
    if (object != null) {
      return object;
    }

    if (matchNode.getType() == MatchNode.MATCHNODE_EXPRENT) {
      String position = (String)matchNode.getRuleValue(MatchProperties.EXPRENT_POSITION);
      if ("head".equals(position)) {
        return getHeadexprent();
      }
    }

    return null;
  }

  @Override
  public boolean match(MatchNode matchNode, MatchEngine engine) {
    if (!super.match(matchNode, engine)) {
      return false;
    }

    Integer type = (Integer) matchNode.getRuleValue(MatchProperties.STATEMENT_IFTYPE);
    return type == null || this.iftype == type;
  }

  public void fixIfInvariantEmptyElseBranch() {
    // if(){...}else{;} -> if(){...}

    Statement elseStat = this.getElsestat();

    if (this.iftype != IfStatement.IFTYPE_IFELSE ||
        elseStat.type != StatementType.BASIC_BLOCK ||
        elseStat.getExprents() == null ||
        !elseStat.getExprents().isEmpty()) {
      return;
    }

    // Degrade to an if statement
    this.getStats().removeWithKey(elseStat.id);

    this.iftype = IfStatement.IFTYPE_IF;
    this.setElsestat(null);

    // remove the if head -> elseStat edge
    this.getFirst().removeSuccessor(this.getElseEdge());

    this.setElseEdge(null);

    if (this.getAllSuccessorEdges().isEmpty()) {
      StatEdge nextEdge = elseStat.getFirstSuccessor();

      nextEdge.changeSource(this);
      // No need to check the type, if the if didn't have any successors, the edge can't be a break edge with this
      // as the closure
    } else {
      ValidationHelper.validateTrue(
        this.getFirstSuccessor().getDestination() == elseStat.getFirstSuccessor().getDestination(),
        "Expected the empty elseStat of the if statement to have the same destination as the if statement");
      // no need to change the edge, just deleting the outgoing edge from the ifstat is enough
      elseStat.getFirstSuccessor().remove();
    }
  }

  public void fixIfInvariantEmptyIfBranch() {
    // if(){;}else{...} -> if(!){...}

    Statement ifStat = this.getIfstat();

    if (this.iftype != IfStatement.IFTYPE_IFELSE ||
      ifStat == null || // should be a different fix
      ifStat.type != StatementType.BASIC_BLOCK ||
      ifStat.getExprents() == null ||
      !ifStat.getExprents().isEmpty()) {
      return;
    }

    // move else to the if position
    this.getStats().removeWithKey(ifStat.id);

    this.iftype = IfStatement.IFTYPE_IF;
    this.setIfstat(this.getElsestat());
    this.setElsestat(null);

    // remove the if head -> ifStat edge
    this.getFirst().removeSuccessor(this.getIfEdge());

    this.setIfEdge(this.getElseEdge());
    this.setElseEdge(null);

    if (this.getAllSuccessorEdges().isEmpty()) {
      // Make the ifStat -> next edge point from the if statement to the next statement
      StatEdge nextEdge = ifStat.getFirstSuccessor();
      nextEdge.changeSource(this);
      // No need to check the type, if the if didn't have any successors, the edge can't be a break edge with this
      // as the closure
    } else {
      ValidationHelper.validateTrue(
        this.getFirstSuccessor().getDestination() == ifStat.getFirstSuccessor().getDestination(),
        "Expected the empty ifStat of the if statement to have the same destination as the if statement");
      // no need to change the edge, just deleting the outgoing edge from the ifstat is enough
      ifStat.getFirstSuccessor().remove();
    }

    // negate head expression
    this.setNegated(!this.isNegated());
    this.getHeadexprentList().set(0, ((IfExprent) this.getHeadexprent().copy()).negateIf());
  }
}

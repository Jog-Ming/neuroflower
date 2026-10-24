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


      // `if (C) continue; body` in the source; the decompiler printed its mirror `if (!C) { body }`.
      // The target's branch-then-goto shape and line table prove the continue. The mirror is the
      // loop's whole remaining body, so the guard is exact only when this sequence is the loop
      // body and the if is its last statement; otherwise the continue would skip the tail.
      if (st instanceof IfStatement ifStatement
          && ifStatement.iftype == IfStatement.IFTYPE_IF && ifStatement.getElsestat() == null
          && !ifStatement.isPatternMatched() && !ifStatement.isLabeled() && !st.isLabeled()
          && ifStatement.getIfstat() != null
          && i == stats.size() - 1 && getParent() instanceof DoStatement
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
          && ifStatement.getIfstat() != null && endsWithReturn(ifStatement.getIfstat())
          && hasContent(stats.subList(i + 1, stats.size()))
          && !RoundTrip.declaresLocal(ifStatement.getIfstat())
          && stats.subList(i + 1, stats.size()).stream().noneMatch(RoundTrip::declaresLocal)
          && RoundTrip.branchesToBody(ifStatement.getHeadexprent(), ifStatement.getIfstat())) {
        IfExprent head = (IfExprent) ifStatement.getHeadexprent().copy();
        head.setCondition(RoundTrip.negateCondition(head.getCondition()));
        buf.append(ExprProcessor.listToJava(ifStatement.varDefinitions, indent));
        buf.append(ifStatement.getFirst().toJava(indent));
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(
          new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, true));
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
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
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
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
        buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifStatement.getIfstat(), indent + 1, true));
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(
          new SequenceStatement(stats.subList(i + 1, stats.size())), indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
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

  private static boolean endsWithReturn(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      if (exprents.isEmpty()) {
        return false;
      }
      Exprent last = exprents.get(exprents.size() - 1);
      return last instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN;
    }
    List<Statement> children = stat.getStats();
    return !children.isEmpty() && endsWithReturn(children.get(children.size() - 1));
  }

  @Override
  public Statement getSimpleCopy() {
    return new SequenceStatement();
  }
}

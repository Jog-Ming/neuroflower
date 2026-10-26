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

    buf.append(first.toJava(indent));

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    Exprent condition = headexprent.get(0);
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

    // `if (C) continue; body`: the loop printed the mirror `if (!C) { body }` as its body.
    // The target's branch-then-goto shape and line table prove the continue; the printed
    // condition may be any expression, and its negation is what the source wrote.
    if (ifstat != null && elsestat == null && condition instanceof IfExprent ifHead
        && getParent() instanceof DoStatement
        && RoundTrip.printContinueGuard(ifHead, this)) {
      Exprent printed = ifHead.getCondition();
      IfExprent guard = (IfExprent) ifHead.copy();
      guard.setCondition(printed instanceof FunctionExprent not
          && not.getFuncType() == FunctionType.BOOL_NOT
          && not.getLstOperands().size() == 1
        ? not.getLstOperands().get(0)
        : RoundTrip.negateCondition(printed));
      buf.appendIndent(indent);
      buf.append(guard.toJava(indent)).append(" {").appendLineSeparator();
      buf.appendIndent(indent + 1).append("continue;").appendLineSeparator();
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
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
        && endsLoopBody(this)
        && RoundTrip.printContinueElse(ifHead, this)) {
      buf.appendIndent(indent).append(ifHead.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
      buf.appendIndent(indent + 1).append("continue;").appendLineSeparator();
      buf.appendIndent(indent).append("}").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(elsestat, indent, false));
      return buf;
    }

    // `if (C) A else B` and `if (!C) B else A` are the same program in different bytes; the target's
    // branch opcode or the arm lines' order says which one was written.
    if (ifstat != null && elsestat != null && !(elsestat instanceof IfStatement)
        && condition instanceof IfExprent ifHead
        && (RoundTrip.swapIfArms(ifHead) || RoundTrip.swapIfArmsByLine(ifstat, elsestat))) {
      IfExprent head = (IfExprent) ifHead.copy();
      head.setCondition(RoundTrip.negateCondition(head.getCondition()));
      // The arm the swap prints second was declared in the method body, so the source closed
      // the branch before it and wrote the other arm as a guard.
      boolean guard = endsWithExit(elsestat) && RoundTrip.startsWithMethodScopeLocal(ifstat);
      buf.appendIndent(indent).append(head.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(elsestat, indent + 1, true));
      if (guard) {
        buf.appendIndent(indent).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent, false));
      } else {
        buf.appendIndent(indent).append("} else {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
      return buf;
    }

    // A guard whose else was declared in the method body: the table writes the else's first
    // local after the parameters, so the original source closed the branch before it.
    if (ifstat != null && elsestat != null
        && condition != null && !isLabeled() && endsWithExit(ifstat)
        && RoundTrip.startsWithMethodScopeLocal(elsestat)) {
      buf.appendIndent(indent).append(condition.toJava(indent)).append(" {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
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
      if (ifedge.explicit) {
        semicolon = true;
        if (ifedge.getType() == StatEdge.TYPE_BREAK) {
          // break
          buf.appendIndent(indent + 1).append("break");
        }
        else {
          // continue
          buf.appendIndent(indent + 1).append("continue");
        }

        if (ifedge.labeled) {
          buf.append(" label").append(ifedge.closure == null ? "<unknownclosure>" : Integer.toString(ifedge.closure.id));
        }
      }
      if(semicolon) {
        buf.append(";").appendLineSeparator();
      }
    }
    else {
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
    }

    appendElse(buf, indent);

    return buf;
  }

  /** Prints the closing brace of the then arm and the else arm, if any, at this indent. */
  private void appendElse(TextBuffer buf, int indent) {
    boolean elseif = false;

    if (elsestat != null) {
      if (elsestat instanceof IfStatement
          && elsestat.varDefinitions.isEmpty() && (elsestat.getFirst().getExprents() != null && elsestat.getFirst().getExprents().isEmpty()) &&
          !elsestat.isLabeled() &&
          (elsestat.getSuccessorEdges(STATEDGE_DIRECT_ALL).isEmpty()
           || !elsestat.getSuccessorEdges(STATEDGE_DIRECT_ALL).get(0).explicit)) { // else if
        buf.appendIndent(indent).append("} else ");

        TextBuffer content = ExprProcessor.jmpWrapper(elsestat, indent, false);
        content.setStart(TextUtil.getIndentString(indent).length());
        buf.append(content);

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
      buf.appendIndent(indent).append("}").appendLineSeparator();
    }
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
        if (ifStatement.getIfstat() != stat) {
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
   * differently. The flat compile is the only one the table proves, so those stay flat.
   */
  static List<Integer> nestedIfGroups(IfExprent head) {
    List<Exprent> operands = booleanOperands(head.getCondition());
    if (operands.size() < 2) {
      return java.util.Collections.emptyList();
    }
    for (int i = 1; i < operands.size(); i++) {
      if (declaresPattern(operands.get(i))) {
        return java.util.Collections.emptyList();
      }
    }
    List<Integer> groups = new ArrayList<>();
    groups.add(0);
    for (int i = 1; i < operands.size(); i++) {
      if (RoundTrip.operandStartsStatement(andOf(operands, 0, i), operands.get(i))) {
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
    List<Integer> groups = nestedIfGroups(head);
    if (groups.isEmpty()
        || (elseArm != null && (!endsWithExit(arm) || RoundTrip.declaresLocal(elseArm)))) {
      return false;
    }
    printNestedIfs(buf, head, arm, groups, indent, elseArm == null);
    buf.appendIndent(indent).append("}").appendLineSeparator();
    if (elseArm != null) {
      buf.append(ExprProcessor.jmpWrapper(elseArm, indent, elseSemicolon));
    }
    return true;
  }

  /**
   * Prints one `if` header per group and the arm the innermost guards, leaving the outermost brace
   * open: the caller closes it, and appends the else arm when there is one.
   */
  static void printNestedIfs(TextBuffer buf, IfExprent head, Statement arm, List<Integer> groups, int indent,
                             boolean allowContinueGuard) {
    List<Exprent> operands = booleanOperands(head.getCondition());
    // The innermost group is the target's guard when its last branch falls through to a jump back
    // to the loop head: the source wrote `if (C) continue;` there, not `if (!C) { arm }`.
    boolean guard = allowContinueGuard && !groups.isEmpty()
      && RoundTrip.endsLoopBody(arm) && RoundTrip.printContinueGuard(head, arm);
    for (int group = 0; group < groups.size(); group++) {
      int to = group + 1 < groups.size() ? groups.get(group + 1) : operands.size();
      IfExprent nested = (IfExprent) head.copy();
      nested.setCondition(andOf(operands, groups.get(group), to));
      if (guard && group == groups.size() - 1) {
        Exprent printed = nested.getCondition();
        nested.setCondition(printed instanceof FunctionExprent not
            && not.getFuncType() == FunctionType.BOOL_NOT
            && not.getLstOperands().size() == 1
          ? not.getLstOperands().get(0)
          : RoundTrip.negateCondition(printed));
        buf.appendIndent(indent + group).append(nested.toJava(indent + group))
          .append(" {").appendLineSeparator();
        buf.appendIndent(indent + group + 1).append("continue;").appendLineSeparator();
        buf.appendIndent(indent + group).append("}").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(arm, indent + group, true));
        for (int close = group - 1; close >= 1; close--) {
          buf.appendIndent(indent + close).append("}").appendLineSeparator();
        }
        return;
      }
      buf.appendIndent(indent + group).append(nested.toJava(indent + group))
        .append(" {").appendLineSeparator();
    }
    buf.append(ExprProcessor.jmpWrapper(arm, indent + groups.size(), true));
    for (int group = groups.size() - 1; group >= 1; group--) {
      buf.appendIndent(indent + group).append("}").appendLineSeparator();
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
        && function.getLstOperands().size() == 2) {
      // The fold nests to the right (the bytecode's three branches to one target), so both
      // sides have to be flattened or a nested test stays hidden inside the right operand.
      collectOperands(function.getLstOperands().get(0), out);
      collectOperands(function.getLstOperands().get(1), out);
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
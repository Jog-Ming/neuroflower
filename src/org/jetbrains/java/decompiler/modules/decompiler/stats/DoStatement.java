// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Pattern;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

// Loop statement
public class DoStatement extends Statement {
  public enum Type {
    INFINITE, DO_WHILE, WHILE, FOR, FOR_EACH
  }

  private Type looptype;

  private final List<Exprent> initExprent = new ArrayList<>();
  private final List<Exprent> conditionExprent = new ArrayList<>();
  private final List<Exprent> incExprent = new ArrayList<>();

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected DoStatement() {
    super(StatementType.DO);
    looptype = Type.INFINITE;

    initExprent.add(null);
    conditionExprent.add(null);
    incExprent.add(null);
  }

  protected DoStatement(Statement head) {

    this();

    first = head;
    stats.addWithKey(first, first.id);

    // post is always null!
  }

  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {

    if (head.getLastBasicType() == LastBasicType.GENERAL && !head.isMonitorEnter()) {

      // at most one outgoing edge
      StatEdge edge = null;
      List<StatEdge> lstSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
      if (!lstSuccs.isEmpty()) {
        edge = lstSuccs.get(0);
      }

      // regular loop
      if (edge != null && edge.getType() == StatEdge.TYPE_REGULAR && edge.getDestination() == head) {
        return new DoStatement(head);
      }

      // continues
      if (!(head instanceof DoStatement) && (edge == null || edge.getType() != StatEdge.TYPE_REGULAR) &&
          head.getContinueSet().contains(head.getBasichead())) {
        return new DoStatement(head);
      }
    }

    return null;
  }

  @Override
  public HashSet<Statement> buildContinueSet() {
    super.buildContinueSet();

    continueSet.remove(first.getBasichead());

    return continueSet;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    // When the guard prints its exit inside the loop, a local it reads that the tree declared
    // before the brace belongs at the assignment the source wrote in the body; the definition has
    // to move before the declarations print here.
    Statement guardReturn = null;
    if (looptype == Type.DO_WHILE && conditionExprent.get(0) != null
        && RoundTrip.loopGuardInsideBody(conditionExprent.get(0), first)) {
      Statement exitTarget = getAllSuccessorEdges().isEmpty()
        ? null : getAllSuccessorEdges().get(0).getDestination();
      guardReturn = RoundTrip.returnInsideLoop(this, exitTarget);
      if (guardReturn != null) {
        RoundTrip.moveDeclarationIntoBody(this, guardReturn, first);
      }
    }

    // A block the target laid out past the back edge is the loop's exit: the arms print the
    // break that reached it, and it prints again after the closing brace. Deciding it here lets a
    // local the block reads but the body only stores be declared above the loop first.
    List<Statement> deferredExits = null;
    if (looptype == Type.INFINITE) {
      deferredExits = RoundTrip.deferExitsAfter(this);
      RoundTrip.hoistDeferredDeclarations(this, deferredExits);
    }

    int varDefsStart = buf.length();
    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    if (isLabeled() || RoundTrip.carriesOutwardBreak(this) || RoundTrip.carriesBreakOut(this)
        || RoundTrip.carriesTrampolineBreak(this)) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    RoundTrip.enterAnyLoop(this);
    try {
      switch (looptype) {
      case INFINITE:
        // An exit copied out of this loop prints as the break the target jumped with.
        RoundTrip.enterLoop(this);
        try {
          List<Statement> deferred = deferredExits == null ? List.of() : deferredExits;
          if (printBreakGuard(buf, indent)) {
            RoundTrip.releaseDeferredExits(deferred);
            break;
          }
          buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          if (!deferred.isEmpty()) {
            RoundTrip.releaseDeferredExits(deferred);
            for (Statement exit : deferred) {
              // The block's own jump edge is the flow into the statement the loop's parent prints
              // next, so only its content moves here.
              buf.append(exit.toJava(indent));
            }
          }
          // A folded increment loop's break leaves for this same block; the body deferred it.
          Statement foldedExit = RoundTrip.takeIncrementLoopExit();
          if (foldedExit != null) {
            buf.append(ExprProcessor.jmpWrapper(foldedExit, indent, false));
          }
        } finally {
          RoundTrip.exitLoop();
        }
        break;
      case DO_WHILE:
        if (conditionExprent.get(0) != null && RoundTrip.loopGuardInsideBody(conditionExprent.get(0), first)) {
          // The source kept the test inside the body as a break guard.
          Exprent bodyHead = firstExprent(first);
          VarExprent moved = null;
          if (bodyHead instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assign
            && assign.getLeft() instanceof VarExprent left
            && !varDefinitions.isEmpty() && varDefinitions.get(varDefinitions.size() - 1) instanceof VarExprent decl
            && decl.getIndex() == left.getIndex()) {
            // The variable's scope starts inside the loop; its declaration belongs there, and the
            // creation's position changes javac's back-edge layout.
            moved = decl;
            buf.setLength(varDefsStart);
            buf.append(ExprProcessor.listToJava(varDefinitions.subList(0, varDefinitions.size() - 1), indent));
          }
          buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
          if (moved != null) {
            buf.appendIndent(indent + 1).append(moved.toJava(indent + 1)).append(";").appendLineSeparator();
          }
          // The guard's exit is the block after the loop. When the target laid that block's code
          // inside the loop, before the back edge, the source returned there and the tree only
          // moved the return after the loop: print it in the arm and let the sequence skip it.
          Statement insideReturn = guardReturn;
          buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
          buf.appendIndent(indent + 1).append("if (")
            .append(RoundTrip.negateCondition(conditionExprent.get(0)).toJava(indent + 1))
            .append(") {").appendLineSeparator();
          if (insideReturn != null) {
            buf.append(insideReturn.toJava(indent + 2));
            RoundTrip.markPrintedInBranch(insideReturn);
          } else {
            buf.appendIndent(indent + 2).append("break;").appendLineSeparator();
          }
          buf.appendIndent(indent + 1).append("}").appendLineSeparator();
          buf.appendIndent(indent).append("}").appendLineSeparator();
          break;
        }
        buf.appendIndent(indent).append("do {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("} while (");
        buf.pushNewlineGroup(indent, 1);
        buf.appendPossibleNewline();
        buf.append(conditionExprent.get(0).toJava(indent));
        buf.appendPossibleNewline("", true);
        buf.popNewlineGroup();
        buf.append(");").appendLineSeparator();
        break;
      case WHILE:
        // `while (true) { if (!C) { exit-block; break; } body }`: the target's test branches to
        // the body and the exit block it sends the guard to sits before that body. The loop's
        // successor is that block; print it inside the arm and let the sequence skip it there.
        Statement exitBlock = null;
        if (!isLabeled() && RoundTrip.whileGuardInsideBody(conditionExprent.get(0), this)) {
          exitBlock = getAllSuccessorEdges().get(0).getDestination();
          // The block prints inside the guard only when the sequence that follows the loop would
          // print it next, and nothing but this loop's own jump reaches it: a shared exit stays
          // where the tree put it.
          boolean sibling = getParent() instanceof SequenceStatement sequence
            && sequence.getStats().indexOf(exitBlock) == sequence.getStats().indexOf(this) + 1;
          boolean ownExit = true;
          for (StatEdge edge : exitBlock.getAllPredecessorEdges()) {
            // A jump from inside the loop that carries a label is a `break label;` of the source,
            // which prints where it stands; only this loop's own exit edge may move.
            if (edge.getSource() != this
                && (edge.labeled || !containsStatementStrict(edge.getSource()))) {
              ownExit = false;
              break;
            }
          }
          if (!sibling || !ownExit) {
            exitBlock = null;
          }
        }
        if (exitBlock != null) {
          buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
          buf.appendIndent(indent + 1).append("if (")
            .append(RoundTrip.negateCondition(conditionExprent.get(0)).toJava(indent + 1))
            .append(") {").appendLineSeparator();
          RoundTrip.markAfterIf(java.util.Collections.singletonList(exitBlock));
          buf.append(ExprProcessor.jmpWrapper(exitBlock, indent + 2, true));
          buf.appendIndent(indent + 2).append("break;").appendLineSeparator();
          buf.appendIndent(indent + 1).append("}").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          break;
        }
        Exprent whileGuard = RoundTrip.foldedBreakGuard(conditionExprent.get(0), this, first);
        buf.appendIndent(indent).append("while (");
        buf.pushNewlineGroup(indent, 1);
        buf.appendPossibleNewline();
        buf.append(whileGuard == null ? conditionExprent.get(0).toJava(indent)
          : ((FunctionExprent) conditionExprent.get(0)).getLstOperands().get(0).toJava(indent));
        buf.appendPossibleNewline("", true);
        buf.popNewlineGroup();
        buf.append(") {").appendLineSeparator();
        if (whileGuard != null) {
          appendBreakGuard(buf, whileGuard, indent + 1);
        }
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        break;
      case FOR:
        int incLine = RoundTrip.sourceLineDeep(incExprent.get(0));
        int condLine = RoundTrip.sourceLineDeep(conditionExprent.get(0));
        if (incLine >= 0 && condLine >= 0 && incLine != condLine) {
          TextBuffer body = ExprProcessor.jmpWrapper(first, indent + 1, false);
          if (!endsWithTransfer(body)) {
            Exprent init = initExprent.get(0);
            if (init instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assign
              && assign.getLeft() instanceof VarExprent left
              && !varDefinitions.isEmpty() && varDefinitions.get(varDefinitions.size() - 1) instanceof VarExprent decl
              && decl.getIndex() == left.getIndex()) {
              // The original declared and initialized in one statement; keep that shape.
              buf.setLength(varDefsStart);
              buf.append(ExprProcessor.listToJava(varDefinitions.subList(0, varDefinitions.size() - 1), indent));
              buf.appendIndent(indent).append(decl.toJava(indent)).append(" = ")
                .append(assign.getRight().toJava(indent)).append(";").appendLineSeparator();
            } else if (init != null) {
              buf.appendIndent(indent).append(init.toJava(indent)).append(";").appendLineSeparator();
            }
            buf.appendIndent(indent).append("while (").append(conditionExprent.get(0).toJava(indent)).append(") {").appendLineSeparator();
            buf.append(body);
            for (Exprent inc : incExprent) {
              if (inc != null) {
                buf.appendIndent(indent + 1).append(inc.toJava(indent + 1)).append(";").appendLineSeparator();
              }
            }
            buf.appendIndent(indent).append("}").appendLineSeparator();
            break;
          }
        }
        buf.appendIndent(indent);
        Exprent forGuard = RoundTrip.foldedBreakGuard(conditionExprent.get(0), this, first);
        buf.pushNewlineGroup(indent, 1);
        buf.append("for (");
        if (initExprent.get(0) != null) {
          buf.append(initExprent.get(0).toJava(indent));
        }
        buf.append(";").appendPossibleNewline(" ")
          .append(forGuard == null ? conditionExprent.get(0).toJava(indent)
            : ((FunctionExprent) conditionExprent.get(0)).getLstOperands().get(0).toJava(indent))
          .append(";").appendPossibleNewline(" ")
          .append(incToJava(indent))
          .appendPossibleNewline("", true);
        buf.popNewlineGroup();
        buf.append(") {").appendLineSeparator();
        if (forGuard != null) {
          appendBreakGuard(buf, forGuard, indent + 1);
        }
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, false));
        buf.appendIndent(indent).append("}").appendLineSeparator();
        break;
      case FOR_EACH:
        buf.appendIndent(indent).append("for (").append(initExprent.get(0).toJava(indent));
        incExprent.get(0).getInferredExprType(null); //TODO: Find a better then null? For now just calls it to clear casts if needed
        narrowForEachCast(incExprent.get(0), initExprent.get(0).getInferredExprType(null));
        buf.append(" : ").append(incExprent.get(0).toJava(indent)).append(") {").appendLineSeparator();
        buf.append(ExprProcessor.jmpWrapper(first, indent + 1, true));
        buf.appendIndent(indent).append("}").appendLineSeparator();
      }
    } finally {
      RoundTrip.exitAnyLoop();
    }

    return buf;
  }

  /** Prints {@code if (!test) { break; }} at the head of a loop body. */
  private static void appendBreakGuard(TextBuffer buf, Exprent test, int indent) {
    buf.appendIndent(indent).append("if (")
      .append(RoundTrip.negateCondition(test).toJava(indent)).append(") {").appendLineSeparator();
    buf.appendIndent(indent + 1).append("break;").appendLineSeparator();
    buf.appendIndent(indent).append("}").appendLineSeparator();
  }

  /** The last statement transfers control, so an update appended after it could not run. */
  /** The first exprent printed in the statement's tree, descending into its first child. */
  private static Exprent firstExprent(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null && !exprents.isEmpty()) {
      return exprents.get(0);
    }
    for (Statement child : stat.getStats()) {
      Exprent found = firstExprent(child);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  private static boolean endsWithTransfer(TextBuffer body) {
    String[] lines = body.toString().split("\\R");
    for (int i = lines.length - 1; i >= 0; i--) {
      String s = lines[i].trim();
      if (s.isEmpty() || s.equals("}") || s.equals("{")) {
        continue;
      }
      return s.endsWith("continue;") || s.endsWith("break;") || s.endsWith("return;")
        || s.startsWith("return ") && s.endsWith(";") || s.startsWith("throw ");
    }
    return false;
  }

  @Override
  public List<Exprent> getStatExprents() {
    List<Exprent> lst = new ArrayList<>();

    switch (looptype) {
      case FOR:
        if (getInitExprent() != null) {
          lst.add(getInitExprent());
        }
      case WHILE:
        lst.add(getConditionExprent());
        break;
      case FOR_EACH:
        lst.add(getInitExprent());
        lst.add(getIncExprent());
    }

    switch (looptype) {
      case DO_WHILE:
        lst.add(getConditionExprent());
        break;
      case FOR:
        for (Exprent inc : incExprent) {
          if (inc != null) {
            lst.add(inc);
          }
        }
    }

    return lst;
  }

  @Override
  public void replaceExprent(Exprent oldexpr, Exprent newexpr) {
    if (initExprent.get(0) == oldexpr) {
      initExprent.set(0, newexpr);
    }
    if (conditionExprent.get(0) == oldexpr) {
      conditionExprent.set(0, newexpr);
    }
    // A comma-separated update keeps several; the pass that replaces exprents loops until
    // nothing changed, so every slot has to accept its replacement or it spins forever.
    for (int i = 0; i < incExprent.size(); i++) {
      if (incExprent.get(i) == oldexpr) {
        incExprent.set(i, newexpr);
      }
    }
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>();


    if (looptype == Type.FOR_EACH) {
      getPatterns(getIncExprent(), vars);
      return vars;
    }

    if (getConditionExprent() == null) {
      return null;
    }

    getPatterns(getConditionExprent(), vars);

    return vars;
  }

  /**
   * A for-each over an expression whose recorded checkcast names a raw generic type prints the
   * cast with the type arguments the loop variable proves. A raw cast leaves javac's inference
   * on Object and the loop variable cannot be assigned; the erased checkcast a generic source
   * cast emits is exactly the one the target recorded. The arguments are solved by unifying the
   * cast class's recorded {@code Iterable} view with {@code Iterable<element>} — a container's
   * own argument need not be the element ({@code HolderSet<E>} iterates {@code Holder<E>}).
   */
  private static void narrowForEachCast(Exprent iterable, VarType elementType) {
    if (!(iterable instanceof FunctionExprent cast) || cast.getFuncType() != FunctionType.CAST
      || !cast.isRecordedCheckcast() || cast.getLstOperands().size() != 2
      || elementType == null || elementType.type != CodeType.OBJECT || elementType.arrayDim != 0
      || !(cast.getLstOperands().get(1) instanceof ConstExprent typeConst)) {
      return;
    }
    VarType castType = typeConst.getConstType();
    if (castType == null || castType.type != CodeType.OBJECT || castType.arrayDim != 0
      || castType.isGeneric()) {
      return;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(castType.value);
    if (cls == null || cls.getSignature() == null) {
      return;
    }
    GenericType view = cls.getSignature().genericType;
    VarType iterableType = GenericType.getGenericSuperType(view,
      new VarType(CodeType.OBJECT, 0, "java/lang/Iterable"));
    if (!(iterableType instanceof GenericType iterableView) || iterableView.getArguments().size() != 1) {
      return;
    }
    Map<VarType, VarType> solved = new HashMap<>();
    iterableView.mapGenVarsTo(new GenericType(CodeType.OBJECT, 0, "java/lang/Iterable", null,
      List.of(elementType), GenericType.WILDCARD_NO), solved);
    for (String parameter : cls.getSignature().fparameters) {
      VarType value = solved.get(GenericType.parse("T" + parameter + ";"));
      if (!isNameableForEachType(value)) {
        return;
      }
    }
    VarType narrowed = view.remap(solved);
    if (narrowed != null && (narrowed.isGeneric() || cls.getSignature().fparameters.isEmpty())) {
      typeConst.setConstType(narrowed);
    } else {
      return;
    }
    // The recorded cast is part of the loop expression's source; it must print even though the
    // decompiler's own inference finds it redundant (a raw cast loses the element type).
    cast.setNeedsCast(true);
  }

  /** A type a for-each cast can name: no free variable, wildcard or raw generic anywhere. */
  private static boolean isNameableForEachType(VarType type) {
    if (type == null || type == GenericType.DUMMY_VAR || type.type == CodeType.GENVAR) {
      return false;
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      for (VarType argument : generic.getArguments()) {
        if (!isNameableForEachType(argument)) {
          return false;
        }
      }
      return true;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    return cls == null || cls.getSignature() == null || cls.getSignature().fparameters.isEmpty();
  }

  private static void getPatterns(Exprent cond, List<VarExprent> vars) {
    List<Exprent> conditionList = cond.getAllExprents(true, true);

    for (Exprent condition : conditionList) {
      if (condition instanceof FunctionExprent func) {

        // Pattern match variable is implicitly defined
        if (func.getFuncType() == FunctionType.INSTANCEOF && func.getLstOperands().size() > 2) {
          vars.addAll(((Pattern) func.getLstOperands().get(2)).getPatternVars());
        }
      }
    }
  }

  @Override
  public boolean hasBasicSuccEdge() {
    return looptype != Type.INFINITE;
  }

  @Override
  public Statement getSimpleCopy() {
    return new DoStatement();
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public List<Exprent> getInitExprentList() {
    return initExprent;
  }

  public List<Exprent> getConditionExprentList() {
    return conditionExprent;
  }

  public List<Exprent> getIncExprentList() {
    return incExprent;
  }

  public Exprent getConditionExprent() {
    return conditionExprent.get(0);
  }

  public void setConditionExprent(Exprent conditionExprent) {
    this.conditionExprent.set(0, conditionExprent);
  }

  public Exprent getIncExprent() {
    return incExprent.get(0);
  }

  public void setIncExprent(Exprent incExprent) {
    this.incExprent.set(0, incExprent);
  }

  /** Adds a further update expression: the source's for header wrote several, comma-separated. */
  public void addIncExprent(Exprent exprent) {
    if (this.incExprent.get(0) == null) {
      this.incExprent.set(0, exprent);
    } else {
      this.incExprent.add(exprent);
    }
  }

  /** The for header's update text: every recorded increment, comma-separated. */
  private String incToJava(int indent) {
    StringBuilder out = new StringBuilder();
    for (Exprent inc : incExprent) {
      if (inc == null) {
        continue;
      }
      if (out.length() > 0) {
        out.append(", ");
      }
      out.append(inc.toJava(indent));
    }
    return out.toString();
  }

  public Exprent getInitExprent() {
    return initExprent.get(0);
  }

  public void setInitExprent(Exprent initExprent) {
    this.initExprent.set(0, initExprent);
  }

  public Type getLooptype() {
    return looptype;
  }

  /**
   * Prints a `while (true)` whose body was folded as `if (!E) { arm } exit;` back to the guard the
   * source wrote, `if (E) break; arm`, with the loop's exit left outside the body. False, printing
   * nothing, when the body is not that shape.
   */
  /**
   * Prints a `while (true)` whose exit was folded into the body as `if (E) { return; } rest` back to
   * the guard the source wrote, `if (E) break; rest`. The return sits past the loop's back edge in
   * the target, so it is the loop's exit and not part of the body; leaving it inside makes the loop
   * run once.
   */
  private boolean printBreakGuard(TextBuffer buf, int indent) {
    if (!(first instanceof SequenceStatement sequence) || sequence.getStats().size() != 2
        || !varDefinitions.isEmpty()) {
      return false;
    }
    List<Statement> stats = sequence.getStats();
    if (!(stats.get(0) instanceof IfStatement guard) || guard.getElsestat() != null
        || guard.getIfstat() == null || !guard.varDefinitions.isEmpty()
        || guard.getHeadexprent() == null) {
      return false;
    }
    org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent head = guard.getHeadexprent();
    ExitExprent exit = bareReturn(guard.getIfstat());
    if (exit == null) {
      return false;
    }
    int exitOffset = RoundTrip.firstOffset(guard.getIfstat());
    int bodyEnd = -1;
    for (int i = 1; i < stats.size(); i++) {
      bodyEnd = Math.max(bodyEnd, RoundTrip.lastOffset(stats.get(i)));
    }
    // The return lies past the body's last instruction: it is the loop's exit, not an arm.
    if (exitOffset < 0 || bodyEnd < 0 || exitOffset <= bodyEnd) {
      return false;
    }
    buf.appendIndent(indent).append("while (true) {").appendLineSeparator();
    buf.append(ExprProcessor.jmpWrapper(guard.getFirst(), indent + 1, false));
    buf.appendIndent(indent + 1).append("if (")
      .append(head.getCondition().toJava(indent + 1)).append(") {").appendLineSeparator();
    buf.appendIndent(indent + 2).append("break;").appendLineSeparator();
    buf.appendIndent(indent + 1).append("}").appendLineSeparator();
    for (int i = 1; i < stats.size(); i++) {
      buf.append(ExprProcessor.jmpWrapper(stats.get(i), indent + 1, true));
    }
    buf.appendIndent(indent).append("}").appendLineSeparator();
    return true;
  }

  /** The bare `return;` a block prints, or null. */
  private static ExitExprent bareReturn(Statement stat) {
    List<Exprent> exprents = stat == null ? null : stat.getExprents();
    if (exprents == null || exprents.size() != 1 || !(exprents.get(0) instanceof ExitExprent exit)) {
      return null;
    }
    return exit.getExitType() == ExitExprent.Type.RETURN && exit.getValue() == null ? exit : null;
  }


  public void setLooptype(Type looptype) {
    this.looptype = looptype;
  }
}

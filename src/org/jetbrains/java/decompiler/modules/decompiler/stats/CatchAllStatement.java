// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.ExceptionHandler;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

public class CatchAllStatement extends Statement {

  private Statement handler;

  private boolean isFinally;

  // FinallyProcessor sets this when the class file proves the body's try/catch and this finally
  // are one source statement, so the body catch prints inline instead of inside a second try.
  private boolean mergeCatch;

  private VarExprent monitor;

  private final List<VarExprent> vars = new ArrayList<>();

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected CatchAllStatement() {
    super(StatementType.CATCH_ALL);
  }

  protected CatchAllStatement(Statement head, Statement handler) {

    this();

    first = head;
    stats.addWithKey(head, head.id);

    this.handler = handler;
    stats.addWithKey(handler, handler.id);

    List<StatEdge> lstSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (!lstSuccs.isEmpty()) {
      StatEdge edge = lstSuccs.get(0);
      if (edge.getType() == StatEdge.TYPE_REGULAR) {
        post = edge.getDestination();
      }
    }
    
    vars.add(new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                            new VarType(CodeType.OBJECT, 0, "java/lang/Throwable"),
                            DecompilerContext.getVarProcessor()));
  }


  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {
    if (head.getLastBasicType() != LastBasicType.GENERAL) {
      return null;
    }

    Set<Statement> setHandlers = DecHelper.getUniquePredExceptions(head);
    if (setHandlers.size() != 1) {
      return null;
    }

    for (StatEdge edge : head.getSuccessorEdges(StatEdge.TYPE_EXCEPTION)) {
      Statement exc = edge.getDestination();

      if (edge.getExceptions() == null && exc.getLastBasicType() == LastBasicType.GENERAL && setHandlers.contains(exc)) {
        List<StatEdge> lstSuccs = exc.getSuccessorEdges(STATEDGE_DIRECT_ALL);
        if (lstSuccs.isEmpty() || lstSuccs.get(0).getType() != StatEdge.TYPE_REGULAR) {

          if (head.isMonitorEnter() || exc.isMonitorEnter()) {
            return null;
          }

          if (DecHelper.invalidHeadMerge(head)) {
            return null;
          }

          if (DecHelper.checkStatementExceptions(Arrays.asList(head, exc))) {
            return new CatchAllStatement(head, exc);
          }
        }
      }
    }

    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    String new_line_separator = DecompilerContext.getNewLineSeparator();

    TextBuffer buf = new TextBuffer();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    boolean labeled = isLabeled();
    if (labeled) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    // FinallyProcessor marked this finally when the class file proves its body catch belongs to
    // the same source statement: no catch-all exception range wraps a catch handler's own offset.
    // A real nested try inside the outer try protects the whole inner statement, handler included.
    Statement body = first;
    if (isFinally && mergeCatch) {
      Statement sole = soleCatch(first);
      if (sole != null) {
        body = sole;
      }
    }

    List<StatEdge> lstSuccs = body.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    if (body instanceof CatchStatement && body.varDefinitions.isEmpty() && isFinally &&
        !labeled && !body.isLabeled() && (lstSuccs.isEmpty() || !lstSuccs.get(0).explicit)) {
      TextBuffer content = ExprProcessor.jmpWrapper(body, indent, true);
      content.setLength(content.length() - new_line_separator.length());
      buf.append(content);
    }
    else {
      buf.appendIndent(indent).append("try {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(first, indent + 1, true));
      buf.appendIndent(indent).append("}");
    }

    if (isFinally) {
      buf.append(" finally");
    } else {
      buf.append(" catch (").append(vars.get(0).toJava(indent)).append(")");
    }
    buf.append(" {").appendLineSeparator();

    if (monitor != null) {
      buf.appendIndent(indent+1).append("if (").append(monitor.toJava(indent)).append(") {").appendLineSeparator();
    }

    buf.append(ExprProcessor.jmpWrapper(handler, indent + 1 + (monitor != null ? 1 : 0), true));

    if (monitor != null) {
      buf.appendIndent(indent + 1).append("}").appendLineSeparator();
    }

    buf.appendIndent(indent).append("}").appendLineSeparator();

    return buf;
  }

  @Override
  public void replaceStatement(Statement oldstat, Statement newstat) {

    if (handler == oldstat) {
      handler = newstat;
    }

    super.replaceStatement(oldstat, newstat);
  }

  @Override
  public Statement getSimpleCopy() {

    CatchAllStatement cas = new CatchAllStatement();

    cas.isFinally = this.isFinally;

    if (this.monitor != null) {
      cas.monitor = new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                                   VarType.VARTYPE_INT,
                                   DecompilerContext.getVarProcessor());
    }

    if (!this.vars.isEmpty()) {
      cas.vars.add(new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                              new VarType(CodeType.OBJECT, 0, "java/lang/Throwable"),
                              DecompilerContext.getVarProcessor()));
    }

    return cas;
  }

  @Override
  public void initSimpleCopy() {
    first = stats.get(0);
    handler = stats.get(1);
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public Statement getHandler() {
    return handler;
  }

  public boolean isFinally() {
    return isFinally;
  }

  public void setFinally(boolean isFinally) {
    this.isFinally = isFinally;
  }

  public void setMergeCatch(boolean mergeCatch) {
    this.mergeCatch = mergeCatch;
  }

  public VarExprent getMonitor() {
    return monitor;
  }

  public void setMonitor(VarExprent monitor) {
    this.monitor = monitor;
  }

  public List<VarExprent> getVars() {
    return vars;
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    return this.vars;
  }

  /**
   * The single try/catch a finally's body holds, or null. The body sequence may carry an emptied
   * block next to the catch — the leftover of the inlined copy — which prints nothing and does not
   * change the shapes around it.
   */
  public static @Nullable Statement soleCatch(Statement first) {
    @Nullable CatchStatement catchStat;
    if (first instanceof CatchStatement direct) {
      catchStat = direct;
    }
    else if (first instanceof SequenceStatement seq && !seq.isLabeled() && seq.varDefinitions.isEmpty()
        && !hasExplicitEdge(seq)) {
      catchStat = null;
      for (Statement child : seq.getStats()) {
        if (child instanceof CatchStatement nested) {
          if (catchStat != null) {
            return null;
          }
          catchStat = nested;
        }
        else if (!printsNothing(child)) {
          return null;
        }
      }
      if (catchStat == null) {
        return null;
      }
    }
    else {
      return null;
    }

    return catchStat;
  }

  private static boolean hasExplicitEdge(Statement stat) {
    List<StatEdge> succs = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    return !succs.isEmpty() && succs.get(0).explicit;
  }

  /** Whether the statement prints no text at all, including no break or continue. */
  private static boolean printsNothing(Statement stat) {
    return stat instanceof BasicBlockStatement block && !stat.isLabeled()
      && stat.varDefinitions.isEmpty() && !hasExplicitEdge(stat)
      && block.getBlock() != null && block.getBlock().getSeq().isEmpty()
      && (block.getExprents() == null || block.getExprents().isEmpty());
  }

  /**
   * Whether the class file proves the finally does not wrap the catch handler: no catch-all
   * exception range strictly contains a catch handler's own offset. A nested
   * {@code try { try … catch … } finally …} protects the whole inner statement, handler included,
   * so one of the outer ranges spans the handler; a single try/catch/finally ends its try range
   * before the handler and begins the handler's range at the handler itself.
   */
  public static boolean finallySpansNoCatchHandler(CatchStatement catchStat, StructMethod mt) {
    FullInstructionSequence seq = mt.getInstructionSequence();
    if (seq == null || seq.exceptionTable() == null) {
      return false;
    }
    List<Statement> stats = catchStat.getStats();
    if (stats.size() < 2) {
      return false;
    }
    for (int i = 1; i < stats.size(); i++) {
      BasicBlock block = stats.get(i).getBasichead() == null ? null : stats.get(i).getBasichead().getBlock();
      if (block == null || block.getSeq().isEmpty() || block.getInstruction(0).opcode != CodeConstants.opc_astore) {
        return false;
      }
      int offset = block.getOldOffset(0);
      if (offset < 0) {
        return false;
      }
      // The clause exists because a typed table entry catches at this offset. A handler offset no
      // entry targets belongs to another method's code (a copied tree), so this table says
      // nothing about it and the merge must not be decided from it.
      boolean targeted = false;
      for (ExceptionHandler handler : seq.exceptionTable().getHandlers()) {
        if (instructionOffset(seq, handler.handler()) == offset && handler.exceptionClass() != null) {
          targeted = true;
        }
        if (handler.exceptionClass() == null
            && instructionOffset(seq, handler.from()) < offset && offset < instructionOffset(seq, handler.to())) {
          return false;
        }
      }
      if (!targeted) {
        return false;
      }
    }
    return true;
  }

  /** The bytecode offset of the instruction at this index, or the end of code. */
  private static int instructionOffset(FullInstructionSequence seq, int index) {
    return index < seq.length() ? seq.getInstr(index).startOffset : Integer.MAX_VALUE;
  }
}

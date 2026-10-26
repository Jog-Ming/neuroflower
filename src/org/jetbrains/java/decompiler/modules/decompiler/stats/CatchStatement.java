// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Set;

public class CatchStatement extends Statement {
  private final List<List<String>> exctstrings = new ArrayList<>();
  private final List<VarExprent> vars = new ArrayList<>();
  private final List<Exprent> resources = new ArrayList<>();

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected CatchStatement() {
    super(StatementType.TRY_CATCH);
  }

  protected CatchStatement(Statement head, Statement next, Set<Statement> setHandlers) {
    this();

    first = head;
    stats.addWithKey(first, first.id);

    for (StatEdge edge : head.getSuccessorEdges(StatEdge.TYPE_EXCEPTION)) {
      Statement stat = edge.getDestination();

      if (setHandlers.contains(stat)) {
        stats.addWithKey(stat, stat.id);
        exctstrings.add(new ArrayList<>(edge.getExceptions()));
        
        vars.add(new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                                new VarType(CodeType.OBJECT, 0, edge.getExceptions().get(0)),
                                // FIXME: for now simply the first type. Should get the first common superclass when possible.
                                DecompilerContext.getVarProcessor()));
      }
    }

    if (next != null) {
      post = next;
    }
  }

  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {
    if (head.getLastBasicType() != LastBasicType.GENERAL) {
      return null;
    }

    Set<Statement> setHandlers = DecHelper.getUniquePredExceptions(head);
    if (!setHandlers.isEmpty()) {
      int hnextcount = 0; // either no statements with connection to next, or more than 1

      Statement next = null;
      List<StatEdge> lstHeadSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);
      if (!lstHeadSuccs.isEmpty() && lstHeadSuccs.get(0).getType() == StatEdge.TYPE_REGULAR) {
        next = lstHeadSuccs.get(0).getDestination();
        hnextcount = 2;
      }

      for (StatEdge edge : head.getSuccessorEdges(StatEdge.TYPE_EXCEPTION)) {
        Statement stat = edge.getDestination();

        boolean handlerok = true;

        if (edge.getExceptions() != null && setHandlers.contains(stat)) {
          if (stat.getLastBasicType() != LastBasicType.GENERAL) {
            handlerok = false;
          } else {
            List<StatEdge> lstStatSuccs = stat.getSuccessorEdges(STATEDGE_DIRECT_ALL);
            if (!lstStatSuccs.isEmpty() && lstStatSuccs.get(0).getType() == StatEdge.TYPE_REGULAR) {

              Statement statn = lstStatSuccs.get(0).getDestination();

              if (next == null) {
                next = statn;
              } else if (next != statn) {
                handlerok = false;
              }

              if (handlerok) {
                hnextcount++;
              }
            }
          }
        } else {
          handlerok = false;
        }

        if (!handlerok) {
          setHandlers.remove(stat);
        }
      }

      if (hnextcount != 1 && !setHandlers.isEmpty()) {
        List<Statement> lst = new ArrayList<>();
        lst.add(head);
        lst.addAll(setHandlers);

        for (Statement st : lst) {
          if (st.isMonitorEnter()) {
            return null;
          }
        }

        if (DecHelper.invalidHeadMerge(head)) {
          return null;
        }

        if (DecHelper.checkStatementExceptions(lst)) {
          return new CatchStatement(head, next, setHandlers);
        }
      }
    }
    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    if (resources.isEmpty()) {
      buf.appendIndent(indent).append("try {").appendLineSeparator();
    }
    else {
      buf.appendIndent(indent).append("try (");

      if (resources.size() > 1) {
        buf.appendLineSeparator();
        buf.append(ExprProcessor.listToJava(resources, indent + 1));
        buf.appendIndent(indent);
      }
      else {
        buf.append(resources.get(0).toJava(indent + 1));
      }
      buf.append(") {").appendLineSeparator();
    }

    // A return the decompiler folded into the try body: javac ends the protected range with a
    // skip-goto, so a return instruction past that destination was written after the try/catch.
    // A sequence-bodied try is accepted only when its last child is a lone return: the hoist
    // then moves exactly that statement out, never a return other statements still depend on.
    Exprent hoistedReturn = null;
    Statement hoistOwner = first;
    int firstHandler = firstHandlerOffset();
    if (firstHandler >= 0) {
      Statement owner = first.getExprents() != null && !first.getExprents().isEmpty()
        ? first : trailingReturnOwner(first);
      List<Exprent> bodyExprents = owner == null ? null : owner.getExprents();
      if (bodyExprents != null && !bodyExprents.isEmpty()) {
        Exprent lastBody = bodyExprents.get(bodyExprents.size() - 1);
        if (lastBody instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN
            && exit.getValue() != null && RoundTrip.returnPastTry(exit, firstHandler)) {
          hoistedReturn = lastBody;
          hoistOwner = owner;
          bodyExprents.remove(bodyExprents.size() - 1);
        }
      }
    }

    buf.append(ExprProcessor.jmpWrapper(first, indent + 1, true));
    buf.appendIndent(indent).append("}");

    for (int i = 1; i < stats.size(); i++) {
      Statement stat = stats.get(i);
      // map first instruction storing the exception to the catch statement
      BasicBlock block = stat.getBasichead().getBlock();
      Integer handlerOffset = null;
      if (!block.getSeq().isEmpty() && block.getInstruction(0).opcode == CodeConstants.opc_astore) {
        handlerOffset = block.getOldOffset(0);
      }

      // javac gives a try-with-resources' synthetic close the closing brace's line, so the
      // target's table says whether the original put the brace on a line without the catch.
      boolean newLine = DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_CATCH_LINE)
          && handlerOffset != null
          && RoundTrip.catchOnNewLine(i == 1 ? first : stats.get(i - 1), handlerOffset,
              i == 1 && !resources.isEmpty());
      if (newLine) {
        buf.appendLineSeparator().appendIndent(indent);
      }
      if (handlerOffset != null && handlerOffset > -1) {
        // The store belongs to the catch's line, which is this one only after a split.
        buf.addBytecodeMapping(handlerOffset);
      }
      buf.append(newLine ? "catch (" : " catch (");

      List<String> exception_types = exctstrings.get(i - 1);
      for (int exc_index = 0; exc_index < exception_types.size(); ++exc_index) {
        String name = ExprProcessor.getCastTypeName(new VarType(CodeType.OBJECT, 0, exception_types.get(exc_index)));
        if (exception_types.size() > 1 && exc_index > 0) { // multi-catch, Java 7 style
          buf.append(" | ");
        }
        buf.append(name);
      }

      buf.append(" ");

      VarExprent var = vars.get(i - 1);

      // A rename for a lambda clash reaches the uses (which lose their lvt) but not this
      // declaration. The renamed form extends the lvt name; a synthetic varN from the processor
      // does not, and there the lvt is the right name.
      String mapped = var.getProcessor() == null ? null
        : var.getProcessor().getVarName(var.getVarVersionPair());
      if (mapped != null && var.getLVT() != null && !mapped.equals(var.getLVT().getName())
          && mapped.startsWith(var.getLVT().getName())) {
        var.setLVT(null);
      }

      validateType(exception_types, var.getVarType());

      // Temporarily set variable as not a definition, since we just wrote the type above
      try (var v = var.new DefinitionLocker()) {
        buf.append(var.toJava(indent));
      }

      buf.append(") {").appendLineSeparator();
      // javac ends a catch parameter's scope at the closing brace, so a statement whose first
      // instruction lies at or after that end was written outside the catch block. The decompiler
      // folds such a tail into the handler, which lengthens the scope by the tail's first
      // statement. Print the tail after the brace, where the variable table says it belongs.
      List<Exprent> tail = null;
      if (i == stats.size() - 1 && stat.getExprents() != null
          && getParent() != null
          && (getParent().type == StatementType.SEQUENCE || getParent().type == StatementType.ROOT)) {
        int scopeEnd = catchScopeEnd(stat);
        // javac omits the parameter's entry exactly when the catch block was empty, so every
        // handler statement was written after the closing brace in the original source.
        int emptyStart = scopeEnd > 0 ? -1 : emptyCatchBodyStart(stat, var.getIndex());
        if (scopeEnd > 0 || emptyStart >= 0) {
          int boundary = scopeEnd > 0 ? scopeEnd : emptyStart;
          List<Exprent> exprents = stat.getExprents();
          int split = exprents.size();
          while (split > 0) {
            Exprent last = exprents.get(split - 1);
            if (last.bytecode == null || last.bytecode.isEmpty() || last.bytecode.nextSetBit(0) < boundary) {
              break;
            }
            split--;
          }
          if (split < exprents.size()) {
            tail = new ArrayList<>(exprents.subList(split, exprents.size()));
            exprents.subList(split, exprents.size()).clear();
          }
        }
      }
      buf.append(ExprProcessor.jmpWrapper(stat, indent + 1, false)).appendIndent(indent);
      // javac attributes the instruction after a try's protected range to the last catch's
      // closing brace. Map that offset to the brace so the aligner pads the arm to the line
      // the table records instead of leaving the brace on its unaligned line.
      if (i == stats.size() - 1 && handlerOffset != null) {
        int exitOffset = RoundTrip.handlerExitOffset(handlerOffset);
        if (exitOffset >= 0 && RoundTrip.lineAtOffset(exitOffset) > 0
            && RoundTrip.lineAtOffset(exitOffset) != RoundTrip.lineAtOffset(exitOffset - 1)) {
          buf.addBytecodeMapping(exitOffset);
        }
      }
      buf.append("}");
      if (tail != null) {
        buf.appendLineSeparator();
        buf.append(ExprProcessor.listToJava(tail, indent));
        stat.getExprents().addAll(tail);
      }
    }
    buf.appendLineSeparator();

    if (hoistedReturn != null) {
      hoistOwner.getExprents().add(hoistedReturn);
      buf.appendIndent(indent).append(hoistedReturn.toJava(indent)).append(";").appendLineSeparator();
    }

    return buf;
  }

  /** The bytecode offset of the first catch handler's exception store, or -1. */
  /**
   * The sequence statement whose own exprents end with the try body's trailing return, or null.
   * Only the body's last printing child is consulted: a return inside a nested arm is not the
   * body's own exit and must not be hoisted.
   */
  private static Statement trailingReturnOwner(Statement body) {
    List<Statement> children = body.getStats();
    if (children == null || children.isEmpty()) {
      return null;
    }
    for (int i = children.size() - 1; i >= 0; i--) {
      Statement child = children.get(i);
      if (RoundTrip.printsNothing(child)) {
        continue;
      }
      List<Exprent> exprents = child.getExprents();
      if (exprents == null || exprents.isEmpty()) {
        return null;
      }
      Exprent last = exprents.get(exprents.size() - 1);
      return last instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN
        && exit.getValue() != null ? child : null;
    }
    return null;
  }

  private int firstHandlerOffset() {
    if (stats.size() < 2) {
      return -1;
    }
    BasicBlock block = stats.get(1).getBasichead() == null ? null : stats.get(1).getBasichead().getBlock();
    if (block == null || block.getSeq().isEmpty() || block.getInstruction(0).opcode != CodeConstants.opc_astore) {
      return -1;
    }
    return block.getOldOffset(0);
  }

  /**
   * The end of the catch parameter's local variable table scope, or -1 when the table cannot name
   * it. The handler's first instruction stores the exception; the entry that starts at the next
   * instruction and covers it is the parameter, and its length ends at the original closing brace.
   */
  private static int catchScopeEnd(Statement handler) {
    BasicBlock block = handler.getBasichead() == null ? null : handler.getBasichead().getBlock();
    if (block == null || block.getSeq().length() < 2 || block.getInstruction(0).opcode != CodeConstants.opc_astore) {
      return -1;
    }
    StructMethod mt = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    StructLocalVariableTableAttribute lvt = mt == null ? null : mt.getLocalVariableAttr();
    if (lvt == null) {
      return -1;
    }
    int body = block.getOldOffset(1);
    if (body < 0) {
      return -1;
    }
    return lvt.matchingVars(block.getInstruction(0).operand(0), body)
      .findFirst().map(StructLocalVariableTableAttribute.LocalVariable::getEnd).orElse(-1);
  }

  /**
   * The handler's first offset when the table has no entry for the catch parameter. javac writes
   * that entry for every non-empty catch body, so its absence marks an originally empty body.
   */
  private static int emptyCatchBodyStart(Statement handler, int varIndex) {
    BasicBlock block = handler.getBasichead() == null ? null : handler.getBasichead().getBlock();
    if (block == null || block.getSeq().length() < 2 || block.getInstruction(0).opcode != CodeConstants.opc_astore) {
      return -1;
    }
    StructMethod mt = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    StructLocalVariableTableAttribute lvt = mt == null ? null : mt.getLocalVariableAttr();
    if (lvt == null) {
      return -1;
    }
    int body = block.getOldOffset(1);
    if (body < 0) {
      return -1;
    }
    int slot = block.getInstruction(0).operand(0);
    if (lvt.matchingVars(slot, body).findFirst().isPresent()) {
      return -1;
    }
    // A try-with-resources close handler stores its throwable the same way but uses it, and javac
    // writes no entry for it either. Only a body that never touches the variable was empty.
    if (handler.getExprents() != null) {
      for (Exprent exprent : handler.getExprents()) {
        if (usesVar(exprent, varIndex)) {
          return -1;
        }
      }
    }
    return body;
  }

  private static boolean usesVar(Exprent exprent, int index) {
    if (exprent instanceof VarExprent var && var.getIndex() == index) {
      return true;
    }
    for (Exprent child : exprent.getAllExprents()) {
      if (usesVar(child, index)) {
        return true;
      }
    }
    return false;
  }

  private void validateType(List<String> exTypes, VarType exVarType) {
    // TODO: join together all types, then check if exVarType instanceof that
    // Not correct!!
    if (ValidationHelper.VALIDATE) {
//      VarType type = new VarType(CodeType.OBJECT, 0, exTypes.get(exTypes.size() - 1));
//      ValidationHelper.validateTrue(type.higherEqualInLatticeThan(exVarType), "Invalid exception type " + exVarType + " " + type);
    }
  }

  @Override
  public List<Exprent> getStatExprents() {
    List<Exprent> lst = new ArrayList<>(resources);
    lst.addAll(vars);
    return lst;
  }

  @Override
  public Statement getSimpleCopy() {
    CatchStatement cs = new CatchStatement();

    for (List<String> exc : this.exctstrings) {
      cs.exctstrings.add(new ArrayList<>(exc));
      cs.vars.add(new VarExprent(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.VAR_COUNTER),
                                 new VarType(CodeType.OBJECT, 0, exc.get(0)),
                                 DecompilerContext.getVarProcessor()));
    }

    return cs;
  }

  public void getOffset(BitSet values) {
    super.getOffset(values);

    for (Exprent exp : this.getResources()) {
      exp.getBytecodeRange(values);
    }
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public List<List<String>> getExctStrings() {
    return exctstrings;
  }

  public List<VarExprent> getVars() {
    return vars;
  }

  public List<Exprent> getResources() {
    return resources;
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>(getVars());

    // resource vars must also be included
    for (Exprent exp : getResources()) {
      if (exp instanceof AssignmentExprent assignment) {
        vars.add((VarExprent) assignment.getLeft());
      }
    }

    return vars;
  }
}
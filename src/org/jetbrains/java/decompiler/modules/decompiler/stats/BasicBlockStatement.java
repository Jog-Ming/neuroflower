// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.util.StartEndPair;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.List;

public final class BasicBlockStatement extends Statement {

  // *****************************************************************************
  // private fields
  // *****************************************************************************

  private final BasicBlock block;
  private boolean removableMonitorexit;

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  public BasicBlockStatement(BasicBlock block) {

    super(StatementType.BASIC_BLOCK, block.id);

    this.block = block;

    CounterContainer coun = DecompilerContext.getCounterContainer();
    if (id >= coun.getCounter(CounterContainer.STATEMENT_COUNTER)) {
      coun.setCounter(CounterContainer.STATEMENT_COUNTER, id + 1);
    }

    Instruction instr = block.getLastInstruction();
    if (instr != null) {
      if (instr.group == CodeConstants.GROUP_JUMP && instr.opcode != CodeConstants.opc_goto) {
        lastBasicType = LastBasicType.IF;
      }
      else if (instr.group == CodeConstants.GROUP_SWITCH) {
        lastBasicType = LastBasicType.SWITCH;
      }
    }

    // monitorenter and monitorexits
    buildMonitorFlags();
  }

  @Override
  public void markMonitorexitDead() {
    InstructionSequence seq = this.getBlock().getSeq();

    if (seq != null && !seq.isEmpty()) {
      for (int i = 0; i < seq.length(); i++) {
        if (seq.getInstr(i).opcode == CodeConstants.opc_monitorexit) {
          this.setRemovableMonitorexit(true);
          break;
        }
      }
    }
  }

  @Override
  public BasicBlockStatement getBasichead() {
    return this;
  }

  // *****************************************************************************
  // public methods
  // *****************************************************************************

  @Override
  public TextBuffer toJava(int indent) {
    if (varDefinitions.isEmpty() && RoundTrip.isConsumedGuardExit(this)) {
      return new TextBuffer();
    }
    TextBuffer tb = ExprProcessor.listToJava(varDefinitions, indent);
    boolean islabeled = isLabeled();
    if (islabeled) {
      tb.appendIndent(indent).append("label").append(id).append(':').append("// $VF: Invalid label!").appendLineSeparator();
    }

    if ("off".equals(System.getenv("NEUROFLOWER_BLOCKSCOPES"))) {
      tb.append(ExprProcessor.listToJava(exprents, indent));
      return tb;
    }

    // The target's local variable table says when the source declared the same name again in a
    // disjoint block: the second store reopens the variable, the statements between the scopes are
    // wrapped in a block, and the store prints as a declaration.
    int size = exprents.size();
    boolean[] openAt = new boolean[size];
    boolean[] closeBefore = new boolean[size + 1];
    planBlockScopes(openAt, closeBefore);
    boolean changed = closeBefore[size];
    for (int i = 0; i < size && !changed; i++) {
      changed = openAt[i] || closeBefore[i];
    }
    if (!changed) {
      // A local whose scope the table proves ended inside this block: the slot is handed to a
      // later local, so the run that starts at the declaration was a block of its own.
      tb.append(org.jetbrains.java.decompiler.modules.decompiler.RoundTrip
        .withBlocks(exprents, 0, size, indent, printsOwnEnd()));
      return tb;
    }
    for (int i = 0; i < size; i++) {
      if (closeBefore[i]) {
        tb.appendIndent(indent).append("}").appendLineSeparator();
      }
      if (openAt[i]) {
        tb.appendIndent(indent).append("{").appendLineSeparator();
      }
      tb.append(ExprProcessor.listToJava(List.of(exprents.get(i)), indent));
    }
    if (closeBefore[size]) {
      tb.appendIndent(indent).append("}").appendLineSeparator();
    }
    return tb;
  }

  /**
   * Whether a block closing at this one's end would be a block of its own: a sequence prints no
   * brace around its statements, but a loop body, an arm or a try already does, and there the
   * closing brace of the construct is the one that ends the scope.
   */
  private boolean printsOwnEnd() {
    if (!(getParent() instanceof SequenceStatement sequence)) {
      return false;
    }
    Statement above = sequence.getParent();
    return above == null || !(above instanceof DoStatement || above instanceof IfStatement
      || above instanceof CatchAllStatement || above instanceof CatchStatement
      || above instanceof SynchronizedStatement);
  }

  private void planBlockScopes(boolean[] openAt, boolean[] closeBefore) {
    Object wrapper = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (wrapper instanceof org.jetbrains.java.decompiler.main.rels.MethodWrapper current
        && current.methodStruct.getClassQualifiedName().contains("$")) {
      return; // anonymous, local and member classes carry generated scopes of their own
    }
    List<int[]> windows = new ArrayList<>();
    for (int i = 0; i < exprents.size(); i++) {
      Exprent exprent = exprents.get(i);
      if (!(exprent instanceof AssignmentExprent assignment)
          || !(assignment.getLeft() instanceof VarExprent left)
          || left.getIndex() == 0 || left.isDefinition() || exprent.bytecode == null) {
        continue; // only a plain assignment can reopen a source variable
      }
      List<int[]> scopes = org.jetbrains.java.decompiler.modules.decompiler.RoundTrip
        .localScopes(left.getIndex(), left.getName());
      if (scopes.size() < 2) {
        continue;
      }
      for (int k = 1; k < scopes.size(); k++) {
        int scopeStart = scopes.get(k)[0];
        if (!exprent.bytecode.get(scopeStart) && !exprent.bytecode.get(scopeStart - 1)) {
          continue;
        }
        int[] earlier = scopes.get(k - 1);
        int open = -1;
        for (int j = i; j >= 0; j--) {
          java.util.BitSet bits = exprents.get(j).bytecode;
          if (bits != null && (bits.get(earlier[0]) || bits.get(earlier[0] - 1))) {
            open = j;
            break;
          }
        }
        if (open < 0) {
          continue;
        }
        int close = exprents.size();
        for (int j = open + 1; j <= i; j++) {
          java.util.BitSet bits = exprents.get(j).bytecode;
          if (bits != null && !bits.isEmpty() && bits.nextSetBit(0) >= earlier[1]) {
            close = j;
            break;
          }
        }
        if (close > open) {
          windows.add(new int[]{open, close});
          left.setDefinition(true);
        }
        break;
      }
    }
    windows.sort(java.util.Comparator.comparingInt(a -> a[0]));
    int mergedStart = -1;
    int mergedEnd = -1;
    for (int[] window : windows) {
      if (mergedStart < 0) {
        mergedStart = window[0];
        mergedEnd = window[1];
      } else if (window[0] < mergedEnd) {
        mergedEnd = Math.max(mergedEnd, window[1]);
      } else {
        openAt[mergedStart] = true;
        closeBefore[mergedEnd] = true;
        mergedStart = window[0];
        mergedEnd = window[1];
      }
    }
    if (mergedStart >= 0) {
      openAt[mergedStart] = true;
      closeBefore[mergedEnd] = true;
    }
  }


  @Override
  public Statement getSimpleCopy() {

    BasicBlock newblock = new BasicBlock(
      DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.STATEMENT_COUNTER));

    InstructionSequence seq = new InstructionSequence();
    for (var instr : block.getSeq()) {
      seq.addInstruction(instr.clone());
    }

    newblock.setSeq(seq);

    return new BasicBlockStatement(newblock);
  }

  // TODO: cache this?
  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    if (getExprents() != null && getExprents().size() > 0) {
      List<VarExprent> vars = new ArrayList<>();
      List<Exprent> exps = getExprents();

      for (Exprent exp : exps) {
        List<Exprent> inner = exp.getAllExprents(true);
        inner.add(exp);

        for (Exprent exprent : inner) {
          if (exprent instanceof FunctionExprent func && func.getFuncType() == FunctionExprent.FunctionType.INSTANCEOF) {
            if (func.getLstOperands().size() > 2) {
              vars.addAll(((Pattern) func.getLstOperands().get(2)).getPatternVars());
            }
          }
        }
      }

      return vars;
    }

    return null;
  }

  public boolean isRemovableMonitorexit() {
    return removableMonitorexit;
  }

  public void setRemovableMonitorexit(boolean removableMonitorexit) {
    this.removableMonitorexit = removableMonitorexit;
  }

  public static BasicBlockStatement create() {
    BasicBlockStatement stat = new BasicBlockStatement(new BasicBlock(DecompilerContext.getCounterContainer().getCounterAndIncrement(CounterContainer.STATEMENT_COUNTER)));
    stat.setExprents(new ArrayList<>());

    return stat;
  }

  @Override
  public boolean hasBasicSuccEdge() {
    return true;
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public BasicBlock getBlock() {
    return block;
  }

  // TODO: is this allowed? SecondaryFunctionsHelper says "only head expressions can be replaced!"
  @Override
  public void replaceExprent(Exprent oldexpr, Exprent newexpr) {
    for (int i = 0; i < this.exprents.size(); i++) {
      if (this.exprents.get(i) == oldexpr) {
        this.exprents.set(i, newexpr);
      }
    }
  }

  @Override
  public StartEndPair getStartEndRange() {
    if (block.size() > 0) {
      return new StartEndPair(block.getStartInstruction(), block.getEndInstruction());
    } else {
      return new StartEndPair(0, 0);
    }
  }
}

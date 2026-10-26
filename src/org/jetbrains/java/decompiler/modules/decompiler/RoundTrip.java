package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLineNumberTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.util.BitSet;
import java.util.List;

/** Target-aware choices for byte-faithful output. Only active with {@code --round-trip=1}. */
public final class RoundTrip {
  private static final java.util.Map<StructMethod, BitSet> VOID_RETURNS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Instruction end offset by start offset; the live sequence is released before printing. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> INSTRUCTION_ENDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Per method: handler bytecode offset -> first offset after its protected range. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> HANDLER_ENDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Returns already printed as guard exits; the same instruction must not print a second time. */
  private static final java.util.Map<StructMethod, java.util.Set<Integer>> CONSUMED_GUARD_EXITS = new java.util.concurrent.ConcurrentHashMap<>();
  /** For each continue guard, the end offset of its condition branch maps to the loop-head offset. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> CONTINUE_GUARDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Continue guards by branch end: {goto offset (the continue), body start (the branch target)}. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, int[]>> CONTINUE_SITES = new java.util.concurrent.ConcurrentHashMap<>();
  /** The same, for an if/else whose then arm ends with the continue: branch end maps to loop head. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> CONTINUE_ELSE_GUARDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Continue-else guards by branch end: {goto offset (the continue), else start (the branch target)}. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, int[]>> CONTINUE_ELSE_SITES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Branch opcode by the end offset of each conditional branch, for polarity checks. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> BRANCHES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Jump target of each conditional branch, by the end offset of the branch instruction. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> BRANCH_TARGETS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Target of each conditional branch, by its start offset. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> BRANCH_STARTS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Target of each goto, by its start offset. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> GOTO_TARGETS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Slot stored immediately before the load a value return reads, by the return's start offset. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> RETURN_STORES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Instructions that store or discard the stack's value: a call's result ends its statement here. */
  private static final java.util.Map<StructMethod, BitSet> VALUE_SINKS = new java.util.concurrent.ConcurrentHashMap<>();

  private RoundTrip() {}

  /** Remember where a method's void returns are; the instruction sequence is gone by print time. */
  public static void recordMethod(StructMethod method, FullInstructionSequence seq) {
    BitSet returns = new BitSet();
    BitSet sinks = new BitSet();
    java.util.Map<Integer, Integer> guards = new java.util.HashMap<>();
    java.util.Map<Integer, int[]> sites = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> elseGuards = new java.util.HashMap<>();
    java.util.Map<Integer, int[]> elseSites = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> prevByEnd = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> branches = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> branchTargets = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> ends = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> returnStores = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> gotos = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> branchStarts = new java.util.HashMap<>();
    for (int i = 0; i < seq.length(); i++) {
      Instruction instr = seq.getInstr(i);
      ends.put(instr.startOffset, instr.startOffset + instr.length);
      if (instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore
        || instr.opcode == CodeConstants.opc_putfield || instr.opcode == CodeConstants.opc_putstatic
        || instr.opcode == CodeConstants.opc_pop || instr.opcode == CodeConstants.opc_pop2) {
        sinks.set(instr.startOffset);
      }
      if (instr.opcode == CodeConstants.opc_goto) {
        gotos.put(instr.startOffset, instr.startOffset + instr.operand(0));
      }
      if (instr.opcode == CodeConstants.opc_return) {
        returns.set(instr.startOffset);
      }
      // `store N; load N; return`: javac's copy of a value the source kept in a variable. The
      // printer folded the copy away; the slot's LVT entry proves the variable existed.
      if (i >= 2 && instr.opcode >= CodeConstants.opc_ireturn && instr.opcode <= CodeConstants.opc_areturn) {
        Instruction load = seq.getInstr(i - 1);
        Instruction store = seq.getInstr(i - 2);
        if (load.opcode >= CodeConstants.opc_iload && load.opcode <= CodeConstants.opc_aload
          && store.opcode >= CodeConstants.opc_istore && store.opcode <= CodeConstants.opc_astore
          && load.operand(0) == store.operand(0)) {
          returnStores.put(instr.startOffset, load.operand(0));
        }
      }
      if (isConditional(instr.opcode)) {
        branchStarts.put(instr.startOffset, instr.startOffset + instr.operand(0));
        branches.put(instr.startOffset + instr.length, instr.opcode);
        branchTargets.put(instr.startOffset + instr.length, instr.startOffset + instr.operand(0));
      }
      // `if (C) continue;`: the branch falls through to a goto and jumps past it to the body.
      // The goto may go back to the loop head (while/for-each) or forward to a for loop's
      // increment; the loop the statement belongs to decides which target is the continue.
      if (i + 1 < seq.length() && isConditional(instr.opcode)) {
        Instruction next = seq.getInstr(i + 1);
        if (next.opcode == CodeConstants.opc_goto) {
          int branchTarget = instr.startOffset + instr.operand(0);
          int gotoTarget = next.startOffset + next.operand(0);
          if (branchTarget > next.startOffset) {
            // Key by the branch's end; the head exprent's offsets cover the branch instruction.
            guards.put(instr.startOffset + instr.length, gotoTarget);
            sites.put(instr.startOffset + instr.length, new int[]{next.startOffset, branchTarget});
          }
        }
      }
      prevByEnd.put(instr.startOffset + instr.length, instr.startOffset);
    }
    // `if (C) { ...; continue; } rest`: the branch jumps over the then arm to `rest`, and the
    // then arm's terminal goto is the continue. Instructions are contiguous, so that goto is the
    // one ending exactly where a forward branch lands; record it under the branch's end.
    for (java.util.Map.Entry<Integer, Integer> branch : branchTargets.entrySet()) {
      Integer prev = prevByEnd.get(branch.getValue());
      if (branch.getValue() > branch.getKey() && prev != null && gotos.containsKey(prev)) {
        elseGuards.put(branch.getKey(), gotos.get(prev));
        elseSites.put(branch.getKey(), new int[]{prev, branch.getValue()});
      }
    }
    VOID_RETURNS.put(method, returns);
    VALUE_SINKS.put(method, sinks);
    CONTINUE_GUARDS.put(method, guards);
    CONTINUE_SITES.put(method, sites);
    CONTINUE_ELSE_GUARDS.put(method, elseGuards);
    CONTINUE_ELSE_SITES.put(method, elseSites);
    BRANCHES.put(method, branches);
    BRANCH_TARGETS.put(method, branchTargets);
    INSTRUCTION_ENDS.put(method, ends);
    java.util.Map<Integer, Integer> handlerEnds = new java.util.HashMap<>();
    org.jetbrains.java.decompiler.code.ExceptionTable table = seq.exceptionTable();
    if (table != null) {
      for (org.jetbrains.java.decompiler.code.ExceptionHandler handler : table.getHandlers()) {
        int handlerIndex = handler.handler();
        int toIndex = handler.to();
        if (handlerIndex < 0 || handlerIndex >= seq.length() || toIndex < 0 || toIndex >= seq.length()) {
          continue;
        }
        // Only a try body that falls through ends with javac's skip-goto; that goto carries the
        // enclosing try statement's closing-brace line. Where the body returns or throws, the
        // range ends at the handler itself, whose line is the catch clause's, not the brace's.
        Instruction exit = seq.getInstr(toIndex);
        if (exit.opcode != CodeConstants.opc_goto && exit.opcode != CodeConstants.opc_goto_w) {
          continue;
        }
        handlerEnds.put(seq.getInstr(handlerIndex).startOffset, exit.startOffset);
      }
    }
    HANDLER_ENDS.put(method, handlerEnds);
    GOTO_TARGETS.put(method, gotos);
    BRANCH_STARTS.put(method, branchStarts);
    RETURN_STORES.put(method, returnStores);
  }

  /**
   * The slot a value return's preceding load reads and the instruction store writes. -1 unless the
   * target's last three instructions before the return are exactly {@code store N; load N; ret}.
   */
  public static int storedBeforeReturn(BitSet offsets) {
    StructMethod method = currentMethod();
    if (method == null || offsets == null) {
      return -1;
    }
    java.util.Map<Integer, Integer> stores = RETURN_STORES.get(method);
    if (stores == null) {
      return -1;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer slot = stores.get(offset);
      if (slot != null) {
        return slot;
      }
    }
    return -1;
  }

  /**
   * Whether the statement opens a block whose table entry was written before the parameters:
   * javac emits a block's variables when the block closes, so such an entry was block scoped.
   * The block must also end at the method's close for the tail to be the guard's else arm.
   */
  public static boolean opensTrailingBlock(Statement firstTail) {
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute lvt = method == null ? null : method.getLocalVariableAttr();
    if (lvt == null) {
      return false;
    }
    List<LocalVariable> vars = lvt.getVariables().toList();
    int paramsStart = Integer.MAX_VALUE;
    int maxEnd = 0;
    for (LocalVariable v : vars) {
      if (v.getStart() == 0) {
        paramsStart = Math.min(paramsStart, v.getOrder());
      }
      maxEnd = Math.max(maxEnd, v.getEnd());
    }
    if (paramsStart == Integer.MAX_VALUE || !spansMethod(vars, maxEnd)) {
      return false;
    }
    LocalVariable first = firstDefinedLvt(firstTail);
    return first != null && first.getStart() > 0 && first.getOrder() >= 0
        && first.getOrder() < paramsStart && first.getEnd() == maxEnd;
  }

  /**
   * Whether the statement's first local was method scoped in the source: its entry follows the
   * parameter group, so the original declared it outside the enclosing brace.
   */
  public static boolean startsWithMethodScopeLocal(Statement stat) {
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute lvt = method == null ? null : method.getLocalVariableAttr();
    if (lvt == null) {
      return false;
    }
    List<LocalVariable> vars = lvt.getVariables().toList();
    int paramsEnd = -1;
    for (LocalVariable v : vars) {
      if (v.getStart() == 0) {
        paramsEnd = Math.max(paramsEnd, v.getOrder());
      }
    }
    if (paramsEnd < 0) {
      return false;
    }
    LocalVariable first = firstDefinedLvt(stat);
    return first != null && first.getStart() > 0 && first.getOrder() > paramsEnd;
  }

  private static boolean spansMethod(List<LocalVariable> vars, int maxEnd) {
    for (LocalVariable v : vars) {
      if (v.getStart() == 0 && v.getEnd() == maxEnd) {
        return true;
      }
    }
    return false;
  }

  public static LocalVariable firstDefinedLvt(Statement stat) {
    if (stat.getExprents() != null) {
      for (Exprent exprent : stat.getExprents()) {
        for (Exprent e : exprent.getAllExprents(true, true)) {
          if (e instanceof VarExprent var && var.isDefinition() && var.getLVT() != null) {
            return var.getLVT();
          }
        }
      }
    }
    for (Statement child : stat.getStats()) {
      LocalVariable lvt = firstDefinedLvt(child);
      if (lvt != null) {
        return lvt;
      }
    }
    return null;
  }

  /**
   * The target's void return that ends the block between a condition and its body, when the line
   * table puts that return before the body's first line; -1 when no such return proves the guard
   * shape. The return block is exactly the fall-through the printer folded into the body, so the
   * AST does not carry it.
   */
  public static int voidReturnBeforeBody(BitSet conditionOffsets, Statement body) {
    if (!selector("bodyguard")) {
      return -1;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return -1;
    }
    BitSet returns = VOID_RETURNS.get(method);
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    StructLineNumberTableAttribute table = method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    int bodyStart = firstOffset(body);
    if (returns == null || ends == null || table == null || conditionOffsets == null
        || conditionOffsets.isEmpty() || bodyStart < 0) {
      return -1;
    }
    int conditionEnd = -1;
    for (int offset = conditionOffsets.nextSetBit(0); offset >= 0; offset = conditionOffsets.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end != null && end > conditionEnd) {
        conditionEnd = end;
      }
    }
    if (conditionEnd < 0) {
      return -1;
    }
    int exit = -1;
    for (int candidate = returns.nextSetBit(conditionEnd); candidate >= 0 && candidate < bodyStart;
         candidate = returns.nextSetBit(candidate + 1)) {
      exit = candidate;
    }
    if (exit < 0) {
      return -1;
    }
    int exitLine = table.findLineNumber(exit);
    int bodyLine = table.findLineNumber(bodyStart);
    return exitLine >= 0 && bodyLine >= 0 && exitLine < bodyLine ? exit : -1;
  }

  /** True when this statement would print no text at all (an empty arm or block). */
  public static boolean printsNothing(Statement statement) {
    if (statement == null) {
      return true;
    }
    if (!statement.getVarDefinitions().isEmpty()) {
      return false;
    }
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null) {
      return exprents.isEmpty();
    }
    for (Statement child : statement.getStats()) {
      if (!printsNothing(child)) {
        return false;
      }
    }
    return true;
  }

  /**
   * True when the target's line table puts this if's else arm before its then arm, so the source
   * wrote the arms in the other order with the negated condition.
   */
  public static boolean swapIfArmsByLine(Statement thenArm, Statement elseArm) {
    if (!selector("polarityline")) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    // A block that prints nothing has no line of its own; its offset belongs to the branch.
    if (printsNothing(thenArm) || printsNothing(elseArm)) {
      return false;
    }
    int thenStart = firstOffset(thenArm);
    int elseStart = firstOffset(elseArm);
    if (thenStart < 0 || elseStart < 0) {
      return false;
    }
    int thenLine = table.findLineNumber(thenStart);
    int elseLine = table.findLineNumber(elseStart);
    return thenLine >= 0 && elseLine >= 0 && thenLine > elseLine;
  }

  /**
   * True when the target branched the other way: the original wrote the negated condition with the
   * arms swapped. Only plain boolean tests are handled; comparisons and short-circuit conditions
   * compile to different opcode families and are left alone.
   */
  public static boolean swapIfArms(Exprent head) {
    if (!selector("polarity") || !(head instanceof IfExprent ifHead)) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> branches = BRANCHES.get(method);
    BitSet offsets = head.bytecode;
    if (branches == null || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer opcode = branches.get(offsets.length());
    if (opcode == null) {
      return false;
    }
    int expected = lastBranch(ifHead.getCondition());
    int other = complement(expected);
    return other != 0 && opcode == other;
  }

  /**
   * True when the target's last condition branch jumps exactly to the instruction this exprent
   * starts at. A negated instanceof guard with an explicit cast compiles to {@code ifne} over the
   * returning arm to the cast; the same guard written with a pattern variable branches with
   * {@code ifeq} to the returning arm and falls through to the cast. The jump target therefore
   * proves which of the two sources the class file came from.
   */
  public static boolean branchEntersAt(Exprent head, Exprent exprent) {
    if (!selector("patternjump")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null || head == null || exprent == null) {
      return false;
    }
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    BitSet offsets = head.bytecode;
    // The assignment's own offsets start at the store; the value it stores starts earlier.
    BitSet starts = new BitSet();
    exprent.getBytecodeRange(starts);
    if (targets == null || offsets == null || offsets.isEmpty() || starts.isEmpty()) {
      return false;
    }
    Integer target = targets.get(offsets.length());
    return target != null && target == starts.nextSetBit(0);
  }

  /**
   * The branch opcode javac emits after the last test of this condition when the arm is skipped —
   * the opcode the target would carry had the condition been written this way. `&&` and `||` both
   * test their right operand last and jump to the else arm when it is false; a negation swaps the
   * branch. Returns 0 for tests outside the boolean/null families.
   */
  private static int lastBranch(Exprent condition) {
    if (condition instanceof FunctionExprent function) {
      FunctionExprent.FunctionType type = function.getFuncType();
      if (type == FunctionExprent.FunctionType.BOOL_NOT) {
        return complement(lastBranch(function.getLstOperands().get(0)));
      }
      if (type == FunctionExprent.FunctionType.BOOLEAN_AND || type == FunctionExprent.FunctionType.BOOLEAN_OR) {
        java.util.List<Exprent> operands = function.getLstOperands();
        return lastBranch(operands.get(operands.size() - 1));
      }
      if ((type == FunctionExprent.FunctionType.EQ || type == FunctionExprent.FunctionType.NE)
          && function.getLstOperands().size() == 2
          && (isNull(function.getLstOperands().get(0)) || isNull(function.getLstOperands().get(1)))) {
        // `x == null` is false when non-null: the skip branch is ifnonnull.
        return type == FunctionExprent.FunctionType.EQ ? CodeConstants.opc_ifnonnull : CodeConstants.opc_ifnull;
      }
      if ((type == FunctionExprent.FunctionType.EQ || type == FunctionExprent.FunctionType.NE)
          && function.getLstOperands().size() == 2) {
        // javac folds a comparison against a boolean constant into the boolean's own test:
        // `x != false` and `x == true` are x (ifeq), `x == false` and `x != true` are !x (ifne).
        Boolean constant = null;
        Exprent other = null;
        Boolean left0 = booleanConstant(function.getLstOperands().get(0));
        Boolean right0 = booleanConstant(function.getLstOperands().get(1));
        if (left0 != null) {
          constant = left0;
          other = function.getLstOperands().get(1);
        } else if (right0 != null) {
          constant = right0;
          other = function.getLstOperands().get(0);
        }
        if (constant != null && other != null && isPlainBoolean(other)) {
          boolean positive = (type == FunctionExprent.FunctionType.NE) != constant;
          return positive ? lastBranch(other) : complement(lastBranch(other));
        }
      }
      if (type == FunctionExprent.FunctionType.INSTANCEOF) {
        return CodeConstants.opc_ifeq;
      }
      if ((type == FunctionExprent.FunctionType.AND || type == FunctionExprent.FunctionType.OR
          || type == FunctionExprent.FunctionType.XOR) && booleanOperands(function)) {
        // Non-short-circuit boolean arithmetic: one test after the operation, like a plain value.
        return CodeConstants.opc_ifeq;
      }
      if (function.getLstOperands().size() == 2) {
        VarType left = function.getLstOperands().get(0).getExprType();
        VarType right = function.getLstOperands().get(1).getExprType();
        if (left != null && right != null) {
          boolean refs = left.typeFamily == TypeFamily.OBJECT && right.typeFamily == TypeFamily.OBJECT;
          boolean ints = isIntegerFamily(left) && isIntegerFamily(right);
          // long/float/double compare through lcmp/fcmp and then branch on the int result.
          boolean wide = (left.typeFamily == TypeFamily.LONG && right.typeFamily == TypeFamily.LONG)
            || (left.typeFamily == TypeFamily.FLOAT && right.typeFamily == TypeFamily.FLOAT);
          switch (type) {
            case EQ:
              if (refs) return CodeConstants.opc_if_acmpne;
              if (ints) return CodeConstants.opc_if_icmpne;
              if (wide) return CodeConstants.opc_ifne;
              break;
            case NE:
              if (refs) return CodeConstants.opc_if_acmpeq;
              if (ints) return CodeConstants.opc_if_icmpeq;
              if (wide) return CodeConstants.opc_ifeq;
              break;
            case LT:
              if (ints) return CodeConstants.opc_if_icmpge;
              if (wide) return CodeConstants.opc_ifge;
              break;
            case GE:
              if (ints) return CodeConstants.opc_if_icmplt;
              if (wide) return CodeConstants.opc_iflt;
              break;
            case GT:
              if (ints) return CodeConstants.opc_if_icmple;
              if (wide) return CodeConstants.opc_ifle;
              break;
            case LE:
              if (ints) return CodeConstants.opc_if_icmpgt;
              if (wide) return CodeConstants.opc_ifgt;
              break;
          }
        }
      }
    }
    return isPlainBoolean(condition) ? CodeConstants.opc_ifeq : 0;
  }

  private static boolean isIntegerFamily(VarType type) {
    return type.typeFamily == TypeFamily.INTEGER || type.typeFamily == TypeFamily.BOOLEAN;
  }

  private static boolean booleanOperands(FunctionExprent function) {
    for (Exprent operand : function.getLstOperands()) {
      VarType type = operand.getExprType();
      if (type == null || type.typeFamily != TypeFamily.BOOLEAN) {
        return false;
      }
    }
    return !function.getLstOperands().isEmpty();
  }

  private static int complement(int opcode) {
    return switch (opcode) {
      case CodeConstants.opc_ifeq -> CodeConstants.opc_ifne;
      case CodeConstants.opc_ifne -> CodeConstants.opc_ifeq;
      case CodeConstants.opc_ifnull -> CodeConstants.opc_ifnonnull;
      case CodeConstants.opc_ifnonnull -> CodeConstants.opc_ifnull;
      case CodeConstants.opc_if_icmpeq -> CodeConstants.opc_if_icmpne;
      case CodeConstants.opc_if_icmpne -> CodeConstants.opc_if_icmpeq;
      case CodeConstants.opc_if_icmplt -> CodeConstants.opc_if_icmpge;
      case CodeConstants.opc_if_icmpge -> CodeConstants.opc_if_icmplt;
      case CodeConstants.opc_if_icmpgt -> CodeConstants.opc_if_icmple;
      case CodeConstants.opc_if_icmple -> CodeConstants.opc_if_icmpgt;
      case CodeConstants.opc_if_acmpeq -> CodeConstants.opc_if_acmpne;
      case CodeConstants.opc_if_acmpne -> CodeConstants.opc_if_acmpeq;
      case CodeConstants.opc_iflt -> CodeConstants.opc_ifge;
      case CodeConstants.opc_ifge -> CodeConstants.opc_iflt;
      case CodeConstants.opc_ifgt -> CodeConstants.opc_ifle;
      case CodeConstants.opc_ifle -> CodeConstants.opc_ifgt;
      default -> 0;
    };
  }

  private static boolean isNull(Exprent exprent) {
    return exprent instanceof ConstExprent constant && constant.isNull();
  }

  /** The value of a boolean constant, or null when the exprent is not one. */
  private static Boolean booleanConstant(Exprent exprent) {
    if (exprent instanceof ConstExprent constant && constant.getExprType() != null
        && constant.getExprType().typeFamily == TypeFamily.BOOLEAN
        && constant.getValue() instanceof Integer value) {
      return value != 0;
    }
    return null;
  }

  private static boolean isPlainBoolean(Exprent exprent) {
    return exprent instanceof InvocationExprent || exprent instanceof VarExprent
      || exprent instanceof FieldExprent || exprent instanceof ConstExprent;
  }

  private static boolean isConditional(int opcode) {
    return opcode >= CodeConstants.opc_ifeq && opcode <= CodeConstants.opc_if_acmpne
      || opcode == CodeConstants.opc_ifnull || opcode == CodeConstants.opc_ifnonnull;
  }

  public static boolean enabled() {
    return DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP);
  }

  /** For bisecting a suspect transform: {@code RT_OFF=name1,name2} turns these off. */
  /** The target's source line for the first instruction the exprent owns, or -1. */
  public static int sourceLine(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return -1;
    }
    return lineAt(method, exprent.bytecode.nextSetBit(0));
  }

  /** The target's source line for the instruction at the exprent's last offset, or -1. */
  public static int sourceLineEnd(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return -1;
    }
    return lineAt(method, exprent.bytecode.previousSetBit(Integer.MAX_VALUE));
  }

  /**
   * Whether the target's line table has an entry exactly at the expression's first instruction.
   * javac only marks lines where an AST node's position sits, so an argument that merely inherits
   * the enclosing statement's line has no entry of its own; a break there is layout the original
   * never had.
   */
  public static boolean lineStartsHere(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return false;
    }
    StructLineNumberTableAttribute lnt =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (lnt == null) {
      return false;
    }
    int offset = exprent.bytecode.nextSetBit(0);
    return lnt.findLineNumber(offset) != (offset <= 0 ? -1 : lnt.findLineNumber(offset - 1));
  }

  /** Whether the target's line table has an entry exactly at the expression's last instruction. */
  public static boolean lineStartsAtEnd(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return false;
    }
    StructLineNumberTableAttribute lnt =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (lnt == null) {
      return false;
    }
    int offset = exprent.bytecode.previousSetBit(Integer.MAX_VALUE);
    return lnt.findLineNumber(offset) != (offset <= 0 ? -1 : lnt.findLineNumber(offset - 1));
  }

  /** The first offset after the protected range of the handler at this offset, or -1. */
  public static int handlerExitOffset(int handlerOffset) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : HANDLER_ENDS.get(method);
    Integer end = ends == null ? null : ends.get(handlerOffset);
    return end == null ? -1 : end;
  }

  /** The target's source line for a bytecode offset, or -1. */
  public static int lineAtOffset(int offset) {
    StructMethod method = currentMethod();
    return method == null || offset < 0 ? -1 : lineAt(method, offset);
  }

  /** The greatest line the target gives an instruction strictly between two offsets, or -1. */
  public static int highestLineBetween(int from, int to) {
    StructMethod method = currentMethod();
    if (method == null || from < 0 || to <= from) {
      return -1;
    }
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return -1;
    }
    int[] raw = table.getRawData();
    int best = -1;
    for (int i = 0; i + 1 < raw.length; i += 2) {
      if (raw[i] > from && raw[i] < to) {
        best = Math.max(best, raw[i + 1]);
      }
    }
    return best;
  }

  /**
   * Whether the original wrote this catch clause on a line of its own. A try-with-resources'
   * synthetic close sits on the closing brace's line, so the greatest line between the block's
   * last exprent and the handler belongs to the closing brace. A brace written on the catch's
   * line puts that entry on the handler's line. A try without resources emits nothing there,
   * and the brace's line is not in the class file at all.
   */
  public static boolean catchOnNewLine(Statement previous, int handlerOffset, boolean resources) {
    if (!resources || previous == null || handlerOffset < 0) {
      return false;
    }
    int end = previous.getStartEndRange().end;
    int braceLine = Math.max(lineAtOffset(end), highestLineBetween(end, handlerOffset));
    int handlerLine = lineAtOffset(handlerOffset);
    return braceLine >= 0 && handlerLine > braceLine;
  }

  /**
   * Whether a boolean operator's right operand starts on a line of its own. Both operands' own
   * bitsets can cover only a short-circuit branch, laid on the line the whole expression ends
   * on, so the line the operand's text begins and ends on is read from its parts.
   */
  public static boolean newlineBetweenOperands(Exprent before, Exprent after) {
    if (!enabled()) {
      return false;
    }
    int end = -1;
    for (Exprent part : before.getAllExprents(true, false)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int line = lineAtOffset(part.bytecode.previousSetBit(Integer.MAX_VALUE));
      if (line > end) {
        end = line;
      }
    }
    if (end < 0) {
      end = sourceLineEnd(before);
    }
    // Only an operand whose own first instruction starts a line proves the source broke
    // before it: a later entry inside the operand may belong to a line the operand's text
    // began earlier (a chain broken before its first call, an argument on its own line).
    int first = -1;
    for (Exprent part : after.getAllExprents(true, true)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int offset = part.bytecode.nextSetBit(0);
      if (first < 0 || offset < first) {
        first = offset;
      }
    }
    if (first < 0) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    int start = lineAtOffset(first);
    boolean startsLine = table.findLineNumber(first) != (first <= 0 ? -1 : table.findLineNumber(first - 1));
    return startsLine && end >= 0 && start >= 0 && start > end;
  }

  /**
   * Whether a boolean operand begins the target's next line, judging by the operand's own first
   * instruction. javac enters an invocation's line at its invoke, after its arguments, so an
   * operand that starts with a call has no entry where its text starts; the call's own offset is
   * the line the operand was written on.
   */
  public static boolean newlineBeforeOperand(Exprent before, Exprent after) {
    if (!enabled() || after == null || !(after instanceof InvocationExprent)) {
      return newlineBetweenOperands(before, after);
    }
    int first = after.bytecode == null || after.bytecode.isEmpty()
      ? -1 : after.bytecode.nextSetBit(0);
    if (first < 0) {
      return newlineBetweenOperands(before, after);
    }
    int end = -1;
    for (Exprent part : before.getAllExprents(true, false)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int line = lineAtOffset(part.bytecode.previousSetBit(Integer.MAX_VALUE));
      if (line > end) {
        end = line;
      }
    }
    if (end < 0) {
      end = sourceLineEnd(before);
    }
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    boolean startsLine = table.findLineNumber(first) != (first <= 0 ? -1 : table.findLineNumber(first - 1));
    int start = lineAtOffset(first);
    return startsLine && end >= 0 && start >= 0 && start > end;
  }

  /** Whether the original source started the second expression on a later line than the first ended. */
  public static boolean newlineBetween(Exprent before, Exprent after) {
    int end = sourceLineEnd(before);
    int start = sourceLine(after);
    return end >= 0 && start >= 0 && start > end;
  }

  /** The target's source line for a method's first instruction. */
  public static int methodLine(StructMethod method) {
    if (method == null) {
      return -1;
    }
    return lineAt(method, 0);
  }

  public static int lineAt(StructMethod method, int offset) {
    StructLineNumberTableAttribute lnt =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    return lnt == null ? -1 : lnt.findLineNumber(offset);
  }

  /**
   * The start offset of the last instruction an exprent maps, or -1. An exprent's bitset also
   * covers the bytes of its instructions, so only the registered starts count.
   */
  public static int lastInstructionStart(BitSet bytecode) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    if (ends == null || bytecode == null) {
      return -1;
    }
    for (int offset = bytecode.previousSetBit(Integer.MAX_VALUE); offset >= 0;
         offset = bytecode.previousSetBit(offset - 1)) {
      if (ends.containsKey(offset)) {
        return offset;
      }
    }
    return -1;
  }

  /** Whether the instruction right after {@code offset} stores or discards the call's value. */
  public static boolean valueConsumedAfter(int offset) {
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    BitSet sinks = VALUE_SINKS.get(method);
    Integer next = ends == null ? null : ends.get(offset);
    return next != null && sinks != null && sinks.get(next);
  }

  /** The target's first exact line-table entry strictly after {@code offset}, or -1. */
  public static int entryOffsetAfter(int offset) {
    StructMethod method = currentMethod();
    if (method == null) {
      return -1;
    }
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return -1;
    }
    int[] raw = table.getRawData();
    int best = -1;
    for (int i = 0; i + 1 < raw.length; i += 2) {
      if (raw[i] > offset && (best < 0 || raw[i] < best)) {
        best = raw[i];
      }
    }
    return best;
  }

  /** True when the target's table starts a source line at this bytecode offset. */
  public static boolean lineStartsAt(int offset) {
    StructMethod method = currentMethod();
    if (method == null || offset <= 0) {
      return true;
    }
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return true;
    }
    int here = table.findLineNumber(offset);
    int before = table.findLineNumber(offset - 1);
    return here < 0 || before < 0 || here != before;
  }

  public static boolean selector(String name) {
    if (!enabled()) {
      return false;
    }
    String disabled = System.getenv("RT_OFF");
    return disabled == null || !disabled.contains(name);
  }

  /**
   * True when the two return expressions come from distinct return instructions in the target.
   * A return-position ternary shares one return after a join; an if/else has one per arm.
   */
  public static boolean hasDistinctReturnInstructions(Exprent first, Exprent second) {
    if (!selector("ternary")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    int a = returnOffset(seq, first);
    int b = returnOffset(seq, second);
    return a >= 0 && b >= 0 && a != b;
  }

  /**
   * True when the target's increment instruction follows the assignment's store, so the source
   * wrote the increment as a later statement ({@code x = y; y++;}) and the printer's merge into
   * {@code x = y++} would move the iinc in front of the store.
   */
  public static boolean incrementAfterStore(Exprent assignment, Exprent increment) {
    if (!selector("ppistore")) {
      return false;
    }
    BitSet store = assignment.bytecode;
    BitSet inc = increment.bytecode;
    if (store == null || store.isEmpty() || inc == null || inc.isEmpty()) {
      return false;
    }
    int incOffset = inc.nextSetBit(0);
    int storeOffset = store.length() - 1;
    return incOffset >= 0 && incOffset >= storeOffset;
  }

  /**
   * True when the target kept a duplicate of the left-hand side next to the matching operand:
   * {@code this.f += e} compiles as {@code aload_0; dup; getfield f; ...; putfield f}, while
   * {@code this.f = this.f + e} loads the field twice.
   */
  public static boolean isCompoundTarget(Exprent left, Exprent matching) {
    if (!selector("compound")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    BitSet offsets = matching.bytecode;
    if (seq == null || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer index = seq.offsetToIndex().get(offsets.nextSetBit(0));
    if (index == null) {
      return false;
    }
    int opcode = seq.getInstr(index).opcode;
    if (left instanceof FieldExprent) {
      if (opcode != CodeConstants.opc_getfield && opcode != CodeConstants.opc_getstatic) {
        return false;
      }
      return index > 0 && isDup(seq.getInstr(index - 1).opcode);
    }
    if (left instanceof VarExprent) {
      if (!isLoad(opcode)) {
        return false;
      }
      return index + 1 < seq.length() && isDup(seq.getInstr(index + 1).opcode);
    }
    return false;
  }

  private static boolean isDup(int opcode) {
    return opcode >= CodeConstants.opc_dup && opcode <= CodeConstants.opc_dup2_x2;
  }

  /** True when the target emitted a checkcast inside this expression's bytecode range. */
  public static boolean forceCast(Exprent exprent) {
    if (!selector("cast")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    return hasOpcode(seq, exprent, CodeConstants.opc_checkcast);
  }

  /**
   * The condition to print for {@code if (C) { return; } body} when the target's instructions and
   * line table prove the source wrote the exit first. The early return sits between the condition
   * and the body in the target's instruction sequence; when the printed condition is the negated
   * mirror rather than a NOT, the line table must also put the exit's line before the body's.
   * Returns null when the shape is the mirror or the target cannot prove the direction.
   */
  public static Exprent guardCondition(Exprent head, Statement body) {
    if (!selector("guardprint") || !(head instanceof IfExprent ie)) {
      return null;
    }
    Exprent condition = ie.getCondition();
    StructMethod method = currentMethod();
    if (method == null) {
      return null;
    }
    BitSet returns = VOID_RETURNS.get(method);
    BitSet offsets = head.bytecode;
    int bodyStart = firstOffset(body);
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    if (returns == null || returns.isEmpty() || offsets == null || offsets.isEmpty() || ends == null) {
      return null;
    }
    int lastStart = -1;
    int lastEnd = -1;
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end != null && offset > lastStart) {
        lastStart = offset;
        lastEnd = end;
      }
    }
    if (!(lastEnd >= 0 && lastEnd < bodyStart && returns.get(lastEnd))) {
      return null;
    }
    if (condition instanceof FunctionExprent function && function.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT) {
      markGuardExit(method, lastEnd);
      return function.getLstOperands().get(0);
    }
    // A negated condition of the printer's own making: only the target's line table can say whether
    // the source wrote the exit first or the body first.
    StructLineNumberTableAttribute table = method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return null;
    }
    int exitLine = table.findLineNumber(lastEnd);
    int bodyLine = table.findLineNumber(bodyStart);
    if (exitLine < 0 || bodyLine < 0 || exitLine >= bodyLine) {
      return null;
    }
    markGuardExit(method, lastEnd);
    return negateCondition(condition);
  }

  /**
   * True when the head's last branch targets the then-arm's first instruction: the source wrote
   * {@code if (!C) { rest } else { body }} and javac branched to the else arm, while the guard form
   * {@code if (C) { body; return; } rest} branches past the if to the rest.
   */
  public static boolean branchesToBody(Exprent head, Statement body) {
    StructMethod method = currentMethod();
    if (method == null || head == null || head.bytecode == null) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    if (ends == null || targets == null) {
      return false;
    }
    int bodyStart = firstOffset(body);
    if (bodyStart < 0) {
      return false;
    }
    int lastStart = -1;
    int lastTarget = -1;
    for (int offset = head.bytecode.nextSetBit(0); offset >= 0; offset = head.bytecode.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end != null && targets.containsKey(end) && offset > lastStart) {
        lastStart = offset;
        lastTarget = targets.get(end);
      }
    }
    return lastStart >= 0 && lastTarget == bodyStart;
  }

  /** True when a local variable's scope starts inside the statement's instruction range. */
  public static boolean declaresLocal(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null) {
      return false;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    int start = firstOffset(stat);
    int end = lastEnd(stat);
    if (start < 0 || end < 0) {
      return false;
    }
    return table.getRange(start, end)
      .anyMatch(v -> v.getStart() >= start && v.getStart() <= end);
  }

  private static int lastEnd(Statement stat) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    if (ends == null) {
      return -1;
    }
    int max = -1;
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    queue.add(stat);
    while (!queue.isEmpty()) {
      Statement cur = queue.poll();
      List<Exprent> exprents = cur.getExprents();
      if (exprents != null) {
        for (Exprent exprent : exprents) {
          for (Exprent inner : exprent.getAllExprents(true, true)) {
            BitSet bits = inner.bytecode;
            if (bits == null) {
              continue;
            }
            for (int off = bits.nextSetBit(0); off >= 0; off = bits.nextSetBit(off + 1)) {
              Integer end = ends.get(off);
              if (end != null && end > max) {
                max = end;
              }
            }
          }
        }
      }
      queue.addAll(cur.getStats());
    }
    return max;
  }

  /**
   * True when the condition's branches target both the exit block and the body, and the exit sits
   * before the body: the source wrote the guard inside {@code while (true)}. A synthesized `&&`
   * carries no offsets of its own, so each operand's branch is the one starting where the operand
   * ends.
   */
  public static boolean guardBranches(Exprent condition, Statement exit, Statement body) {
    StructMethod method = currentMethod();
    if (method == null || condition == null || exit == null || body == null
        || !(condition instanceof FunctionExprent function)
        || function.getFuncType() != FunctionExprent.FunctionType.BOOLEAN_AND
        || function.getLstOperands().size() != 2) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> branchStarts = BRANCH_STARTS.get(method);
    if (ends == null || branchStarts == null) {
      return false;
    }
    int exitStart = firstOffset(exit);
    int bodyStart = firstOffset(body);
    if (exitStart < 0 || bodyStart < 0 || exitStart >= bodyStart) {
      return false;
    }
    boolean toExit = false;
    boolean toBody = false;
    for (Exprent operand : function.getLstOperands()) {
      Integer target = ownBranchTarget(operand, branchStarts);
      if (target == null) {
        return false;
      }
      if (target == exitStart) {
        toExit = true;
      } else if (target == bodyStart) {
        toBody = true;
      }
    }
    return toExit && toBody;
  }

  private static Integer ownBranchTarget(Exprent operand, java.util.Map<Integer, Integer> branchStarts) {
    BitSet bits = operand.bytecode;
    if (bits == null) {
      return null;
    }
    Integer found = null;
    for (int off = bits.nextSetBit(0); off >= 0; off = bits.nextSetBit(off + 1)) {
      Integer target = branchStarts.get(off);
      if (target != null) {
        found = target;
      }
    }
    return found;
  }

  /**
   * The strict guard layout: every conditional branch of the head targets one void return that is
   * exactly one instruction before the body, and the head block's last instruction is a goto to
   * that body (the `goto body / return / body:` layout the source's early-return guard compiles to).
   */
  public static boolean guardReturnLayout(Statement headBlock, Exprent head, Statement arm) {
    StructMethod method = currentMethod();
    if (method == null || headBlock == null || head == null || head.bytecode == null || arm == null) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    BitSet returns = VOID_RETURNS.get(method);
    if (ends == null || targets == null || returns == null) {
      return false;
    }
    int bodyStart = firstOffset(arm);
    if (bodyStart < 0) {
      return false;
    }
    Integer common = null;
    for (int offset = head.bytecode.nextSetBit(0); offset >= 0; offset = head.bytecode.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end == null) {
        continue;
      }
      Integer target = targets.get(end);
      if (target == null) {
        continue;
      }
      if (common == null) {
        common = target;
      } else if (!common.equals(target)) {
        return false;
      }
    }
    if (common == null || !returns.get(common) || common + 1 != bodyStart) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (gotos == null) {
      return false;
    }
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getValue() == bodyStart && ends.get(entry.getKey()) != null
          && ends.get(entry.getKey()) == common) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when the loop's condition was written inside the body as a break guard: the condition's
   * own conditional branch targets the exit rather than the body's start, and an unconditional
   * goto inside the body jumps back to that start -- while (true) { ... if (!cond) break; }.
   */
  public static boolean loopGuardInsideBody(Exprent condition, Statement body) {
    StructMethod method = currentMethod();
    if (method == null || condition == null || condition.bytecode == null || body == null) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> branchStarts = BRANCH_STARTS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (ends == null || branchStarts == null || gotos == null) {
      return false;
    }
    int bodyStart = firstOffset(body);
    if (bodyStart < 0) {
      return false;
    }
    // The condition's own branch may be a set bit of its bytecode, or start exactly where the
    // last condition instruction ends. BRANCH_STARTS is the map keyed by the branch's start.
    Integer conditionTarget = ownBranchTarget(condition, branchStarts);
    if (conditionTarget == null) {
      int lastBit = -1;
      for (int offset = condition.bytecode.nextSetBit(0); offset >= 0; offset = condition.bytecode.nextSetBit(offset + 1)) {
        if (ends.containsKey(offset) && offset > lastBit) {
          lastBit = offset;
        }
      }
      Integer branchStart = lastBit < 0 ? null : ends.get(lastBit);
      conditionTarget = branchStart == null ? null : branchStarts.get(branchStart);
    }
    // A do-while's conditional back edge targets the body's start; a break guard targets the exit.
    if (conditionTarget == null || conditionTarget == bodyStart) {
      return false;
    }
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getValue() == bodyStart && entry.getKey() > bodyStart) {
        return true;
      }
    }
    return false;
  }

  /**
   * The remainder-loop layout: the condition's branch targets the body, the tail's statements fill
   * the exit block between the condition and the body, and the back edge jumps behind the tail.
   * The source wrote {@code while (true) { if (!cond) { tail } body }}.
   */
  public static boolean guardExitBeforeBody(Exprent condition, Statement tailFirst, Statement tailLast, Statement body) {
    StructMethod method = currentMethod();
    if (method == null || condition == null || condition.bytecode == null || tailFirst == null
        || tailLast == null || body == null) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> branchStarts = BRANCH_STARTS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (ends == null || branchStarts == null || gotos == null) {
      return false;
    }
    int bodyStart = firstOffset(body);
    int tailStart = firstOffset(tailFirst);
    int tailEnd = lastEnd(tailLast);
    if (bodyStart < 0 || tailStart < 0 || tailEnd < 0 || tailEnd != bodyStart) {
      return false;
    }
    Integer conditionTarget = ownBranchTarget(condition, branchStarts);
    if (conditionTarget == null) {
      int lastBit = -1;
      for (int offset = condition.bytecode.nextSetBit(0); offset >= 0; offset = condition.bytecode.nextSetBit(offset + 1)) {
        if (ends.containsKey(offset) && offset > lastBit) {
          lastBit = offset;
        }
      }
      Integer branchStart = lastBit < 0 ? null : ends.get(lastBit);
      conditionTarget = branchStart == null ? null : branchStarts.get(branchStart);
    }
    if (conditionTarget == null || conditionTarget != bodyStart) {
      return false;
    }
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getKey() > tailEnd && entry.getValue() <= tailStart) {
        return true;
      }
    }
    return false;
  }

  /** True when the arm's last instruction is a goto that lands beyond the tail's end. */
  public static boolean armJumpsPast(Statement arm, Statement tail) {
    StructMethod method = currentMethod();
    if (method == null || arm == null || tail == null) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (ends == null || gotos == null) {
      return false;
    }
    int tailEnd = lastEnd(tail);
    if (tailEnd < 0) {
      return false;
    }
    int lastStart = lastStart(arm);
    if (lastStart < 0) {
      return false;
    }
    Integer target = gotos.get(lastStart);
    return target != null && target > tailEnd;
  }

  private static int lastStart(Statement stat) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    if (ends == null) {
      return -1;
    }
    int max = -1;
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    queue.add(stat);
    while (!queue.isEmpty()) {
      Statement cur = queue.poll();
      List<Exprent> exprents = cur.getExprents();
      if (exprents != null) {
        for (Exprent exprent : exprents) {
          for (Exprent inner : exprent.getAllExprents(true, true)) {
            BitSet bits = inner.bytecode;
            if (bits == null) {
              continue;
            }
            for (int off = bits.nextSetBit(0); off >= 0; off = bits.nextSetBit(off + 1)) {
              if (ends.containsKey(off) && off > max) {
                max = off;
              }
            }
          }
        }
      }
      queue.addAll(cur.getStats());
    }
    return max;
  }

  private static void markGuardExit(StructMethod method, int offset) {
    CONSUMED_GUARD_EXITS.computeIfAbsent(method, key -> java.util.concurrent.ConcurrentHashMap.newKeySet()).add(offset);
  }

  /**
   * True when this statement is a single exit already printed as a guard: the guard made the rest of
   * the sequence unconditional, so the same return instruction must not be printed again.
   */
  public static boolean isConsumedGuardExit(Statement statement) {
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Set<Integer> consumed = CONSUMED_GUARD_EXITS.get(method);
    if (consumed == null || consumed.isEmpty()) {
      return false;
    }
    List<Exprent> exprents = statement.getExprents();
    if (exprents == null || exprents.size() != 1 || !(exprents.get(0) instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit)) {
      return false;
    }
    if (exit.getExitType() != org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
        && exit.getExitType() != org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.THROW) {
      return false;
    }
    BitSet offsets = exit.bytecode;
    if (offsets == null) {
      return false;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      if (consumed.contains(offset)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The logical negation of a condition as an expression to print. Comparisons flip their operator
   * (except float/double, where NaN breaks the equivalence), boolean junctions swap under De Morgan,
   * and anything else keeps a {@code !}.
   */
  public static Exprent negateCondition(Exprent condition) {
    if (condition instanceof FunctionExprent function) {
      FunctionExprent.FunctionType type = function.getFuncType();
      java.util.List<Exprent> operands = function.getLstOperands();
      if (type == FunctionExprent.FunctionType.BOOL_NOT && operands.size() == 1) {
        return operands.get(0).copy();
      }
      if ((type == FunctionExprent.FunctionType.BOOLEAN_AND || type == FunctionExprent.FunctionType.BOOLEAN_OR)
          && !operands.isEmpty()) {
        FunctionExprent.FunctionType flipped = type == FunctionExprent.FunctionType.BOOLEAN_AND
          ? FunctionExprent.FunctionType.BOOLEAN_OR : FunctionExprent.FunctionType.BOOLEAN_AND;
        java.util.List<Exprent> negated = new java.util.ArrayList<>();
        for (Exprent operand : operands) {
          negated.add(negateCondition(operand));
        }
        return new FunctionExprent(flipped, negated, function.bytecode);
      }
      FunctionExprent.FunctionType opposite = oppositeComparison(type);
      if (opposite != null && operands.size() == 2 && comparableWithoutNaN(operands)) {
        java.util.List<Exprent> flipped = new java.util.ArrayList<>();
        flipped.add(operands.get(0).copy());
        flipped.add(operands.get(1).copy());
        return new FunctionExprent(opposite, flipped, function.bytecode);
      }
    }
    return new FunctionExprent(FunctionExprent.FunctionType.BOOL_NOT, condition.copy(), condition.bytecode);
  }

  private static FunctionExprent.FunctionType oppositeComparison(FunctionExprent.FunctionType type) {
    return switch (type) {
      case EQ -> FunctionExprent.FunctionType.NE;
      case NE -> FunctionExprent.FunctionType.EQ;
      case LT -> FunctionExprent.FunctionType.GE;
      case GE -> FunctionExprent.FunctionType.LT;
      case GT -> FunctionExprent.FunctionType.LE;
      case LE -> FunctionExprent.FunctionType.GT;
      default -> null;
    };
  }

  private static boolean comparableWithoutNaN(java.util.List<Exprent> operands) {
    VarType left = operands.get(0).getExprType();
    VarType right = operands.get(1).getExprType();
    return left != null && right != null
      && left.typeFamily != TypeFamily.FLOAT && left.typeFamily != TypeFamily.DOUBLE
      && right.typeFamily != TypeFamily.FLOAT && right.typeFamily != TypeFamily.DOUBLE;
  }

  /**
   * True when the target returns before the body: the source was
   * {@code if (!C) { return value; } body} rather than {@code if (C) { body } return value;}.
   */
  public static boolean returnGuard(Statement body, Statement tail) {
    if (!selector("retguard")) {
      return false;
    }
    int bodyStart = firstOffset(body);
    int tailStart = firstOffset(tail);
    if (bodyStart < 0 || tailStart < 0) {
      return false;
    }
    // The original's line table says which shape it wrote: a guard puts the exit's line before the
    // body's, while `if (C) { body } exit;` puts it after, whatever order the blocks compile in.
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table != null) {
      int bodyLine = table.findLineNumber(bodyStart);
      int tailLine = table.findLineNumber(tailStart);
      if (System.getenv("NEUROFLOWER_RETGUARD_DEBUG") != null) {
        System.err.println("retguard " + method.getName() + " bodyStart " + bodyStart + " line " + bodyLine
          + " tailStart " + tailStart + " line " + tailLine);
      }
      if (bodyLine >= 0 && tailLine >= 0) {
        return tailLine < bodyLine;
      }
    }
    return tailStart < bodyStart;
  }

  /**
   * True when the target's table puts the exit's line after the following statement's, so the
   * source wrote {@code body; exit;} rather than the guard the bytecode's block order suggests.
   */
  public static boolean exitAfterBody(Statement exitStatement, Statement body) {
    if (!selector("exitlast")) {
      return false;
    }
    int exitStart = firstOffset(exitStatement);
    int bodyStart = firstOffset(body);
    if (exitStart < 0 || bodyStart < 0) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    int exitLine = table.findLineNumber(exitStart);
    int bodyLine = table.findLineNumber(bodyStart);
    if (System.getenv("NEUROFLOWER_RETGUARD_DEBUG") != null) {
      System.err.println("exitlast " + method.getName() + " exit " + exitStart + "@" + exitLine
        + " body " + bodyStart + "@" + bodyLine);
    }
    return exitLine >= 0 && bodyLine >= 0 && exitLine > bodyLine;
  }

  /**
   * True when the target compiled this if as {@code if (C) continue;} — the condition branches to
   * the body and the fall-through jumps back to the loop head. The printer's mirror is
   * {@code if (!C) { body }}, which compiles to the opposite branch with no goto.
   */
  public static boolean printContinueGuard(Exprent head, Statement sequence) {
    if (!selector("continueguard")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    BitSet offsets = head.bytecode;
    if (guards == null || guards.isEmpty() || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer target = guards.get(offsets.length());
    if (target == null) {
      return false;
    }
    Statement loop = sequence.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    if (!isContinueTarget(doStatement, target)) {
      return false;
    }
    // The target's table must put the continue's line before the body's first line.
    java.util.Map<Integer, int[]> sites = CONTINUE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(offsets.length());
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (site != null && table != null) {
      int continueLine = table.findLineNumber(site[0]);
      int bodyLine = table.findLineNumber(site[1]);
      if (continueLine >= 0 && bodyLine >= 0 && continueLine >= bodyLine) {
        return false;
      }
    }
    return true;
  }

  /**
   * Whether a local declared in this statement runs to its end. Such a statement's scope closes at
   * the jump that follows it; a {@code continue} printed after the local's last use would close the
   * scope after that jump instead of before it, and the local's table range would grow. A local
   * declared in a nested block ends earlier and is unaffected.
   */
  public static boolean declaresLocalToEnd(Statement statement) {
    StructMethod method = currentMethod();
    if (method == null || statement == null) {
      return false;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    int start = firstOffset(statement);
    int end = lastEnd(statement);
    if (start < 0 || end < 0) {
      return false;
    }
    // The table's own range filter wants both ends, but the scope ends at the jump past the last
    // instruction, so bound the start here and compare the end directly.
    return table.getRange(start, Integer.MAX_VALUE)
      .anyMatch(v -> v.getStart() <= end && v.getEnd() >= end);
  }

  /**
   * The mirror of {@link #printContinueGuard} for an else arm: {@code if (C) { ...; continue; } rest}
   * where the decompiler kept {@code rest} as the else arm. The branch jumps over the then arm and
   * the goto ending that arm is the continue. The caller proves the arm is the rest of the loop
   * body, so hoisting it keeps every scope's end where it was and no local can change slot.
   */
  public static boolean printContinueElse(Exprent head, Statement sequence) {
    if (!selector("continueguard")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_ELSE_GUARDS.get(method);
    BitSet offsets = head.bytecode;
    if (guards == null || guards.isEmpty() || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer target = guards.get(offsets.length());
    if (target == null) {
      return false;
    }
    Statement loop = sequence.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    // Only a jump to the loop head counts. An ordinary if/else joins after its else arm, which
    // is still inside the loop, so the loop's extent alone cannot tell the two apart.
    if (!isLoopHeadTarget(doStatement, target)) {
      return false;
    }
    // The source wrote `continue;` on a line of its own, so the table starts an entry at its goto
    // and puts it before the else arm's first line. An if/else's closing jump inherits the line of
    // the arm before it and starts nothing; when the table has no entry at the goto, the extra
    // `continue` line would change the table and the arm is an ordinary else.
    java.util.Map<Integer, int[]> sites = CONTINUE_ELSE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(offsets.length());
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (site == null || table == null || !startsLine(table, site[0])) {
      return false;
    }
    int continueLine = table.findLineNumber(site[0]);
    int bodyLine = table.findLineNumber(site[1]);
    if (continueLine >= 0 && bodyLine >= 0 && continueLine >= bodyLine) {
      return false;
    }
    return true;
  }

  /** Whether the table starts an entry at this exact offset: a statement on a new line began there. */
  private static boolean startsLine(StructLineNumberTableAttribute table, int offset) {
    int[] raw = table.getRawData();
    for (int i = 0; i + 1 < raw.length; i += 2) {
      if (raw[i] == offset) {
        return true;
      }
    }
    return false;
  }

  /** Whether {@code target} is where a {@code continue} of this loop lands, without the loop's extent. */
  private static boolean isLoopHeadTarget(org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop, int target) {
    // A continue jumps to the loop's head, which is built before the body's first statement.
    int bodyStart = firstOffset(loop.getFirst());
    if (bodyStart >= 0 && target >= 0 && target < bodyStart) {
      return true;
    }
    Exprent head = switch (loop.getLooptype()) {
      case WHILE, DO_WHILE -> loop.getConditionExprent();
      case FOR, FOR_EACH -> loop.getIncExprent() != null ? loop.getIncExprent() : loop.getConditionExprent();
      default -> null;
    };
    if (head != null && head.bytecode != null && !head.bytecode.isEmpty()) {
      // The loop top may load a local the condition exprent does not own, so the target can sit
      // a short load before the exprent's first byte.
      int start = head.bytecode.nextSetBit(0);
      if (target <= start && target >= start - 3) {
        return true;
      }
      // An array for-each keeps its increment after the body; the exprent owns that bytecode.
      Exprent inc = loop.getIncExprent();
      if (inc != null && inc.bytecode != null && inc.bytecode.get(target)) {
        return true;
      }
    }
    return false;
  }

  /** The instruction a {@code continue} in this loop jumps to. */
  private static boolean isContinueTarget(org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop, int target) {
    // A continue jumps to the loop's head, which is built before the body's first statement. The
    // condition's own bytecode may not cover the receiver chain, so compare with the body start.
    int bodyStart = firstOffset(loop.getFirst());
    if (bodyStart >= 0 && target >= 0 && target < bodyStart) {
      return true;
    }
    Exprent head = switch (loop.getLooptype()) {
      case WHILE, DO_WHILE -> loop.getConditionExprent();
      case FOR, FOR_EACH -> loop.getIncExprent() != null ? loop.getIncExprent() : loop.getConditionExprent();
      default -> null;
    };
    if (head != null && head.bytecode != null && !head.bytecode.isEmpty()) {
      // The loop top may load a local the condition exprent does not own, so the target can sit
      // a short load before the exprent's first byte.
      int start = head.bytecode.nextSetBit(0);
      if (target <= start && target >= start - 3) {
        return true;
      }
      // An array for-each keeps its increment after the body; the exprent owns that bytecode.
      Exprent inc = loop.getIncExprent();
      if (inc != null && inc.bytecode != null && inc.bytecode.get(target)) {
        return true;
      }
    }
    // A for-each continue jumps to the compiler's hasNext block and a for's to the increment; both
    // live inside the loop but are not owned by the iterable or condition exprent.
    if (loop.getLooptype() == org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement.Type.FOR_EACH) {
      // A for-each continue jumps into the compiler's hasNext block, which sits before the first
      // instruction any exprent of the loop covers.
      return target >= 0 && bodyStart >= 0 && target < bodyStart;
    }
    int min = firstOffset(loop);
    int max = lastOffset(loop);
    return min >= 0 && max >= min && target >= min && target <= max;
  }

  /** Last target offset covered by a statement, or -1. */
  public static int lastOffset(Statement statement) {
    int max = -1;
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          BitSet bits = inner.bytecode;
          if (bits != null && !bits.isEmpty()) {
            int offset = bits.length() - 1;
            if (offset > max) {
              max = offset;
            }
          }
        }
      }
    } else {
      for (Statement child : statement.getStats()) {
        int offset = lastOffset(child);
        if (offset > max) {
          max = offset;
        }
      }
    }
    return max;
  }

  /** First target offset covered by a statement, or -1. */
  public static int firstOffset(Statement statement) {
    int min = -1;
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        // Wrappers such as yield carry no offsets of their own; the expression they hold does.
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          BitSet bits = inner.bytecode;
          if (bits != null && !bits.isEmpty()) {
            int offset = bits.nextSetBit(0);
            if (min < 0 || offset < min) {
              min = offset;
            }
          }
        }
      }
    } else {
      for (Statement child : statement.getStats()) {
        int offset = firstOffset(child);
        if (offset >= 0 && (min < 0 || offset < min)) {
          min = offset;
        }
      }
    }
    return min;
  }

  /** True when the target loads this local into the return, i.e. the source kept the variable. */
  public static boolean targetReturnUsesLocal(Exprent exit, int var) {
    if (!selector("returnlocal")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    int ret = returnOffset(seq, exit);
    Integer index = ret < 0 ? null : seq.offsetToIndex().get(ret);
    if (index == null || index < 2) {
      return false;
    }
    Instruction load = seq.getInstr(index - 1);
    Instruction store = seq.getInstr(index - 2);
    return isLoad(load.opcode) && isStore(store.opcode)
      && variableIndex(load) == var && variableIndex(store) == var;
  }

  private static boolean isLoad(int opcode) {
    return opcode >= CodeConstants.opc_iload && opcode <= CodeConstants.opc_aload
      || opcode >= CodeConstants.opc_iload_0 && opcode <= CodeConstants.opc_aload_3;
  }

  private static boolean isStore(int opcode) {
    return opcode >= CodeConstants.opc_istore && opcode <= CodeConstants.opc_astore
      || opcode >= CodeConstants.opc_istore_0 && opcode <= CodeConstants.opc_astore_3;
  }

  private static int variableIndex(Instruction instr) {
    if (instr.opcode >= CodeConstants.opc_iload && instr.opcode <= CodeConstants.opc_aload
      || instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore) {
      return instr.operand(0);
    }
    if (instr.opcode >= CodeConstants.opc_iload_0 && instr.opcode <= CodeConstants.opc_aload_3) {
      return (instr.opcode - CodeConstants.opc_iload_0) % 4;
    }
    return (instr.opcode - CodeConstants.opc_istore_0) % 4;
  }

  /**
   * The start/end pairs of the target's scopes for a local slot with this name, in order. Two
   * entries mean the source declared the name twice in disjoint blocks.
   */
  public static java.util.List<int[]> localScopes(int index, String name) {
    StructMethod method = currentMethod();
    if (method == null) {
      return java.util.List.of();
    }
    org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute table =
      method.getAttribute(org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return java.util.List.of();
    }
    java.util.List<int[]> out = new java.util.ArrayList<>();
    for (org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable var
        : table.matchingVars(index).toList()) {
      if (name == null || !name.equals(var.getName())) {
        continue;
      }
      out.add(new int[]{var.getStart(), var.getEnd()});
    }
    out.sort(java.util.Comparator.comparingInt(a -> a[0]));
    return out;
  }

  public static StructMethod currentMethod() {
    StructMethod method = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    if (method != null) {
      return method;
    }
    MethodWrapper wrapper = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    return wrapper == null ? null : wrapper.methodStruct;
  }

  private static boolean hasOpcode(FullInstructionSequence seq, Exprent exprent, int wanted) {
    BitSet offsets = exprent.bytecode;
    if (offsets == null) {
      return false;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer index = seq.offsetToIndex().get(offset);
      if (index != null && seq.getInstr(index).opcode == wanted) {
        return true;
      }
    }
    return false;
  }

  private static int returnOffset(FullInstructionSequence seq, Exprent exprent) {
    BitSet offsets = exprent.bytecode;
    if (offsets == null) {
      return -1;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer index = seq.offsetToIndex().get(offset);
      if (index == null) {
        continue;
      }
      int opcode = seq.getInstr(index).opcode;
      if (opcode >= CodeConstants.opc_ireturn && opcode <= CodeConstants.opc_return) {
        return offset;
      }
    }
    return -1;
  }
}

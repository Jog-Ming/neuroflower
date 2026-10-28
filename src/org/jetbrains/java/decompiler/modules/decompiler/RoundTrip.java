package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ArrayExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
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
  /** A statement whose trailing jump an enclosing print has taken over (an else's implicit exit). */
  private static final ThreadLocal<Statement> SUPPRESSED_JUMP = new ThreadLocal<>();
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
  /** For each switch instruction (by start offset): its default target, then its keyed targets. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, int[]>> SWITCH_TARGETS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Offsets just past an inlined copy of a finally body, per method. */
  private static final java.util.Map<StructMethod, java.util.Set<Integer>> FINALLY_COPY_ENDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** The method's last instruction start offset. */
  private static final java.util.Map<StructMethod, Integer> LAST_INSTRUCTION = new java.util.concurrent.ConcurrentHashMap<>();
  /** Slot stored immediately before the load a value return reads, by the return's start offset. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> RETURN_STORES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Instructions that store or discard the stack's value: a call's result ends its statement here. */
  private static final java.util.Map<StructMethod, BitSet> VALUE_SINKS = new java.util.concurrent.ConcurrentHashMap<>();
  /** `dup; store N`: the duplicated value is the one the local N receives, keyed by the dup's start. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> DUP_STORES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Start offsets of every store to a slot, keyed by the slot. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, BitSet>> STORE_SITES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Start offsets of every load of a slot, keyed by the slot. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, BitSet>> LOAD_SITES = new java.util.concurrent.ConcurrentHashMap<>();
  /** The slot a store at this start offset writes. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> STORE_SLOTS = new java.util.concurrent.ConcurrentHashMap<>();

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
    java.util.Map<Integer, int[]> switches = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> branchStarts = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> dupStores = new java.util.HashMap<>();
    java.util.Map<Integer, BitSet> storeSites = new java.util.HashMap<>();
    java.util.Map<Integer, BitSet> loadSites = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> storeSlots = new java.util.HashMap<>();
    java.util.List<int[]> finallyCopies = new java.util.ArrayList<>();
    for (int i = 0; i < seq.length(); i++) {
      Instruction instr = seq.getInstr(i);
      ends.put(instr.startOffset, instr.startOffset + instr.length);
      if (instr.opcode >= CodeConstants.opc_iload && instr.opcode <= CodeConstants.opc_aload) {
        loadSites.computeIfAbsent(instr.operand(0), k -> new BitSet()).set(instr.startOffset);
      }
      if (instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore) {
        storeSites.computeIfAbsent(instr.operand(0), k -> new BitSet()).set(instr.startOffset);
        storeSlots.put(instr.startOffset, instr.operand(0));
        // `dup; store N`: the duplicate on the stack and the local N are the same value version,
        // so the store's own value is also the value the source assigned to N.
        if (i > 0) {
          int prev = seq.getInstr(i - 1).opcode;
          if (prev == CodeConstants.opc_dup || prev == CodeConstants.opc_dup2) {
            dupStores.put(instr.startOffset, instr.operand(0));
          }
        }

      }
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
      // A switch's case targets are the arm entry points the CFG no longer keeps: an arm that
      // prints nothing still entered its block here, and which block that was decides if the
      // source wrote a bare `break;` there.
      if (instr instanceof org.jetbrains.java.decompiler.code.SwitchInstruction sw) {
        int[] dests = sw.getDestinations();
        int fallback = sw.getDefaultDestination();
        if (dests != null && fallback >= 0 && fallback < seq.length()) {
          int[] targets = new int[dests.length + 1];
          targets[0] = seq.getInstr(fallback).startOffset;
          for (int d = 0; d < dests.length; d++) {
            if (dests[d] < 0 || dests[d] >= seq.length()) {
              targets = null;
              break;
            }
            targets[d + 1] = seq.getInstr(dests[d]).startOffset;
          }
          if (targets != null) {
            switches.put(instr.startOffset, targets);
          }
        }
      }
      // `store N; load N; return`: javac's copy of a value the source kept in a variable. The
      // printer folded the copy away; the slot's LVT entry proves the variable existed. A store
      // inside a try is not adjacent to the load, which sits after the catch: there the try body
      // ends with `store N; goto L` and L is exactly `load N; return`.
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
        if (exit.opcode == CodeConstants.opc_goto || exit.opcode == CodeConstants.opc_goto_w) {
          handlerEnds.put(seq.getInstr(handlerIndex).startOffset, exit.startOffset);
        }
        // A finally handler's body ends with athrow; javac copies that body to every path that
        // leaves the protected range, so the same instruction run appears several times.
        int start = seq.getInstr(handlerIndex).startOffset;
        int athrow = -1;
        for (int i = handlerIndex; i < seq.length(); i++) {
          int opcode = seq.getInstr(i).opcode;
          if (opcode == CodeConstants.opc_athrow) {
            athrow = seq.getInstr(i).startOffset;
            break;
          }
          if (opcode == CodeConstants.opc_goto || opcode == CodeConstants.opc_return) {
            break;
          }
        }
        if (athrow >= 0) {
          finallyCopies.add(new int[]{start, athrow});
        }
      }
    }
    HANDLER_ENDS.put(method, handlerEnds);
    // Inlined copies of a finally body: every instruction of the handler up to its athrow, found
    // again elsewhere in the stream. Record the offset just past each copy and the method's last
    // instruction offset, so a `return` that only a copy jumps to can be recognised.
    java.util.Set<Integer> copyEnds = new java.util.HashSet<>();
    for (int[] body : finallyCopies) {
      java.util.List<long[]> signature = new java.util.ArrayList<>();
      for (int i = 0; i < seq.length(); i++) {
        Instruction instr = seq.getInstr(i);
        if (instr.startOffset < body[0]) {
          continue;
        }
        if (instr.startOffset >= body[1]) {
          break;
        }
        signature.add(new long[]{instr.opcode, 0});
      }
      // javac prefixes the handler itself with the exception store; the inlined copies do not have
      // it, so it is not part of the body being copied.
      if (!signature.isEmpty()
          && signature.get(0)[0] >= CodeConstants.opc_istore && signature.get(0)[0] <= CodeConstants.opc_astore) {
        signature.remove(0);
      }
      // ...and the rethrow's own value load sits right before the athrow, also not copied.
      if (!signature.isEmpty()
          && signature.get(signature.size() - 1)[0] >= CodeConstants.opc_iload
          && signature.get(signature.size() - 1)[0] <= CodeConstants.opc_aload) {
        signature.remove(signature.size() - 1);
      }
      if (signature.isEmpty()) {
        continue;
      }
      for (int start = 0; start + signature.size() <= seq.length(); start++) {
        if (seq.getInstr(start).startOffset >= body[0] && seq.getInstr(start).startOffset < body[1]) {
          continue;
        }
        boolean same = true;
        for (int k = 0; k < signature.size(); k++) {
          Instruction instr = seq.getInstr(start + k);
          long[] want = signature.get(k);
          if (instr.opcode != want[0]) {
            same = false;
            break;
          }
        }
        if (same) {
          copyEnds.add(seq.getInstr(start + signature.size() - 1).startOffset + seq.getInstr(start + signature.size() - 1).length);
        }
      }
    }
    FINALLY_COPY_ENDS.put(method, copyEnds);
    LAST_INSTRUCTION.put(method, seq.length() == 0 ? -1 : seq.getInstr(seq.length() - 1).startOffset);
    GOTO_TARGETS.put(method, gotos);
    SWITCH_TARGETS.put(method, switches);
    BRANCH_STARTS.put(method, branchStarts);
    RETURN_STORES.put(method, returnStores);
    DUP_STORES.put(method, dupStores);
    STORE_SITES.put(method, storeSites);
    LOAD_SITES.put(method, loadSites);
    STORE_SLOTS.put(method, storeSlots);
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
   * True when the target's last condition branch jumps to the arm the printed condition says it
   * should not: an {@code &&} chain's last test branches to the else arm, an {@code ||} chain's to
   * the then arm, so a branch to the other arm proves the source wrote the negated condition with
   * the arms the other way round. Unlike the opcode test this reads the branch's destination, which
   * does not depend on how the decompiler typed the operands.
   */
  public static boolean swapIfArmsByTarget(Exprent head, Statement thenArm, Statement elseArm) {
    if (!selector("polaritytarget") || !(head instanceof IfExprent ifHead)) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    int thenStart = firstOffset(thenArm);
    int elseStart = firstOffset(elseArm);
    int target = lastBranchTarget(ifHead.bytecode);
    if (thenStart < 0 || elseStart < 0 || target < 0 || thenStart == elseStart) {
      return false;
    }
    boolean or = lastAtomUnderOr(ifHead.getCondition(), false);
    return or ? target == elseStart : target == thenStart;
  }

  /**
   * True when the target's last condition branch lands on the arm the printed condition says it
   * should: an {@code &&} chain's last test reaches the else arm, an {@code ||} chain's the then
   * arm. When this holds the tree's polarity is the source's, and line evidence about the arms
   * must not flip it.
   */
  public static boolean polaritySelfConsistent(Exprent head, Statement thenArm, Statement elseArm) {
    if (!selector("polaritytarget") || !(head instanceof IfExprent ifHead)) {
      return false;
    }
    if (currentMethod() == null) {
      return false;
    }
    int thenStart = firstOffset(thenArm);
    int elseStart = firstOffset(elseArm);
    int target = lastBranchTarget(ifHead.bytecode);
    if (thenStart < 0 || elseStart < 0 || target < 0 || thenStart == elseStart) {
      return false;
    }
    boolean or = lastAtomUnderOr(ifHead.getCondition(), false);
    return or ? target == thenStart : target == elseStart;
  }

  /** The first instruction offset a statement covers, including its condition's operands. */
  public static int statementOffset(Statement statement) {
    if (statement == null) {
      return -1;
    }
    BitSet bits = new BitSet();
    statement.getOffset(bits);
    return bits.nextSetBit(0);
  }

  /**
   * True when the head's last condition branch lands on the first instruction of the arm the tree
   * prints as its then arm. javac sends a condition's last test to the else arm (or to the
   * statement after an else-less if), never to the then arm, so a branch that lands there proves
   * the tree labelled the arms the wrong way round: the source wrote the disjunction positively
   * with this arm after the other one. The head has to carry the whole printed condition; a head
   * that merged another statement's test spans offsets the condition's own operands do not.
   */
  public static boolean swapIfArmsByLastTarget(Exprent head, Statement thenArm) {
    if (!selector("ifarmtarget") || !(head instanceof IfExprent ifHead)) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null || thenArm == null || ifHead.bytecode == null || ifHead.bytecode.isEmpty()) {
      return false;
    }
    Exprent condition = ifHead.getCondition();
    if (condition == null || declaresPatternVariable(condition)) {
      return false;
    }
    BitSet conditionRange = new BitSet();
    condition.getBytecodeRange(conditionRange);
    if (conditionRange.isEmpty() || conditionRange.length() != ifHead.bytecode.length()) {
      return false;
    }
    // An unconditional jump inside the test region is the `continue`/`break` of a guard the tree
    // merged into this condition: the source wrote several statements, not one disjunction.
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (gotos != null) {
      for (int at = ifHead.bytecode.nextSetBit(0); at >= 0 && at < ifHead.bytecode.length();
           at = ifHead.bytecode.nextSetBit(at + 1)) {
        if (gotos.containsKey(at)) {
          return false;
        }
      }
    }
    int target = lastBranchTarget(ifHead.bytecode);
    return target > 0 && target == statementOffset(thenArm);
  }

  /** Whether the expression declares a pattern variable of its own. */
  private static boolean declaresPatternVariable(Exprent exprent) {
    for (Exprent part : exprent.getAllExprents(true, true)) {
      if (part instanceof FunctionExprent function
          && function.getFuncType() == FunctionExprent.FunctionType.INSTANCEOF
          && function.getLstOperands().size() > 2) {
        return true;
      }
    }
    return false;
  }

  /** The destination of the last conditional branch inside these offsets, or -1. */
  private static int lastBranchTarget(BitSet bytecode) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    if (ends == null || targets == null || bytecode == null || bytecode.isEmpty()) {
      return -1;
    }
    int lastStart = -1;
    int lastTarget = -1;
    for (int offset = bytecode.nextSetBit(0); offset >= 0; offset = bytecode.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end != null && targets.containsKey(end) && offset > lastStart) {
        lastStart = offset;
        lastTarget = targets.get(end);
      }
    }
    return lastTarget;
  }

  /**
   * Whether the condition's last test jumps on success rather than on failure: the last atom of an
   * {@code ||} chain does, the last atom of an {@code &&} chain does not, and a negation flips it.
   */
  private static boolean lastAtomUnderOr(Exprent condition, boolean inverted) {
    while (condition instanceof FunctionExprent function) {
      FunctionExprent.FunctionType type = function.getFuncType();
      if (type == FunctionExprent.FunctionType.BOOL_NOT) {
        Exprent inner = function.getLstOperands().get(0);
        // A negation of an atom is the atom's own polarity and leaves the side alone; a negation of
        // a chain swaps the connective, so the chain is read with the flag flipped.
        if (inner instanceof FunctionExprent nested
            && (nested.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND
                || nested.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_OR)) {
          inverted = !inverted;
          condition = inner;
          continue;
        }
        return inverted;
      }
      if (type == FunctionExprent.FunctionType.BOOLEAN_AND || type == FunctionExprent.FunctionType.BOOLEAN_OR) {
        inverted ^= type == FunctionExprent.FunctionType.BOOLEAN_OR;
        java.util.List<Exprent> operands = function.getLstOperands();
        condition = operands.get(operands.size() - 1);
      } else {
        return inverted;
      }
    }
    return inverted;
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
   * True when the target's line table puts a candidate for-update on a line distinct from the
   * condition's, proving the source wrote it as the loop body's last statement rather than in a
   * for header. A for header's update carries the header's line, which the condition shares
   * unless the header itself was written across several lines; the caller only uses this to keep
   * the while form, which compiles to the same instructions either way.
   */
  public static boolean updateIsBodyStatement(Exprent condition, Exprent update) {
    if (!selector("whileupdate")) {
      return false;
    }
    int updateLine = sourceLine(update);
    int conditionLine = sourceLine(condition);
    return updateLine >= 0 && conditionLine >= 0 && updateLine != conditionLine;
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

  /**
   * True when this void return is only reached by falling out of a protected region: the method's
   * last instruction is a shared exit, and some jump into it sits right after an inlined copy of a
   * finally body. A return the source wrote inside try/finally gets its own return instruction.
   */
  public static boolean fallsOutOfFinally(Exprent exit) {
    if (!selector("finallycopy") || exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Set<Integer> copyEnds = FINALLY_COPY_ENDS.get(method);
    Integer last = LAST_INSTRUCTION.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    int offset = exit.bytecode.nextSetBit(0);
    if (copyEnds == null || last == null || gotos == null || offset < 0 || offset != last) {
      return false;
    }
    boolean hit = false;
    for (java.util.Map.Entry<Integer, Integer> goto_ : gotos.entrySet()) {
      if (goto_.getValue() == offset && copyEnds.contains(goto_.getKey())) {
        hit = true;
        break;
      }
    }
    return hit;
  }

  /** The first offset after the protected range of the handler at this offset, or -1. */
  public static int handlerExitOffset(int handlerOffset) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : HANDLER_ENDS.get(method);
    Integer end = ends == null ? null : ends.get(handlerOffset);
    return end == null ? -1 : end;
  }

  /**
   * True when the target's return sits past the try's protected range. javac ends the range at a
   * skip-goto, so a return written after the try/catch starts at or after that goto's destination,
   * while one folded into the body starts before it.
   */
  public static boolean returnPastTry(Exprent exit, int handlerOffset) {
    if (exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return false;
    }
    int skip = handlerExitOffset(handlerOffset);
    if (skip < 0 || exit.bytecode.nextSetBit(0) < skip) {
      return false;
    }
    // The return instruction can sit past the range while the value it returns was computed
    // inside it: `return valueOf(response);` keeps the call protected and only the return
    // outside, which is `T result; try { result = …; } catch …; return result;`. Hoisting such a
    // return would move the call out of the range and let the exception escape.
    if (exit instanceof ExitExprent exitExprent) {
      Exprent value = exitExprent.getValue();
      int valueStart = value == null ? -1 : firstOffsetOf(value);
      if (valueStart >= 0 && valueStart < skip) {
        return false;
      }
    }
    return true;
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
   * on, so the line the operand's text begins and ends on is read from its parts, and the
   * beginning is the first line-table entry the operand's left-hand evaluation chain reaches.
   */
  public static boolean newlineBetweenOperands(Exprent before, Exprent after) {
    if (!enabled() || after == null) {
      return false;
    }
    int end = lastLine(before);
    if (end < 0) {
      end = sourceLineEnd(before);
    }
    // Only a line the operand's own text begins at proves the source broke before it: a later
    // entry inside the operand may belong to a sub-expression that starts its own line.
    int start = operandStartLine(after);
    return start >= 0 && end >= 0 && start > end;
  }

  /** The last source line the expression's text covers, or -1. */
  private static int lastLine(Exprent exprent) {
    int end = -1;
    for (Exprent part : exprent.getAllExprents(true, false)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int line = lineAtOffset(part.bytecode.previousSetBit(Integer.MAX_VALUE));
      if (line > end) {
        end = line;
      }
    }
    return end;
  }

  /**
   * True when the target ran this increment before anything the next statement loads, which is what
   * `++x; use(x);` compiles to: javac evaluates the statement's own side effect first. The inlined
   * form `use(++x)` loads the receiver (or the first argument) before the increment instead.
   */
  public static boolean ppmmStandsAlone(Exprent ppmm, Exprent next) {
    if (!selector("ppmminline")) {
      return false;
    }
    int inc = firstOffsetOf(ppmm);
    int nxt = firstOffsetOf(next);
    return inc >= 0 && nxt >= 0 && inc < nxt;
  }

  /**
   * True when the target ran this increment before the expression's first instruction and on a line
   * of its own: the source wrote `++x;` as a statement, so inlining would both move the iinc behind
   * whatever the expression evaluates first and print two source lines as one. When the increment and
   * the expression share a line the two forms compile to the same bytes, and the printer's inline
   * form is the source's.
   */
  public static boolean updatePrecedesExpression(Exprent update, Exprent expression) {
    if (!selector("ppmmearly")) {
      return false;
    }
    int inc = firstOffsetOf(update);
    int first = firstOffsetOf(expression);
    if (inc < 0 || first < 0 || inc >= first) {
      return false;
    }
    int incLine = lineAtOffset(inc);
    int firstLine = lineAtOffset(first);
    return incLine >= 0 && firstLine >= 0 && incLine != firstLine;
  }

  /**
   * The smallest instruction offset the expression's evaluation touches, or -1. A switch expression
   * owns no offsets of its own; its instructions are its backing statement's, and the evaluation
   * starts at that statement's first one.
   */
  public static int evaluationOffset(Exprent exprent) {
    if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.SwitchExprent sw
        && selector("switchline")) {
      // The switch's own instructions begin at the block holding its selector; its arms start
      // later, and an empty head block would make the arms look like the start.
      Statement head = sw.getBacking().getFirst();
      org.jetbrains.java.decompiler.util.StartEndPair range = head == null ? null : head.getStartEndRange();
      int offset = range == null ? -1 : range.start;
      if (offset < 0) {
        offset = firstOffset(sw.getBacking());
      }
      if (offset >= 0) {
        return offset;
      }
    }
    return firstOffsetOf(exprent);
  }

  /** The smallest instruction offset any part of the expression owns, or -1. */
  private static int firstOffsetOf(Exprent exprent) {
    int first = -1;
    for (Exprent part : exprent.getAllExprents(true, true)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int offset = part.bytecode.nextSetBit(0);
      if (first < 0 || offset < first) {
        first = offset;
      }
    }
    return first;
  }

  /**
   * The target's line at which the operand's text begins, or -1 when its table has no entry of
   * its own. Only an entry at the operand's own first instruction proves the source broke before
   * it; an entry found anywhere else belongs to a sub-expression that changed line inside it.
   */
  public static int operandStartLine(Exprent exprent) {
    int first = firstOffsetOf(exprent);
    if (first < 0 || !lineStartsAt(first)) {
      return -1;
    }
    return lineAtOffset(first);
  }

  /**
   * Whether the target's table starts a line exactly at this operand's first instruction, after
   * the line the text before it ends on. javac anchors a statement at its condition's first
   * instruction and an operand of a boolean expression only at an invocation inside it, so an
   * entry at the very first instruction proves the source wrote the test as nested statements
   * rather than as the right operand of {@code &&}.
   */
  public static boolean operandStartsStatement(Exprent before, Exprent after) {
    if (!selector("ifnest") || after == null) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    int first = firstOffsetOf(after);
    if (first < 0 || !lineStartsAt(first)) {
      return false;
    }
    int end = lastLine(before);
    int start = lineAtOffset(first);
    return end >= 0 && start > end;
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

  /** As {@link #lastInstructionStart(BitSet)} over an explicit method's instruction table. */
  public static int lastInstructionStart(BitSet bytecode, StructMethod method) {
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

  /**
   * The slot a {@code dup; store N} pair starting at this store offset writes, or -1. The
   * duplicate on the operand stack and the local N are the same value version.
   */
  public static int dupStoreSlot(StructMethod method, int storeOffset) {
    java.util.Map<Integer, Integer> map = method == null ? null : DUP_STORES.get(method);
    Integer slot = map == null ? null : map.get(storeOffset);
    return slot == null ? -1 : slot;
  }

  /** The offset just past the instruction at this start offset, or -1. */
  public static int instructionEnd(StructMethod method, int offset) {
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    Integer end = ends == null ? null : ends.get(offset);
    return end == null ? -1 : end;
  }

  /** The slot a store instruction at this start offset writes, or -1. */
  public static int storeSlotAt(StructMethod method, int offset) {
    java.util.Map<Integer, Integer> map = method == null ? null : STORE_SLOTS.get(method);
    Integer slot = map == null ? null : map.get(offset);
    return slot == null ? -1 : slot;
  }

  /** Whether the method loads this slot anywhere. */
  public static boolean loadsSlot(StructMethod method, int slot) {
    java.util.Map<Integer, BitSet> map = method == null ? null : LOAD_SITES.get(method);
    BitSet sites = map == null ? null : map.get(slot);
    return sites != null && !sites.isEmpty();
  }

  /** Whether some store to {@code slot} starts after {@code from} and no later than {@code to}. */
  public static boolean storedIn(StructMethod method, int slot, int from, int to) {
    java.util.Map<Integer, BitSet> map = method == null ? null : STORE_SITES.get(method);
    BitSet sites = map == null ? null : map.get(slot);
    if (sites == null || to <= from) {
      return false;
    }
    int next = sites.nextSetBit(from + 1);
    return next >= 0 && next <= to;
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

  /** True when the target names a type variable: a generic variable or an unknown object type. */
  public static boolean isTypeVariableTarget(VarType target) {
    if (target == null || target.arrayDim != 0) {
      return false;
    }
    if (target.type == org.jetbrains.java.decompiler.struct.gen.CodeType.GENVAR) {
      return true;
    }
    return target.type == org.jetbrains.java.decompiler.struct.gen.CodeType.OBJECT
      && !target.isGeneric() && target.value != null
      && DecompilerContext.getStructContext().getClass(target.value) == null;
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
   * {@code this.f = this.f + e} loads the field twice.  An array element's compound form
   * ({@code a[i] |= e}) duplicates the address pair instead: {@code aload a; iload i; dup2;
   * laload; ...; lastore}, where the expanded form loads {@code a} and {@code i} again.
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
    if (left instanceof ArrayExprent) {
      // The address pair (array, index) is one word each, so its duplicate is always dup2 and
      // it sits immediately before the element load the compound form reads through.
      if (opcode < CodeConstants.opc_iaload || opcode > CodeConstants.opc_saload) {
        return false;
      }
      return index > 0 && seq.getInstr(index - 1).opcode == CodeConstants.opc_dup2;
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

  /**
   * True when the target stored through a receiver javac had to cache in a temporary:
   * {@code this.part.f += e} compiles as {@code aload_0; getfield part; astore N; aload N;
   * aload N; getfield f; ...; dup_x1; putfield f; pop} — the value survives the store and is
   * discarded right after, which only an assignment expression produces, and the read has no
   * duplicate of its own because the temporary already holds the receiver.
   */
  public static boolean isCachedReceiverTarget(Exprent store, Exprent matching) {
    if (!selector("compound-temp")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    BitSet storeOffsets = store.bytecode;
    BitSet readOffsets = matching.bytecode;
    if (seq == null || storeOffsets == null || storeOffsets.isEmpty()
      || readOffsets == null || readOffsets.isEmpty()) {
      return false;
    }
    Integer storeIndex = seq.offsetToIndex().get(storeOffsets.nextSetBit(0));
    Integer readIndex = seq.offsetToIndex().get(readOffsets.nextSetBit(0));
    if (storeIndex == null || readIndex == null) {
      return false;
    }
    if (seq.getInstr(storeIndex).opcode != CodeConstants.opc_putfield
      || seq.getInstr(readIndex).opcode != CodeConstants.opc_getfield) {
      return false;
    }
    if (storeIndex == 0 || storeIndex + 1 >= seq.length()) {
      return false;
    }
    int before = seq.getInstr(storeIndex - 1).opcode;
    int after = seq.getInstr(storeIndex + 1).opcode;
    if (before != CodeConstants.opc_dup_x1 && before != CodeConstants.opc_dup2_x1) {
      return false;
    }
    if (after != CodeConstants.opc_pop && after != CodeConstants.opc_pop2) {
      return false;
    }
    // A duplicate before the read is the ordinary field compound (`this.f += e`), which the
    // matching-operand rule already covers; this shape reads through the cached temporary.
    return readIndex == 0 || !isDup(seq.getInstr(readIndex - 1).opcode);
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
    if (lastEnd >= 0 && lastEnd < bodyStart && !returns.get(lastEnd)) {
      // `if (!C) { return; } body`: the condition's branch jumps to the return, which sits before
      // the body, and the fall-through reaches the body instead. The guard prints negated.
      java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
      Integer target = targets == null ? null : targets.get(lastEnd);
      if (target != null && target >= 0 && target < bodyStart && returns.get(target)) {
        markGuardExit(method, target);
        return negateCondition(condition);
      }
    }
    if (!(lastEnd >= 0 && lastEnd < bodyStart && returns.get(lastEnd))) {
      // `if (!C) { return; }` where the exit is reached by falling out of a finally copy: the
      // branch skips a block that runs the copy and then returns, and lands right after it. The
      // return has to lie before the arm; when the arm holds it already, the printer's form is the
      // guard itself and negating the condition would invert a correct one.
      if (selector("finallyguard")) {
        java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
        Integer target = targets == null ? null : targets.get(lastEnd);
        int exit = target == null ? -1 : finallyCopyReturnBefore(method, target, bodyStart);
        if (exit >= 0) {
          markGuardExit(method, exit);
          return negateCondition(condition);
        }
      }
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

  /** The void return a finally copy falls out to, when the branch target is its end, else -1. */
  private static int finallyCopyReturnBefore(StructMethod method, int target, int bodyStart) {
    java.util.Set<Integer> copies = FINALLY_COPY_ENDS.get(method);
    BitSet returns = VOID_RETURNS.get(method);
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    if (copies == null || returns == null || ends == null) {
      return -1;
    }
    for (Integer copyEnd : copies) {
      int next = -1;
      for (Integer start : ends.keySet()) {
        if (start >= copyEnd && (next < 0 || start < next)) {
          next = start;
        }
      }
      Integer end = next < 0 ? null : ends.get(next);
      if (end != null && returns.get(next) && end == target && next < bodyStart) {
        return next;
      }
    }
    return -1;
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

  /** True when only one branch in the method enters this statement's first instruction. */
  public static boolean soleEntry(Statement stat) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    int start = stat == null ? -1 : firstOffset(stat);
    if (targets == null || start < 0) {
      return false;
    }
    int into = 0;
    for (Integer target : targets.values()) {
      if (target != null && target == start) {
        into++;
      }
    }
    return into == 1;
  }

  /**
   * True when the rest of the sequence sits physically before this arm. A source {@code if (C) { A }
   * else { B }} falls through A and jumps over it to B, so the block we print as the arm is B while
   * the statements after it are A; a guard always keeps its arm first.
   */
  public static boolean restPrecedesArm(Statement firstRest, Statement arm) {
    int restStart = firstRest == null ? -1 : firstOffset(firstRest);
    int armStart = arm == null ? -1 : firstOffset(arm);
    return restStart >= 0 && armStart >= 0 && restStart < armStart;
  }

  /** True when a local variable's scope starts inside the statement's instruction range. */
  public static boolean declaresLocal(Statement stat) {
    return declaresLocalBetween(stat, false);
  }

  /** As {@link #declaresLocal} but over the statement's own exprent offsets, not its block's end. */
  public static boolean declaresLocalIn(Statement stat) {
    return declaresLocalBetween(stat, true);
  }

  /**
   * True when the condition's branch jumps to the statement that follows the if, with the if arm
   * starting past a void return: {@code if (!C) { rest; return; } arm}. javac branches to the rest,
   * ends it with the return, and reaches the arm from the condition's own fall-through.
   */
  public static boolean guardBeforeTail(Exprent head, Statement rest, Statement arm) {
    if (!selector("guardtail") || head == null || head.bytecode == null || head.bytecode.isEmpty()) {
      return false;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    BitSet returns = method == null ? null : VOID_RETURNS.get(method);
    if (ends == null || targets == null || returns == null) {
      return false;
    }
    int restStart = firstOffset(rest);
    int armStart = firstOffset(arm);
    if (restStart < 0 || armStart <= restStart) {
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
    // The branch lands on the rest, and the one-byte return ends the guard right before the arm.
    return lastStart >= 0 && lastTarget == restStart && armStart - 1 >= 0 && returns.get(armStart - 1);
  }

  private static boolean declaresLocalBetween(Statement stat, boolean ownOffsets) {
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
    int end = ownOffsets ? lastOffset(stat) : lastEnd(stat);
    if (start < 0 || end < 0) {
      return false;
    }
    return table.getRange(start, end)
      .anyMatch(v -> v.getStart() >= start && v.getStart() <= end);
  }

  public static int lastEnd(Statement stat) {
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

  /**
   * The targets of the condition's own conditional branches, one entry per branch, in instruction
   * order. A {@code ||} compiles as one branch per operand and the operands land on different
   * targets; a simple test or a conjunction has every branch landing on one skip target.
   */
  public static int[] branchTargets(Exprent head) {
    StructMethod method = currentMethod();
    if (method == null || head == null || head.bytecode == null) {
      return new int[0];
    }
    java.util.Map<Integer, Integer> branchStarts = BRANCH_STARTS.get(method);
    if (branchStarts == null) {
      return new int[0];
    }
    java.util.List<Integer> targets = new java.util.ArrayList<>();
    for (int at = head.bytecode.nextSetBit(0); at >= 0; at = head.bytecode.nextSetBit(at + 1)) {
      Integer target = branchStarts.get(at);
      if (target != null) {
        targets.add(target);
      }
    }
    int[] result = new int[targets.size()];
    for (int i = 0; i < result.length; i++) {
      result[i] = targets.get(i);
    }
    return result;
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
   * The last test of a loop condition the source wrote as {@code if (!B) break;}: that guard
   * branches to the body and then jumps to the loop's exit, while the fused `A && B` condition
   * would branch straight to the exit and leave no goto. The recorded branch-then-goto pair whose
   * jump leaves the loop therefore proves the guard statement. Returns the tested operand, or null.
   */
  public static Exprent foldedBreakGuard(Exprent condition, Statement loop, Statement body) {
    if (!selector("loopguard") || !(condition instanceof FunctionExprent function)
        || function.getFuncType() != FunctionExprent.FunctionType.BOOLEAN_AND
        || function.getLstOperands().size() != 2) {
      return null;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return null;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    java.util.Map<Integer, int[]> sites = CONTINUE_SITES.get(method);
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    if (guards == null || sites == null || ends == null) {
      return null;
    }
    int bodyStart = firstOffset(body);
    int loopEnd = lastOffset(loop);
    if (bodyStart < 0 || loopEnd < 0) {
      return null;
    }
    int lastStart = -1;
    if (condition.bytecode != null) {
      for (int offset = condition.bytecode.nextSetBit(0); offset >= 0; offset = condition.bytecode.nextSetBit(offset + 1)) {
        if (ends.containsKey(offset) && offset > lastStart) {
          lastStart = offset;
        }
      }
    }
    if (lastStart >= 0) {
      Integer key = ends.get(lastStart);
      int[] site = key == null ? null : sites.get(key);
      Integer gotoTarget = key == null ? null : guards.get(key);
      // The branch skips to the body and the goto leaves the loop: the guard statement's signature.
      if (site != null && gotoTarget != null && site[1] == bodyStart && gotoTarget > loopEnd) {
        return function.getLstOperands().get(1);
      }
    }
    // The decompiler built the merged condition, so it carries no offsets of its own; the pair is
    // still recorded, keyed by the branch that skips to the body and jumps out of the loop.
    for (java.util.Map.Entry<Integer, int[]> entry : sites.entrySet()) {
      int key = entry.getKey();
      int[] site = entry.getValue();
      Integer gotoTarget = guards.get(key);
      if (gotoTarget != null && site[1] == bodyStart && gotoTarget > loopEnd && key <= loopEnd) {
        return function.getLstOperands().get(1);
      }
    }
    return null;
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
    // The body's first instruction may be an if's test, which the statement holds as a condition
    // exprent rather than in a block; firstOffset would report the arm's start instead.
    int bodyStart = startOffset(body);
    int tailStart = firstOffset(tailFirst);
    int tailEnd = lastEnd(tailLast);
    if (bodyStart < 0 || tailStart < 0 || tailEnd < 0 || tailEnd != bodyStart) {
      return false;
    }
    if (bodyStart != firstOffset(body) && !tailExits(tailFirst, tailLast)) {
      // Only the test's own instruction widens the body's start; such a body begins with an if, so
      // the guard's arm has to leave the method at its end. A tail that ends inside the body would
      // print its fall-through as the arm's closing brace, and the exit it takes with it is lost.
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

  /** True when the tail is one statement that leaves the method: a single return or throw. */
  private static boolean tailExits(Statement tailFirst, Statement tailLast) {
    if (tailFirst != tailLast) {
      return false;
    }
    List<Exprent> exprents = tailFirst.getExprents();
    return exprents != null && exprents.size() == 1
      && exprents.get(0) instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit
      && (exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
          || exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.THROW);
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

  /**
   * The index of the arm statement the target's then-arm ends on, when the arm was folded together
   * with the statements that follow the if: the arm statement ending at {@code g} is followed, in
   * the target, by a goto at {@code g} that jumps to {@code t}, the tail occupies {@code [g+len, t)}
   * and the arm's next statement starts at {@code t}. The source wrote
   * {@code if (C) { A } else { tail } rest}; -1 when the shape is different.
   */
  public static int thenArmSplit(Statement arm, Statement tail) {
    StructMethod method = currentMethod();
    if (method == null || arm == null || tail == null) {
      return -1;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (ends == null || gotos == null || !(arm instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement sequence)) {
      return -1;
    }
    int tailStart = firstOffset(tail);
    int tailEnd = lastEnd(tail);
    if (tailStart < 0 || tailEnd < 0) {
      return -1;
    }
    int gotoStart = -1;
    int target = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      Integer end = ends.get(entry.getKey());
      if (end != null && end == tailStart && entry.getValue() == tailEnd) {
        gotoStart = entry.getKey();
        target = entry.getValue();
        break;
      }
    }
    if (gotoStart < 0) {
      return -1;
    }
    java.util.List<Statement> stats = sequence.getStats();
    for (int k = 0; k < stats.size() - 1; k++) {
      if (lastEnd(stats.get(k)) == gotoStart && firstOffset(stats.get(k + 1)) == target) {
        return k;
      }
    }
    return -1;
  }

  /**
   * The index of the arm exprent the target's then-arm ends on when the arm is a single basic block
   * whose statements are exprents: the exprent ending just before the goto, with the next exprent
   * starting at the goto's target. Same evidence as {@link #thenArmSplit}, one level down.
   */
  public static int thenExprentSplit(java.util.List<Exprent> exprents, Statement tail) {
    StructMethod method = currentMethod();
    if (method == null || exprents == null || exprents.size() < 2 || tail == null) {
      return -1;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (ends == null || gotos == null) {
      return -1;
    }
    int tailStart = firstOffset(tail);
    int tailEnd = lastEnd(tail);
    if (tailStart < 0 || tailEnd < 0) {
      return -1;
    }
    int gotoStart = -1;
    int target = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      Integer end = ends.get(entry.getKey());
      if (end != null && end == tailStart && entry.getValue() == tailEnd) {
        gotoStart = entry.getKey();
        target = entry.getValue();
        break;
      }
    }
    if (gotoStart < 0) {
      return -1;
    }
    for (int k = 0; k + 1 < exprents.size(); k++) {
      Exprent before = exprents.get(k);
      Exprent after = exprents.get(k + 1);
      if (before.bytecode == null || before.bytecode.isEmpty()
          || after.bytecode == null || after.bytecode.isEmpty()) {
        continue;
      }
      int beforeEnd = before.bytecode.previousSetBit(Integer.MAX_VALUE) + 1;
      int afterStart = after.bytecode.nextSetBit(0);
      // The next exprent's own offsets may start after the goto target when its operands are
      // loaded first; what pins the boundary is the exprent ending exactly on the goto.
      if (beforeEnd == gotoStart && afterStart >= target) {
        return k;
      }
    }
    return -1;
  }

  /** The goto that sits immediately before this tail and jumps past it, or -1. */
  public static int gotoBeforeTail(Statement tail) {
    StructMethod method = currentMethod();
    if (method == null || tail == null) {
      return -1;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (ends == null || gotos == null) {
      return -1;
    }
    int tailStart = firstOffset(tail);
    int tailEnd = lastEnd(tail);
    if (tailStart < 0 || tailEnd < 0) {
      return -1;
    }
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      Integer end = ends.get(entry.getKey());
      if (end != null && end == tailStart && entry.getValue() == tailEnd) {
        return entry.getKey();
      }
    }
    return -1;
  }

  /** The end offset of a statement's own head exprents (an if's prelude), or -1. */
  public static int headExprentsEnd(Statement stat) {
    if (!(stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStatement)) {
      return -1;
    }
    java.util.List<Exprent> exprents = ifStatement.getFirst().getExprents();
    if (exprents == null || exprents.isEmpty()) {
      return -1;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    int max = -1;
    for (Exprent exprent : exprents) {
      if (exprent.bytecode == null) {
        continue;
      }
      for (int offset = exprent.bytecode.nextSetBit(0); offset >= 0; offset = exprent.bytecode.nextSetBit(offset + 1)) {
        Integer end = ends == null ? null : ends.get(offset);
        if (end != null && end > max) {
          max = end;
        }
      }
    }
    return max;
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

  /** Statements a loop prints after its closing brace; their prints on the way through are breaks. */
  private static final ThreadLocal<java.util.Map<StructMethod, java.util.Set<Statement>>> DEFERRED_EXITS =
    ThreadLocal.withInitial(java.util.concurrent.ConcurrentHashMap::new);
  /** Deferred ifs whose merged head block already printed where the source ran it. */
  private static final ThreadLocal<java.util.Map<StructMethod, java.util.Set<Statement>>> CONSUMED_HEADS =
    ThreadLocal.withInitial(java.util.concurrent.ConcurrentHashMap::new);

  /**
   * The statements this loop must print after its closing brace: the target laid them out past the
   * loop's back edge, so they are the block a {@code break} jumps to, not part of the body. The
   * source wrote the break and the block after the loop; printing the block inside the arm would
   * move it ahead of the body and drop the jump. Empty when the target's layout shows no such
   * block, and when a test inside the body jumps into it as well — then it belongs to the body.
   */
  public static java.util.List<Statement> deferExitsAfter(Statement loop) {
    java.util.List<Statement> out = new java.util.ArrayList<>();
    StructMethod method = currentMethod();
    if (method == null || !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      return out;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    java.util.Map<Integer, Integer> branches = BRANCH_TARGETS.get(method);
    int head = firstOffset(loop);
    int loopEnd = lastOffset(loop);
    if (gotos == null || head < 0 || loopEnd < 0) {
      return out;
    }
    int backEdge = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getValue() != null && entry.getValue() == head && entry.getKey() > backEdge) {
        backEdge = entry.getKey();
      }
    }
    if (backEdge < 0) {
      return out;
    }
    // The first instruction after the back edge that an unconditional jump reaches is the block's
    // start; the source's break is that jump.
    int tail = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      int from = entry.getKey();
      Integer to = entry.getValue();
      if (to != null && from > head && from < to && to > backEdge && to <= loopEnd && (tail < 0 || to < tail)) {
        tail = to;
      }
    }
    if (tail < 0) {
      return out;
    }
    if (branches != null) {
      for (java.util.Map.Entry<Integer, Integer> entry : branches.entrySet()) {
        Integer to = entry.getValue();
        if (to != null && to >= tail && entry.getKey() > head && entry.getKey() <= backEdge) {
          // A test in the body reaches the block without jumping out of the loop: it is body.
          return out;
        }
      }
    }
    collectDeferred(loop, tail, out);
    if (!out.isEmpty() && (usesLoopLocals(loop, out) || reachesFromOutside(loop, out))) {
      // A value the body declares is not in scope after the loop; the block cannot move. And a
      // block another path enters is not the loop's own exit.
      out.clear();
    }
    if (!out.isEmpty()) {
      out.sort(java.util.Comparator.comparingInt(RoundTrip::firstOffset));
      DEFERRED_EXITS.get().computeIfAbsent(method, key -> java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>())).addAll(out);
    }
    return out;
  }

  /**
   * True when something outside the loop jumps to a block the loop would move, or when the jump
   * that reaches it comes from inside a switch — there a printed {@code break} would leave the
   * switch instead of the loop.
   */
  private static boolean reachesFromOutside(Statement loop, java.util.List<Statement> deferred) {
    for (Statement stat : deferred) {
      for (StatEdge edge : stat.getAllPredecessorEdges()) {
        Statement source = edge.getSource();
        if (!loop.containsStatementStrict(source)) {
          return true;
        }
        for (Statement parent = source; parent != null && parent != loop; parent = parent.getParent()) {
          if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /** True when a statement the loop would move reads a variable the loop body declares. */
  private static boolean usesLoopLocals(Statement loop, java.util.List<Statement> deferred) {
    java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> defined = new java.util.HashSet<>();
    collectDefinitions(loop, deferred, defined);
    if (defined.isEmpty()) {
      return false;
    }
    for (Statement stat : deferred) {
      if (readsAny(stat, defined)) {
        return true;
      }
    }
    return false;
  }

  private static void collectDefinitions(Statement stat, java.util.List<Statement> deferred,
                                         java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> out) {
    for (Exprent exprent : ownExprents(stat)) {
      if (exprent instanceof VarExprent var && var.isDefinition()) {
        out.add(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var));
      }
    }
    for (Statement child : stat.getStats()) {
      if (deferred.contains(child)) {
        // A deferred if's head block prints where it stands, so it stays inside the loop.
        if (child instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat
            && ifstat.getFirst() != null) {
          collectDefinitions(ifstat.getFirst(), deferred, out);
        }
        continue;
      }
      collectDefinitions(child, deferred, out);
    }
  }

  private static boolean readsAny(Statement stat, java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> defined) {
    for (Exprent exprent : ownExprents(stat)) {
      if (exprent instanceof VarExprent var && defined.contains(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var))) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      // An if's head block printed in place and is not part of what moves.
      if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat
          && child == ifstat.getFirst()) {
        continue;
      }
      if (readsAny(child, defined)) {
        return true;
      }
    }
    return false;
  }

  /** The exprents a statement prints itself, nested expressions included. */
  private static java.util.List<Exprent> ownExprents(Statement stat) {
    java.util.List<Exprent> out = new java.util.ArrayList<>();
    java.util.List<Exprent> direct = stat.getExprents() != null ? stat.getExprents() : stat.getStatExprents();
    for (Exprent exprent : direct) {
      if (exprent != null) {
        out.addAll(exprent.getAllExprents(true, true));
      }
    }
    return out;
  }

  /** Collects the outermost statements that start at or after the tail, without descending into them. */
  private static void collectDeferred(Statement stat, int tail, java.util.List<Statement> out) {
    for (Statement child : stat.getStats()) {
      if (startsAtTail(child, tail)) {
        // A bare void return is the loop's own exit and already prints as the break that reaches
        // it; there is nothing to move past the loop.
        if (!isBareVoidReturn(child)) {
          out.add(child);
        }
      }
      else {
        collectDeferred(child, tail, out);
      }
    }
  }

  /** True when the statement is one bare void return and nothing else. */
  private static boolean isBareVoidReturn(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    return exprents != null && exprents.size() == 1
      && exprents.get(0) instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit
      && exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
      && exit.getValue() == null;
  }

  /**
   * True when the statement's own instructions all lie in the tail. An if may hold, as its head
   * block, statements the decompiler merged before the test; those print where they ran and only
   * the test and its arms move, so the head is not part of the test.
   */
  private static boolean startsAtTail(Statement stat, int tail) {
    int start = startOffset(stat);
    if (start >= tail) {
      return true;
    }
    if (!(stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat)
        || ifstat.getFirst() == null || stat.getStats().size() < 2) {
      return false;
    }
    if (ifstat.getHeadexprent() != null) {
      BitSet condition = ifstat.getHeadexprent().getCondition().bytecode;
      if (condition == null || condition.isEmpty() || condition.nextSetBit(0) < tail) {
        return false;
      }
    }
    for (Statement child : stat.getStats()) {
      if (child == ifstat.getFirst()) {
        continue;
      }
      int childStart = startOffset(child);
      if (childStart < 0 || childStart < tail) {
        return false;
      }
    }
    return true;
  }

  /** True when this statement's position prints as the break that jumps to the moved block. */
  public static boolean isDeferredExit(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null) {
      return false;
    }
    java.util.Set<Statement> deferred = DEFERRED_EXITS.get().get(method);
    return deferred != null && deferred.contains(stat);
  }

  /** True when the statement's merged head block belongs where the body printed it, not here. */
  public static boolean isHeadConsumed(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null) {
      return false;
    }
    java.util.Set<Statement> consumed = CONSUMED_HEADS.get().get(method);
    return consumed != null && consumed.contains(stat);
  }

  /** Records that a deferred if's head block printed where the source ran it. */
  public static void consumeHead(Statement stat) {
    StructMethod method = currentMethod();
    if (method != null && stat != null) {
      CONSUMED_HEADS.get().computeIfAbsent(method, key -> java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>())).add(stat);
    }
  }

  /** Forgets the deferred set once the loop is about to print the statements itself. */
  public static void releaseDeferredExits(java.util.List<Statement> deferred) {
    StructMethod method = currentMethod();
    if (method == null) {
      return;
    }
    java.util.Set<Statement> set = DEFERRED_EXITS.get().get(method);
    if (set != null) {
      set.removeAll(deferred);
    }
  }

  private static void markGuardExit(StructMethod method, int offset) {
    CONSUMED_GUARD_EXITS.computeIfAbsent(method, key -> java.util.concurrent.ConcurrentHashMap.newKeySet()).add(offset);
  }

  /**
   * Records that this exit's instruction is already accounted for by the form the printer emits, so
   * it must not be printed a second time. A compact record constructor's implicit return is the
   * caller: the closing brace stands for it, and the tree keeps the exprent.
   */
  public static void consumeExit(StructMethod method, Exprent exit) {
    if (method == null || exit == null || exit.bytecode == null) {
      return;
    }
    for (int offset = exit.bytecode.nextSetBit(0); offset >= 0; offset = exit.bytecode.nextSetBit(offset + 1)) {
      markGuardExit(method, offset);
    }
  }

  /** True when this exprent is an exit whose instruction a printed form already accounts for. */
  public static boolean isConsumedExit(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || !(exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent)) {
      return false;
    }
    BitSet offsets = exprent.bytecode;
    if (offsets == null) {
      return false;
    }
    java.util.Set<Integer> consumed = CONSUMED_GUARD_EXITS.get(method);
    if (consumed == null || consumed.isEmpty()) {
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
    return exitAfterBodyImpl(exitStatement, body);
  }

  /**
   * True when the target's last condition branch lands straight on the exit this break edge leaves
   * for, with no branch-then-goto pair recorded at that branch end: the source wrote
   * {@code if (!C) { rest } else { break; }}. The guard form {@code if (C) { break; } rest}
   * compiles to a branch over a jump to the exit, which the scan records as a pair.
   */
  public static boolean breakBranchLandsOnExit(Exprent head, Statement stat) {
    if (!selector("elsebreak")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null || head == null || head.bytecode == null || head.bytecode.isEmpty() || stat == null) {
      return false;
    }
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    if (targets == null) {
      return false;
    }
    Statement loop = stat.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    if (loop == null) {
      return false;
    }
    int end = head.bytecode.length();
    Integer target = targets.get(end);
    // The branch has to leave the loop entirely: the exit is past everything the loop covers.
    int loopEnd = lastOffset(loop);
    if (target == null || loopEnd < 0 || target <= loopEnd) {
      return false;
    }
    return guards == null || !guards.containsKey(end);
  }

  /** Marks a statement whose trailing jump the caller prints as part of a wider shape. */
  public static Statement suppressJump(Statement stat) {
    Statement old = SUPPRESSED_JUMP.get();
    SUPPRESSED_JUMP.set(stat);
    return old;
  }

  public static void restoreJump(Statement old) {
    if (old == null) {
      SUPPRESSED_JUMP.remove();
    } else {
      SUPPRESSED_JUMP.set(old);
    }
  }

  public static boolean isJumpSuppressed(Statement stat) {
    Statement suppressed = SUPPRESSED_JUMP.get();
    if (stat == null || suppressed == null) {
      return false;
    }
    // The suppressed jump may hang off any statement on the tail path: an arm ending in
    // `if (…) { … } else { … }` carries its break as the if's own edge.
    Statement last = suppressed;
    while (true) {
      if (last == stat) {
        return true;
      }
      if (last.getExprents() != null || last.getStats().isEmpty()) {
        return false;
      }
      last = last.getStats().get(last.getStats().size() - 1);
    }
  }

  /** The first instruction offset of a statement, counting an if statement's head condition. */
  public static int statementStart(Statement stat) {
    int min = firstOffset(stat);
    if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStat
        && ifStat.getHeadexprent() != null) {
      BitSet bits = ifStat.getHeadexprent().bytecode;
      if (bits != null && !bits.isEmpty()) {
        int offset = bits.nextSetBit(0);
        if (offset >= 0 && (min < 0 || offset < min)) {
          min = offset;
        }
      }
    }
    return min;
  }

  /** The jump target of a condition's last branch, the branch that skips the then arm, or -1. */
  public static int lastBranchTarget(Exprent head) {
    StructMethod method = currentMethod();
    BitSet offsets = head == null ? null : head.bytecode;
    if (method == null || offsets == null || offsets.isEmpty()) {
      return -1;
    }
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    if (targets == null) {
      return -1;
    }
    Integer target = targets.get(offsets.length());
    return target == null ? -1 : target;
  }

  /** True when any forward jump lands exactly on that offset: a jump to a jump, not a fall-in. */
  public static boolean jumpsOnto(int target) {
    return target > 0 && jumpsOnto(0, target, target);
  }

  /**
   * True when a forward jump starting in {@code [from, before)} lands on {@code target}: the code
   * there leaves by skipping straight over the range, which no fall-through path does.
   */
  public static boolean jumpsOnto(int from, int before, int target) {
    StructMethod method = currentMethod();
    if (method == null || from < 0 || before < 0 || target < 0) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (gotos != null) {
      for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
        if (entry.getValue() == target && entry.getValue() > entry.getKey()
            && entry.getKey() >= from && entry.getKey() < before) {
          return true;
        }
      }
    }
    java.util.Map<Integer, Integer> branches = BRANCH_TARGETS.get(method);
    if (branches != null) {
      // A conditional branch is keyed by the offset just past it; the instruction starts before.
      for (java.util.Map.Entry<Integer, Integer> entry : branches.entrySet()) {
        int start = entry.getKey() - 1;
        if (entry.getValue() == target && entry.getValue() > entry.getKey()
            && start >= from && start < before) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * True when the target's then-arm ends with a jump over the returning block our sequence prints
   * as the statement after the if: the source wrote {@code if (C) { A } else { return X; }} and the
   * arm's fall-through reaches the rest instead. The jump has to sit immediately after the arm's
   * own last instruction, so a merge jump generated for some other construct cannot trigger it.
   */
  public static boolean gotoPastsExit(Statement arm, Statement exit) {
    if (!selector("elseblock")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null || arm == null || exit == null) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (gotos == null) {
      return false;
    }
    int exitStart = firstOffset(exit);
    int armEnd = lastEnd(arm);
    // A goto is three bytes; it must start where the arm's last instruction ends and end on the
    // returning block's first instruction.
    if (exitStart < 0 || armEnd < 0 || armEnd + 3 != exitStart) {
      return false;
    }
    Integer target = gotos.get(exitStart);
    return target != null && target > exitStart;
  }

  /**
   * True when a jump skips exactly this arm: the target records a goto that ends on the arm's first
   * instruction and lands on the instruction after the arm, and the statement before the arm ends
   * where that goto begins. The source wrote `if (C) { rest } else { arm }`; printing the arm after
   * the rest instead would run it on both paths.
   */
  public static boolean gotoJumpsOverArm(Statement arm, Statement rest) {
    if (!selector("elseblock")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null || arm == null || rest == null) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (gotos == null) {
      return false;
    }
    int start = firstOffset(arm);
    int end = lastEnd(arm);
    int restEnd = lastEnd(rest);
    if (start < 0 || end <= start || restEnd < 0 || restEnd + 3 != start) {
      return false;
    }
    // GOTO_TARGETS is keyed by the jump's own offset, which is where the rest ends.
    Integer target = gotos.get(restEnd);
    return target != null && target == end;
  }

  private static boolean exitAfterBodyImpl(Statement exitStatement, Statement body) {
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
    return selector("continueguard") && head != null && head.bytecode != null
      && !head.bytecode.isEmpty() && continuesAt(head.bytecode.length(), sequence);
  }

  /**
   * The goto the guard's printed {@code continue;} compiles to: the jump the target's table puts on
   * the line the source wrote it on, which starts where the head's branch ends. Minus one when the
   * head does not end at a recorded guard.
   */
  public static int continueGoto(Exprent head) {
    StructMethod method = currentMethod();
    if (method == null || head == null || head.bytecode == null || head.bytecode.isEmpty()) {
      return -1;
    }
    java.util.Map<Integer, int[]> sites = CONTINUE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(head.bytecode.length());
    return site == null ? -1 : site[0];
  }

  /**
   * True when this declaration belongs to the for loop after it: the target's table gives the
   * variable a scope that opens at the loop's head and closes with the loop, and the loop's own
   * init declares another variable of the same type. The source wrote `for (T a = …, b = …; …)`,
   * which javac compiles exactly like the hoisted form but gives one declaration in the table.
   */
  public static boolean forInitContinues(Exprent declaration, Statement loop, Exprent init, int boundary) {
    if (!selector("forinit")) {
      return false;
    }
    if (!(declaration instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent first)
        || !(first.getLeft() instanceof VarExprent a) || !a.isDefinition()
        || !(init instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent second)
        || !(second.getLeft() instanceof VarExprent b) || !b.isDefinition()) {
      return false;
    }
    if (a.getLVT() == null || b.getLVT() == null || a.getExprType() == null
        || !a.getExprType().equals(b.getExprType())) {
      return false;
    }
    int start = firstOffset(loop);
    int end = boundary >= 0 ? boundary : lastEnd(loop);
    return start >= 0 && end > start && a.getLVT().getEnd() <= end && a.getLVT().getEnd() > start
      && b.getLVT().getEnd() <= end;
  }

  /** True when the jump into the guard sits immediately before this next test (3 bytes of goto). */
  public static boolean continuesBefore(Exprent next, Statement around) {
    if (!selector("continueguard")) {
      return false;
    }
    int start = firstOffsetOf(next);
    return start >= 3 && continuesAt(start - 3, around);
  }

  /**
   * True when this condition merges that many {@code continue} guards: the target records one jump
   * back to the loop head per statement, so an {@code ||} of n tests came from n separate
   * {@code if (C) continue;} statements rather than one shared condition.
   */
  /**
   * The operand groups the target's recorded continue guards split this condition into, or null
   * when it holds fewer than two. Each guard key K ends one written statement: the next statement
   * starts at K+3, so the group boundary is the first operand that begins at or after it. Unlike
   * {@link #splitsIntoGuards} this does not need one guard per operand — a written guard may itself
   * be a chain of several tests.
   */
  public static java.util.List<java.util.List<Exprent>> guardGroups(Exprent head, java.util.List<Exprent> operands,
                                                                   Statement around) {
    if (!selector("continueguard") || head == null || head.bytecode == null || head.bytecode.isEmpty()
        || operands.size() < 2) {
      return null;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(currentMethod());
    if (guards == null || guards.isEmpty()) {
      return null;
    }
    java.util.List<Integer> keys = new java.util.ArrayList<>();
    for (Integer end : guards.keySet()) {
      if (end > head.bytecode.length() || end <= 0 || !head.bytecode.get(end - 1)) {
        continue;
      }
      if (continuesAt(end, around)) {
        keys.add(end);
      }
    }
    if (keys.isEmpty()) {
      return null;
    }
    java.util.Collections.sort(keys);
    int[] starts = new int[operands.size()];
    for (int i = 0; i < starts.length; i++) {
      starts[i] = firstOffsetOf(operands.get(i));
      if (starts[i] < 0) {
        return null;
      }
    }
    java.util.List<java.util.List<Exprent>> groups = new java.util.ArrayList<>();
    int from = 0;
    for (Integer key : keys) {
      int boundary = key + 3;
      int next = from;
      while (next < starts.length && starts[next] < boundary) {
        next++;
      }
      if (next == from) {
        return null;
      }
      groups.add(new java.util.ArrayList<>(operands.subList(from, next)));
      from = next;
      if (from >= operands.size()) {
        break;
      }
    }
    if (from < operands.size()) {
      groups.add(new java.util.ArrayList<>(operands.subList(from, operands.size())));
    }
    return groups.size() > 1 ? groups : null;
  }

  public static boolean splitsIntoGuards(Exprent head, int operands, Statement around) {
    if (!selector("continueguard") || head == null || head.bytecode == null || head.bytecode.isEmpty()
        || operands < 2) {
      return false;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(currentMethod());
    if (guards == null || guards.isEmpty()) {
      return false;
    }
    int count = 0;
    for (Integer end : guards.keySet()) {
      // The branch that falls into the guard has to sit inside this condition's own bytes.
      if (end > head.bytecode.length() || end <= 0 || !head.bytecode.get(end - 1)) {
        continue;
      }
      if (continuesAt(end, around)) {
        count++;
      }
    }
    return count == operands;
  }

  private static boolean continuesAt(int end, Statement around) {
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    Integer target = guards == null ? null : guards.get(end);
    if (target == null) {
      return false;
    }
    Statement loop = around == null ? null : around.getParent();
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
    int[] site = sites == null ? null : sites.get(end);
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

  /**
   * True when this statement is the last thing printed on the way out of its loop body, so a
   * {@code continue} at its end jumps to the loop head having skipped nothing.
   */
  public static boolean endsLoopBody(Statement stat) {
    Statement cur = stat;
    for (Statement parent = cur.getParent(); parent != null; parent = cur.getParent()) {
      if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement) {
        return true;
      }
      if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement sequence) {
        // The sequence may end with an empty block that prints nothing; the last statement that
        // reaches the page is the one a continue has to follow.
        java.util.List<Statement> stats = sequence.getStats();
        int last = stats.size() - 1;
        while (last >= 0 && printsNothing(stats.get(last))) {
          last--;
        }
        if (last < 0 || stats.get(last) != cur) {
          return false;
        }
      } else if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStatement) {
        if (ifStatement.getIfstat() != cur
            || (ifStatement.getElsestat() != null && !printsNothing(ifStatement.getElsestat()))) {
          return false;
        }
      } else {
        return false;
      }
      cur = parent;
    }
    return false;
  }

  private static final ThreadLocal<java.util.ArrayDeque<Statement>> OPEN_LOOPS =
    ThreadLocal.withInitial(java.util.ArrayDeque::new);

  /** Registers a loop whose body is being printed, so a copied exit can print as its break. */
  public static void enterLoop(Statement loop) {
    OPEN_LOOPS.get().push(loop);
  }

  public static void exitLoop() {
    java.util.ArrayDeque<Statement> loops = OPEN_LOOPS.get();
    if (!loops.isEmpty()) {
      loops.poll();
    }
  }

  /**
   * True when this bare void return is a break the decompiler copied out of the loop it prints in:
   * the target records a goto inside the loop whose destination is this very return, and the return
   * sits after everything else the loop covers. The source's `break;` is that goto; printing
   * `return;` instead drops it, one instruction shorter.
   */
  public static boolean printsAsBreak(Exprent exit) {
    if (!selector("copiedbreak")) {
      return false;
    }
    StructMethod method = currentMethod();
    Statement loop = OPEN_LOOPS.get().peek();
    if (method == null || loop == null || exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return false;
    }
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)
        || doStatement.getLooptype() != org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement.Type.INFINITE) {
      return false;
    }
    int loopStart = firstOffset(loop);
    int exitStart = exit.bytecode.nextSetBit(0);
    int loopEnd = lastEndExcept(loop, exit.bytecode);
    if (loopStart < 0 || loopEnd < 0 || exitStart < 0 || exitStart < loopEnd) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (gotos == null) {
      return false;
    }
    for (java.util.Map.Entry<Integer, Integer> edge : gotos.entrySet()) {
      int from = edge.getKey();
      // The jump may start exactly where the loop's printed body ends: it is the exit edge itself.
      if (edge.getValue() == exitStart && from >= loopStart && from < exitStart) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when a switch arm's {@code break} edge is really the loop's {@code continue}: the target's
   * jump at the arm's last instruction lands on the loop's own continue point (hasNext, increment
   * or condition), which a {@code break} cannot reach — that jumps past the switch instead.
   */
  public static boolean breakJumpsToContinue(int jumpOffset) {
    if (!selector("breakcontinue") || jumpOffset < 0) {
      return false;
    }
    StructMethod method = currentMethod();
    Statement loop = OPEN_ALL_LOOPS.get().peek();
    if (method == null
        || !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    Integer target = gotos == null ? null : gotos.get(jumpOffset);
    return target != null && isLoopHeadTarget(doStatement, target);
  }

  /**
   * True when this bare void return is the method's exit that the block merely falls out of: the
   * target's jump from inside the block lands on the return, so the source let the block complete.
   * Printing a `return;` inside the braces compiles to `monitorexit; return` instead.
   */
  public static boolean fallsOutToExit(Statement block, Exprent exit) {
    if (!selector("synexit")) {
      return false;
    }
    if (!(exit instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent e)
        || e.getExitType() != org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
        || e.getValue() != null) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    int start = firstOffset(block);
    int end = lastEnd(block);
    int exitStart = exit.bytecode.nextSetBit(0);
    if (gotos == null || start < 0 || end < start || exitStart <= start) {
      return false;
    }
    for (java.util.Map.Entry<Integer, Integer> jump : gotos.entrySet()) {
      int from = jump.getKey();
      if (from >= start && from < exitStart && jump.getValue() == exitStart) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when this empty switch arm's `break;` is really the loop's `continue`. The block recorded
   * nothing, so the arm's own jump offset is gone; the switch's bytecode range is the evidence: it
   * must hold exactly one jump to the loop's continue point (that one is this arm's), and this must
   * be the switch's only empty arm, so no other arm can own it.
   */
  public static boolean emptyArmContinues(Statement arm) {
    if (!selector("breakcontinue")) {
      return false;
    }
    StructMethod method = currentMethod();
    Statement loop = OPEN_ALL_LOOPS.get().peek();
    if (method == null || !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    if (!(arm.getParent() instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement sw)) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    int start = firstOffset(sw);
    int end = lastEnd(sw);
    if (gotos == null || start < 0 || end < start) {
      return false;
    }
    java.util.List<int[]> nested = new java.util.ArrayList<>();
    collectNestedSwitchRanges(sw, nested);
    int candidates = 0;
    for (java.util.Map.Entry<Integer, Integer> edge : gotos.entrySet()) {
      int from = edge.getKey();
      if (from < start || from >= end) {
        continue;
      }
      boolean inner = false;
      for (int[] range : nested) {
        if (from >= range[0] && from < range[1]) {
          inner = true;
          break;
        }
      }
      // A jump inside a nested switch belongs to that switch's arms, not to this one.
      if (!inner && isLoopHeadTarget(doStatement, edge.getValue())) {
        candidates++;
      }
    }
    if (candidates != 1) {
      return false;
    }
    int empties = 0;
    for (java.util.List<org.jetbrains.java.decompiler.modules.decompiler.StatEdge> armEdges : sw.getCaseEdges()) {
      if (armEdges.isEmpty()) {
        continue;
      }
      Statement destination = armEdges.get(0).getDestination();
      if (destination.getExprents() != null && destination.getExprents().isEmpty()
          && destination.getStats().isEmpty()) {
        empties++;
      }
    }
    return empties == 1;
  }

  /** Byte ranges of the switches nested inside this one, so their jumps are not counted twice. */
  private static void collectNestedSwitchRanges(Statement stat, java.util.List<int[]> out) {
    for (Statement child : stat.getStats()) {
      if (child instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement nested) {
        int start = firstOffset(nested);
        int end = lastEnd(nested);
        if (start >= 0 && end >= start) {
          out.add(new int[]{start, end});
        }
      }
      collectNestedSwitchRanges(child, out);
    }
  }

  /** Loops whose body is being printed, innermost first, whatever their type. */
  private static final ThreadLocal<java.util.ArrayDeque<Statement>> OPEN_ALL_LOOPS =
    ThreadLocal.withInitial(java.util.ArrayDeque::new);

  /** Registers a loop of any type whose body is being printed. */
  public static void enterAnyLoop(Statement loop) {
    OPEN_ALL_LOOPS.get().push(loop);
  }

  public static void exitAnyLoop() {
    java.util.ArrayDeque<Statement> loops = OPEN_ALL_LOOPS.get();
    if (!loops.isEmpty()) {
      loops.poll();
    }
  }

  /**
   * True when code nested in a loop inside this one jumps to a return the decompiler copied here:
   * no unlabelled `break` can reach that far, so the source named this loop with a label.
   */
  public static boolean carriesOutwardBreak(Statement loop) {
    if (!selector("breaklabel") || loop == null) {
      return false;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (gotos == null) {
      return false;
    }
    java.util.Set<Integer> returns = copiedExitOffsets(loop);
    if (returns.isEmpty()) {
      return false;
    }
    int start = firstOffset(loop);
    int end = loopOwnEnd(loop);
    for (java.util.Map.Entry<Integer, Integer> edge : gotos.entrySet()) {
      if (edge.getKey() >= start && returns.contains(edge.getValue()) && end == edge.getValue()
          && insideNestedLoop(loop, edge.getKey())) {
        return true;
      }
    }
    return false;
  }

  /**
   * The label a bare void return prints with when it is the target's jump out of an enclosing loop
   * that the jump cannot reach without a name, or null when it prints as `return;`/plain `break;`.
   */
  public static String labelledBreakLabel(Exprent exit) {
    if (!selector("breaklabel") || exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return null;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    int exitStart = exit.bytecode.nextSetBit(0);
    if (gotos == null || exitStart < 0) {
      return null;
    }
    java.util.Iterator<Statement> loops = OPEN_ALL_LOOPS.get().iterator();
    if (loops.hasNext()) {
      loops.next();
    }
    while (loops.hasNext()) {
      Statement loop = loops.next();
      int start = firstOffset(loop);
      if (start < 0 || loopOwnEnd(loop) != exitStart) {
        continue;
      }
      for (java.util.Map.Entry<Integer, Integer> edge : gotos.entrySet()) {
        if (edge.getValue() == exitStart && edge.getKey() >= start && edge.getKey() < exitStart) {
          return "label" + loop.id;
        }
      }
    }
    return null;
  }

  /** Where this loop's own body ends: the instruction after its back edge to the head. */
  private static int loopOwnEnd(Statement loop) {
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return -1;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    Exprent head = doStatement.getConditionExprent();
    if (ends == null || gotos == null || head == null) {
      return -1;
    }
    // A condition the decompiler composed carries no offsets of its own.
    int headStart = head.bytecode != null && !head.bytecode.isEmpty()
      ? head.bytecode.nextSetBit(0) : firstOffsetOf(head);
    if (headStart < 0) {
      return -1;
    }
    int end = -1;
    for (java.util.Map.Entry<Integer, Integer> edge : gotos.entrySet()) {
      if (edge.getValue() == headStart) {
        Integer instructionEnd = ends.get(edge.getKey());
        if (instructionEnd != null && instructionEnd > end) {
          end = instructionEnd;
        }
      }
    }
    return end;
  }

  /** Offsets where a bare void return sits anywhere inside this statement. */
  private static java.util.Set<Integer> copiedExitOffsets(Statement stat) {
    java.util.Set<Integer> offsets = new java.util.HashSet<>();
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    queue.add(stat);
    while (!queue.isEmpty()) {
      Statement cur = queue.poll();
      List<Exprent> exprents = cur.getExprents();
      if (exprents != null) {
        for (Exprent exprent : exprents) {
          for (Exprent part : exprent.getAllExprents(true, true)) {
            if (part instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit
                && exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
                && exit.getValue() == null
                && exit.bytecode != null && !exit.bytecode.isEmpty()) {
              offsets.add(exit.bytecode.nextSetBit(0));
            }
          }
        }
      }
      queue.addAll(cur.getStats());
    }
    return offsets;
  }

  /** Whether this offset lies inside a loop nested in {@code outer}. */
  private static boolean insideNestedLoop(Statement outer, int offset) {
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    for (Statement child : outer.getStats()) {
      queue.add(child);
    }
    while (!queue.isEmpty()) {
      Statement cur = queue.poll();
      if (cur instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement) {
        int start = firstOffset(cur);
        int end = lastEndExcept(cur, new BitSet());
        if (start >= 0 && end >= start && offset >= start && offset < end) {
          return true;
        }
      }
      queue.addAll(cur.getStats());
    }
    return false;
  }

  /** The last instruction end inside this statement, ignoring the offsets of one exprent. */
  private static int lastEndExcept(Statement stat, BitSet skip) {
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
            if (bits == null || (bits.isEmpty() && inner == null)) {
              continue;
            }
            for (int off = bits.nextSetBit(0); off >= 0; off = bits.nextSetBit(off + 1)) {
              if (skip != null && skip.get(off)) {
                continue;
              }
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
   * True when the head's last branch lands directly on the block this edge exits to, with no jump
   * following the branch: the source wrote `if (C) { … } else { continue; }`, and the branch to the
   * exit is the condition's own. A guard form would instead branch past a jump to the loop head and
   * record that jump as a continue guard.
   */
  public static boolean exitBranchLandsOn(Exprent head, org.jetbrains.java.decompiler.modules.decompiler.StatEdge edge) {
    if (!selector("elseexit") || head == null || head.bytecode == null || edge == null) {
      return false;
    }
    if (edge.getType() != org.jetbrains.java.decompiler.modules.decompiler.StatEdge.TYPE_CONTINUE
        && edge.getType() != org.jetbrains.java.decompiler.modules.decompiler.StatEdge.TYPE_BREAK) {
      return false;
    }
    if (edge.labeled) {
      return false;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    java.util.Map<Integer, Integer> guards = method == null ? null : CONTINUE_GUARDS.get(method);
    int exitStart = firstOffset(edge.getDestination());
    if (ends == null || targets == null || exitStart < 0 || head.bytecode.isEmpty()) {
      return false;
    }
    int lastStart = -1;
    int lastEnd = -1;
    for (int offset = head.bytecode.nextSetBit(0); offset >= 0; offset = head.bytecode.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end != null && targets.containsKey(end) && offset > lastStart) {
        lastStart = offset;
        lastEnd = end;
      }
    }
    // The branch has to land straight on where a continue of this loop goes (its increment or
    // condition), and no jump may sit between the branch and it.
    if (lastStart < 0
        || !(edge.getDestination() instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop)) {
      return false;
    }
    Integer landing = targets.get(lastEnd);
    if (landing == null || !isContinueTarget(loop, landing)) {
      return false;
    }
    return guards == null || !guards.containsKey(lastEnd);
  }

  /**
   * True when this switch arm is the one javac synthesizes for an exhaustive switch: it throws a
   * freshly built {@code MatchException} and its first instruction owns no line-table entry, so no
   * source statement wrote it. javac rebuilds it from the case list, so not printing it is exact.
   */
  public static boolean synthesizedMatchThrow(Statement stat) {
    if (!selector("matchexception") || stat == null) {
      return false;
    }
    if (!IfPatternMatchProcessor.isStatementMatchThrow(stat)) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    int start = firstOffset(stat);
    return start >= 0 && !startsLine(table, start);
  }

  /**
   * The slots the target's table declares inside this switch arm's own instruction range. A slot
   * that two arms declare is proof the source braced them: unbraced arms share the switch's block,
   * so javac would have to give the second one a fresh slot instead of reusing a dead one.
   */
  public static java.util.Map<Integer, int[]> targetSlotsDeclaredIn(Statement arm, java.util.Set<Integer> own) {
    java.util.Map<Integer, int[]> slots = new java.util.HashMap<>();
    if (!selector("armbraces") || arm == null) {
      return slots;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return slots;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return slots;
    }
    int start = firstOffset(arm);
    // The arm's own exprents bound the range; the block's last instruction can overshoot into
    // the next arm and would attribute that arm's locals to this one.
    int end = lastOffset(arm);
    if (start < 0 || end < 0) {
      return slots;
    }
    table.getRange(start, Integer.MAX_VALUE)
      .filter(v -> v.getStart() >= start && v.getStart() <= end)
      .filter(v -> own.isEmpty() || own.contains(v.getIndex()))
      .forEach(v -> slots.put(v.getIndex(), new int[]{v.getStart(), v.getEnd()}));
    return slots;
  }

  /**
   * True when a local this arm declares is still in the target's table at {@code offset}: its
   * entry closes after the jump, so the arm's block was still open there — the source wrote the
   * {@code break;} inside the brace rather than after it.
   */
  public static boolean declaredScopePast(Statement arm, int offset) {
    if (arm == null || offset < 0) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute table =
      method == null ? null : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    int start = firstOffset(arm);
    int end = lastOffset(arm);
    if (start < 0 || end < 0) {
      return false;
    }
    return table.getRange(start, Integer.MAX_VALUE)
      .anyMatch(v -> v.getStart() >= start && v.getStart() <= end && v.getEnd() > offset);
  }

  /** Last instruction end covered by a statement, or -1. */
  public static int blockEnd(Statement stat) {
    return stat == null ? -1 : lastEnd(stat);
  }

  /**
   * The first local declared at or inside this statement whose target scope ends before the
   * enclosing block does, as {@code {start, end}}, or null. Such a local was declared inside a
   * nested block whose closing brace stood where its scope ends.
   */
  public static int[] nestedBlockScope(Statement stat, int windowEnd, int blockEnd) {
    if (!selector("bareblock") || stat == null) {
      return null;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return null;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return null;
    }
    int start = firstOffset(stat);
    if (start < 0 || windowEnd < start || blockEnd <= 0) {
      return null;
    }
    return table.getRange(start, Integer.MAX_VALUE)
      .filter(v -> v.getStart() >= start && v.getStart() <= windowEnd)
      .filter(v -> v.getEnd() > v.getStart() && v.getEnd() < blockEnd)
      .min(java.util.Comparator.comparingInt(v -> v.getStart()))
      .map(v -> new int[]{v.getStart(), v.getEnd(), v.getIndex()})
      .orElse(null);
  }

  /**
   * True when the target hands this slot to another local at or after that offset: the local
   * that held it ended there, so the source closed a block the printer has no brace for.
   */
  public static boolean slotReusedAfter(int slot, int after) {
    StructMethod method = currentMethod();
    if (method == null || slot < 0 || after < 0) {
      return false;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    return table.getVariables().anyMatch(entry -> entry.getIndex() == slot
      && entry.getStartPC() >= after && entry.getLength() > 0);
  }

  /**
   * True when any statement from {@code from} on still reads the local in this slot: closing a
   * block in front of it would put the read outside the local's scope.
   */
  public static boolean slotUsedFrom(List<Statement> stats, int from, int slot) {
    for (int j = Math.max(0, from); j < stats.size(); j++) {
      Statement stat = stats.get(j);
      java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
      queue.add(stat);
      while (!queue.isEmpty()) {
        Statement cur = queue.poll();
        List<Exprent> exprents = cur.getExprents();
        if (exprents != null) {
          for (Exprent exprent : exprents) {
            for (Exprent part : exprent.getAllExprents(true, true)) {
              if (part instanceof VarExprent var && !var.isStack() && var.getIndex() == slot) {
                return true;
              }
            }
          }
        }
        queue.addAll(cur.getStats());
      }
    }
    return false;
  }

  /** Index of the exprent in this statement whose offsets contain the offset, or -1. */
  public static int exprentAtOffset(Statement stat, int offset) {
    List<Exprent> exprents = stat == null ? null : stat.getExprents();
    if (exprents == null) {
      return -1;
    }
    for (int i = 0; i < exprents.size(); i++) {
      for (Exprent part : exprents.get(i).getAllExprents(true, true)) {
        if (part.bytecode != null && part.bytecode.get(offset)) {
          return i;
        }
      }
    }
    return -1;
  }

  /**
   * True when one of these arms yields: the switch is an expression printed in statement form, and
   * its arms have to cover every input, so a synthesized default cannot be left out.
   */
  public static boolean switchYields(List<Statement> arms) {
    for (Statement arm : arms) {
      if (statementYields(arm)) {
        return true;
      }
    }
    return false;
  }

  private static boolean statementYields(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        // A nested switch owns its own yields.
        if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.SwitchExprent) {
          continue;
        }
        for (Exprent part : exprent.getAllExprents(true, true)) {
          if (part instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.YieldExprent) {
            return true;
          }
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (child instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement) {
        continue;
      }
      if (statementYields(child)) {
        return true;
      }
    }
    return false;
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

  /** The end offset of the statement's last instruction, or -1 when it has no recorded offsets. */
  public static int lastInstructionEnd(Statement statement) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    int start = lastOffsetDeep(statement);
    if (ends == null || start < 0) {
      return -1;
    }
    Integer end = ends.get(start);
    return end == null ? -1 : end;
  }

  /**
   * The greatest instruction start covered by the statement or any statement nested in it, or -1.
   * The recorded bit sets cover every byte of an instruction, so only offsets the scan knows as
   * instruction starts count.
   */
  private static int lastOffsetDeep(Statement statement) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    int max = -1;
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null && ends != null) {
      for (Exprent exprent : exprents) {
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          BitSet bits = inner.bytecode;
          if (bits == null || bits.isEmpty()) {
            continue;
          }
          for (int offset = bits.nextSetBit(0); offset >= 0; offset = bits.nextSetBit(offset + 1)) {
            if (ends.containsKey(offset) && offset > max) {
              max = offset;
            }
          }
        }
      }
    }
    for (Statement child : statement.getStats()) {
      int offset = lastOffsetDeep(child);
      if (offset > max) {
        max = offset;
      }
    }
    return max;
  }

  /**
   * True when a {@code goto} starts exactly where this statement's last instruction ends and lands
   * on {@code target}: the statement's block ended with a jump the source wrote as {@code break;}.
   */
  public static boolean jumpsFromEnd(Statement statement, int target) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (gotos == null || target < 0) {
      return false;
    }
    for (int end : new int[]{lastInstructionEnd(statement), sinkEnd(statement)}) {
      Integer landed = end < 0 ? null : gotos.get(end);
      if (landed != null && landed == target) {
        return true;
      }
    }
    return false;
  }

  /**
   * The end offset of a value sink the printer folded into this statement's last call: a call
   * whose result nothing reads keeps a `pop` of its own, so a jump the source wrote after the
   * statement starts one instruction further than the exprent's own bytes end.
   */
  private static int sinkEnd(Statement statement) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    BitSet sinks = method == null ? null : VALUE_SINKS.get(method);
    int start = statement == null ? -1 : lastOffsetDeep(statement);
    if (ends == null || sinks == null || start < 0) {
      return -1;
    }
    Integer end = ends.get(start);
    if (end == null || !sinks.get(end)) {
      return -1;
    }
    Integer after = ends.get(end);
    return after == null ? -1 : after;
  }

  /** The offset of the goto that starts where this statement's last instruction ends, or -1. */
  public static int tailJumpOffset(Statement statement) {
    int end = lastInstructionEnd(statement);
    if (jumpTargetAt(end) >= 0) {
      return end;
    }
    int sunk = sinkEnd(statement);
    return jumpTargetAt(sunk) >= 0 ? sunk : -1;
  }

  /** The target of the goto that starts where this statement's last instruction ends, or -1. */
  public static int tailJumpTarget(Statement statement) {
    return jumpTargetAt(tailJumpOffset(statement));
  }

  /** The target of the goto starting exactly at this offset, or -1 when none starts there. */
  public static int jumpTargetAt(int offset) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (gotos == null || offset < 0) {
      return -1;
    }
    Integer landed = gotos.get(offset);
    return landed == null ? -1 : landed;
  }

  /**
   * The targets of the switch instruction starting at this offset: the default target first, then
   * the keyed targets in table order (the same order the head's successor edges are stored in), or
   * null when the method recorded no such instruction.
   */
  public static int[] switchTargetsAt(int offset) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, int[]> switches = method == null ? null : SWITCH_TARGETS.get(method);
    return switches == null || offset < 0 ? null : switches.get(offset);
  }

  /** True when {@code target} is where a {@code continue} of an enclosing loop would land. */
  public static boolean enclosingContinueTarget(Statement statement, int target) {
    for (Statement cur = statement == null ? null : statement.getParent(); cur != null; cur = cur.getParent()) {
      if (cur instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop
          && isContinueTarget(loop, target)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the statement can finish without leaving the enclosing block — the Java rule that
   * decides if a {@code break;} appended after it would be reachable code. Conservative where the
   * language is: a loop or switch is assumed to be able to complete normally.
   */
  public static boolean canCompleteNormally(Statement statement) {
    if (statement == null) {
      return true;
    }
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null) {
      if (exprents.isEmpty()) {
        return true;
      }
      Exprent last = exprents.get(exprents.size() - 1);
      return !(last instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit
        && (exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
            || exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.THROW));
    }
    if (statement instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStatement) {
      if (ifStatement.getIfstat() != null && canCompleteNormally(ifStatement.getIfstat())) {
        return true;
      }
      return ifStatement.getElsestat() == null || canCompleteNormally(ifStatement.getElsestat());
    }
    List<Statement> children = statement.getStats();
    if (children.isEmpty()) {
      return true;
    }
    return canCompleteNormally(children.get(children.size() - 1));
  }

  /** True when the statement's own tail already prints an explicit {@code break;} or {@code continue;}. */
  public static boolean printsExplicitJump(Statement statement) {
    Statement last = statement;
    while (true) {
      // The jump may hang off any statement on the tail path: an arm ending in `if (…) { … } else
      // { … }` carries its `break` as the if's own edge, not the last block's.
      for (StatEdge edge : last.getAllSuccessorEdges()) {
        if (edge.explicit && (edge.getType() == StatEdge.TYPE_BREAK || edge.getType() == StatEdge.TYPE_CONTINUE)) {
          return true;
        }
      }
      if (last.getExprents() != null || last.getStats().isEmpty()) {
        return false;
      }
      last = last.getStats().get(last.getStats().size() - 1);
    }
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

  /** First target offset covered by this expression, or -1. */
  public static int firstExprentOffset(Exprent exprent) {
    return firstOffsetOf(exprent);
  }

  /**
   * The end of the innermost local variable scope alive at this offset, or -1. javac ends a catch
   * parameter's scope at the closing brace, so a statement at or past this offset was written
   * outside the block.
   */
  public static int scopeEndAt(int offset) {
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute table =
      method == null ? null : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null || offset < 0) {
      return -1;
    }
    int bestStart = -1;
    int bestEnd = -1;
    for (StructLocalVariableTableAttribute.LocalVariable var : table.getVariables().toList()) {
      if (var.getStart() <= offset && offset < var.getEnd() && var.getStart() > bestStart) {
        bestStart = var.getStart();
        bestEnd = var.getEnd();
      }
    }
    return bestEnd;
  }

  /**
   * True when another expression in this method prints an exit at the same offset: the decompiler
   * copied a join's return into a block while the join still prints it.
   */
  public static boolean exitPrintedElsewhere(Statement root, Exprent exit) {
    if (root == null || exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return false;
    }
    int offset = exit.bytecode.nextSetBit(0);
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    queue.add(root);
    while (!queue.isEmpty()) {
      Statement cur = queue.poll();
      List<Exprent> exprents = cur.getExprents();
      if (exprents != null) {
        for (Exprent candidate : exprents) {
          if (candidate == exit) {
            continue;
          }
          for (Exprent inner : candidate.getAllExprents(true, true)) {
            if (inner instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent
                && inner.bytecode != null && inner.bytecode.get(offset)) {
              return true;
            }
          }
        }
      }
      queue.addAll(cur.getStats());
    }
    return false;
  }

  /**
   * The first instruction offset the statement covers, counting the condition exprents a compound
   * statement holds itself: an if whose test is the first thing it runs starts at the test, not at
   * its first child block.
   */
  public static int startOffset(Statement statement) {
    java.util.BitSet bits = new java.util.BitSet();
    statement.getOffset(bits);
    return bits.nextSetBit(0);
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

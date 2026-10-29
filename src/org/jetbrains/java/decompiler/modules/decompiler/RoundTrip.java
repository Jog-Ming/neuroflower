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
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructClass;
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
  /** A labelled block being printed as an else-if chain; its breaks are implicit in the source. */
  private static final ThreadLocal<Statement> HIDDEN_CLOSURE = new ThreadLocal<>();
  /** A statement already printed as part of a wider shape; printing it again would duplicate it. */
  private static final ThreadLocal<Statement> SKIPPED_STATEMENT = new ThreadLocal<>();
  /** An if of an else-if chain whose closing brace the chain prints on the `else` line. */
  private static final ThreadLocal<Statement> OPEN_ARM = new ThreadLocal<>();
  private static final ThreadLocal<Boolean> ARM_CLOSED = new ThreadLocal<>();
  private static final java.util.Map<StructMethod, BitSet> VOID_RETURNS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Per slot, the stores the local table gives no row to: a temporary's, and a pattern's own. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, java.util.List<int[]>>> TEMP_STORES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Instruction end offset by start offset; the live sequence is released before printing. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> INSTRUCTION_ENDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** The instruction that ends at an offset, keyed by that end: an arm's last instruction. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> INSTRUCTION_BY_END = new java.util.concurrent.ConcurrentHashMap<>();
  /** Per method: handler bytecode offset -> first offset after its protected range. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> HANDLER_ENDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Per method: handler offset -> the skip-goto's destination, where code after the try starts. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> TRY_EXIT_TARGETS = new java.util.concurrent.ConcurrentHashMap<>();
  /** The goto behind the last printed continue-else, for the line alignment. */
  private static final ThreadLocal<int[]> CONTINUE_ELSE_SITE = ThreadLocal.withInitial(() -> new int[]{-1});
  /** The goto behind the last printed continue that a try-with-resources close stands before. */
  private static final ThreadLocal<int[]> CONTINUE_CLOSE_SITE = ThreadLocal.withInitial(() -> new int[]{-1});
  /** Start offsets of {@code close:()V} invocations: the synthetic end of a try-with-resources. */
  private static final java.util.Map<StructMethod, BitSet> CLOSE_CALLS = new java.util.concurrent.ConcurrentHashMap<>();
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
  /** The method's first instruction start offset: the entry a dominance check starts from. */
  private static final java.util.Map<StructMethod, Integer> METHOD_ENTRY = new java.util.concurrent.ConcurrentHashMap<>();
  /** Instructions that do not fall through: returns and {@code athrow}. */
  private static final java.util.Map<StructMethod, BitSet> NO_FALLTHROUGH = new java.util.concurrent.ConcurrentHashMap<>();
  /** Starts of the {@code pop} that discards a void call's value: the statement ends past it. */
  private static final java.util.Map<StructMethod, BitSet> POP_SITES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Protected ranges as {@code {from start, to end (exclusive or MAX_VALUE), handler start}}. */
  private static final java.util.Map<StructMethod, java.util.List<int[]>> EXCEPTION_RANGES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Store offsets that open a row taking over an earlier local's slot: a new declaration. */
  private static final java.util.Map<StructMethod, BitSet> HANDOVER_STARTS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Handover stores a printed brace just closed the previous local before: declare them. */
  private static final ThreadLocal<java.util.Map<StructMethod, BitSet>> SPLIT_DECLARATIONS =
    ThreadLocal.withInitial(java.util.concurrent.ConcurrentHashMap::new);
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
  /** Return instructions of a try-shaped `store S; goto M` / `M: load S; ret`, by the return's start. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, int[]>> TRY_RETURN_STORES = new java.util.concurrent.ConcurrentHashMap<>();
  /** Switch arms that held a for-each's update: the label the source never wrote. */
  private static final java.util.Set<Statement> LOOP_UPDATE_ARMS = java.util.concurrent.ConcurrentHashMap.newKeySet();
  /** First offsets of empty catch bodies, by offset, with the protected range's start. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> EMPTY_CATCHES = new java.util.concurrent.ConcurrentHashMap<>();

  private RoundTrip() {}

  /** Remember where a method's void returns are; the instruction sequence is gone by print time. */
  public static void recordMethod(StructClass cl, StructMethod method, FullInstructionSequence seq) {
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
    BitSet noFallThrough = new BitSet();
    BitSet popSites = new BitSet();
    BitSet closeCalls = new BitSet();
    for (int i = 0; i < seq.length(); i++) {
      Instruction instr = seq.getInstr(i);
      ends.put(instr.startOffset, instr.startOffset + instr.length);
      if (instr.opcode >= CodeConstants.opc_invokevirtual && instr.opcode <= CodeConstants.opc_invokeinterface) {
        // The synthetic close javac appends at the end of a try-with-resources body: the branch
        // that skips it lands past the goto the close's normal path reaches.
        org.jetbrains.java.decompiler.struct.consts.LinkConstant called =
          cl.getPool().getLinkConstant(instr.operand(0));
        if ("close".equals(called.elementname) && "()V".equals(called.descriptor)) {
          closeCalls.set(instr.startOffset);
        }
      }
      if (instr.opcode == CodeConstants.opc_pop || instr.opcode == CodeConstants.opc_pop2) {
        popSites.set(instr.startOffset);
      }
      if (instr.opcode >= CodeConstants.opc_ireturn && instr.opcode <= CodeConstants.opc_return
        || instr.opcode == CodeConstants.opc_athrow || instr.opcode == CodeConstants.opc_ret) {
        noFallThrough.set(instr.startOffset);
      }
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
    java.util.Map<Integer, java.util.List<int[]>> tempStores = new java.util.HashMap<>();
    org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute storeRows =
      method.getLocalVariableAttr();
    if (storeRows != null && !storeSites.isEmpty()) {
      for (java.util.Map.Entry<Integer, BitSet> entry : storeSites.entrySet()) {
        for (int offset = entry.getValue().nextSetBit(0); offset >= 0;
             offset = entry.getValue().nextSetBit(offset + 1)) {
          boolean named = false;
          for (org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable row
              : storeRows.getVariables().toList()) {
            if (row.getIndex() == entry.getKey() && row.getStart() <= offset && row.getEnd() > offset) {
              named = true;
              break;
            }
          }
          if (!named) {
            Integer instructionEnd = ends.get(offset);
            tempStores.computeIfAbsent(entry.getKey(), k -> new java.util.ArrayList<>())
              .add(new int[]{offset, instructionEnd == null ? offset + 1 : instructionEnd});
          }
        }
      }
    }
    TEMP_STORES.put(method, tempStores);
    CLOSE_CALLS.put(method, closeCalls);
    VOID_RETURNS.put(method, returns);
    VALUE_SINKS.put(method, sinks);
    CONTINUE_GUARDS.put(method, guards);
    CONTINUE_SITES.put(method, sites);
    CONTINUE_ELSE_GUARDS.put(method, elseGuards);
    CONTINUE_ELSE_SITES.put(method, elseSites);
    BRANCHES.put(method, branches);
    BRANCH_TARGETS.put(method, branchTargets);
    INSTRUCTION_ENDS.put(method, ends);
    INSTRUCTION_BY_END.put(method, prevByEnd);
    java.util.Map<Integer, Integer> handlerEnds = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> tryExits = new java.util.HashMap<>();
    java.util.List<int[]> exceptionRanges = new java.util.ArrayList<>();
    org.jetbrains.java.decompiler.code.ExceptionTable table = seq.exceptionTable();
    if (table != null) {
      for (org.jetbrains.java.decompiler.code.ExceptionHandler handler : table.getHandlers()) {
        int handlerIndex = handler.handler();
        int toIndex = handler.to();
        if (handler.from() >= 0 && handler.from() < seq.length()
          && handlerIndex >= 0 && handlerIndex < seq.length()) {
          // Every instruction of the protected range may reach the handler by an exception; a
          // dominance check has to see that edge, or a local assigned inside a try would seem to
          // precede whatever the catch runs.
          exceptionRanges.add(new int[]{
            seq.getInstr(handler.from()).startOffset,
            toIndex >= 0 && toIndex < seq.length() ? seq.getInstr(toIndex).startOffset : Integer.MAX_VALUE,
            seq.getInstr(handlerIndex).startOffset
          });
        }
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
        // The skip-goto's destination is where the code after the try/catch begins. A protected
        // range can stop just before its own trailing `return`, leaving the skip-goto one
        // instruction further; it is the last goto before the handler that jumps past it.
        int skipTarget = -1;
        if (exit.opcode == CodeConstants.opc_goto || exit.opcode == CodeConstants.opc_goto_w) {
          skipTarget = exit.startOffset + exit.operand(0);
        } else {
          int handlerStart = seq.getInstr(handlerIndex).startOffset;
          for (int i = toIndex; i < handlerIndex; i++) {
            Instruction candidate = seq.getInstr(i);
            if ((candidate.opcode == CodeConstants.opc_goto || candidate.opcode == CodeConstants.opc_goto_w)
                && candidate.startOffset + candidate.operand(0) > handlerStart) {
              skipTarget = candidate.startOffset + candidate.operand(0);
            }
          }
        }
        if (skipTarget >= 0) {
          tryExits.put(seq.getInstr(handlerIndex).startOffset, skipTarget);
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
    TRY_EXIT_TARGETS.put(method, tryExits);
    // javac writes a catch parameter's table entry for every non-empty catch body. Its absence at
    // the first instruction after the store marks a body the source left empty; the printer sees
    // only the statement the decompiler folded in there, so remember where such a body starts.
    java.util.Map<Integer, Integer> emptyCatches = new java.util.HashMap<>();
    if (table != null && method.getLocalVariableAttr() != null) {
      StructLocalVariableTableAttribute catches = method.getLocalVariableAttr();
      for (org.jetbrains.java.decompiler.code.ExceptionHandler handler : table.getHandlers()) {
        int handlerIndex = handler.handler();
        if (handler.exceptionClass() == null || handlerIndex < 0 || handlerIndex >= seq.length()) {
          continue;
        }
        Instruction store = seq.getInstr(handlerIndex);
        if (store.opcode != CodeConstants.opc_astore) {
          continue;
        }
        int body = store.startOffset + store.length;
        if (catches.matchingVars(store.operand(0), body).findFirst().isPresent()) {
          continue;
        }
        int from = handler.from() < seq.length() ? seq.getInstr(handler.from()).startOffset : -1;
        emptyCatches.put(body, from);
      }
    }
    EMPTY_CATCHES.put(method, emptyCatches);
    // A try body that ends `store S; goto M` with `M: load S; ret` keeps the value in a variable the
    // source declared outside the block: the target's table has two ranges for the slot, one ending
    // where the handler starts and one covering the load and the return. A single range is the
    // source's own `v = expr; return …` inside the try instead.
    java.util.Map<Integer, int[]> tryReturns = new java.util.HashMap<>();
    StructLocalVariableTableAttribute lvt = method.getLocalVariableAttr();
    if (table != null && lvt != null) {
      for (org.jetbrains.java.decompiler.code.ExceptionHandler handler : table.getHandlers()) {
        int toIndex = handler.to();
        int handlerIndex = handler.handler();
        if (toIndex <= 0 || toIndex >= seq.length() || handlerIndex < 0 || handlerIndex >= seq.length()) {
          continue;
        }
        Instruction skip = seq.getInstr(toIndex);
        if (skip.opcode != CodeConstants.opc_goto && skip.opcode != CodeConstants.opc_goto_w) {
          continue;
        }
        Instruction store = seq.getInstr(toIndex - 1);
        if (!isStore(store.opcode)) {
          continue;
        }
        int slot = variableIndex(store);
        int target = skip.startOffset + skip.operand(0);
        Integer loadIndex = seq.offsetToIndex().get(target);
        if (loadIndex == null || loadIndex + 1 >= seq.length()) {
          continue;
        }
        Instruction load = seq.getInstr(loadIndex);
        Instruction ret = seq.getInstr(loadIndex + 1);
        if (!isLoad(load.opcode) || variableIndex(load) != slot
          || ret.opcode < CodeConstants.opc_ireturn || ret.opcode > CodeConstants.opc_areturn) {
          continue;
        }
        int handlerStart = seq.getInstr(handlerIndex).startOffset;
        int retEnd = ret.startOffset + ret.length;
        org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable first = null;
        int matches = 0;
        for (org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable var : lvt.getVariables().toList()) {
          if (var.getIndex() != slot) {
            continue;
          }
          if (var.getStart() == skip.startOffset && var.getEnd() == handlerStart) {
            first = var;
          } else if (var.getStart() == target && var.getEnd() == retEnd && first != null
            && first.getName().equals(var.getName())) {
            matches = 2;
          }
        }
        if (matches == 2) {
          tryReturns.put(ret.startOffset, new int[]{slot, load.startOffset, ret.startOffset});
        }
      }
    }
    TRY_RETURN_STORES.put(method, tryReturns);
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
    METHOD_ENTRY.put(method, seq.length() == 0 ? -1 : seq.getInstr(0).startOffset);
    NO_FALLTHROUGH.put(method, noFallThrough);
    POP_SITES.put(method, popSites);
    EXCEPTION_RANGES.put(method, exceptionRanges);
    GOTO_TARGETS.put(method, gotos);
    SWITCH_TARGETS.put(method, switches);
    BRANCH_STARTS.put(method, branchStarts);
    RETURN_STORES.put(method, returnStores);
    DUP_STORES.put(method, dupStores);
    STORE_SITES.put(method, storeSites);
    LOAD_SITES.put(method, loadSites);
    STORE_SLOTS.put(method, storeSlots);
    HANDOVER_STARTS.put(method, handoverStarts(method));
  }

  /**
   * The store offsets that open a slot's next table row while every path to them passes the
   * previous row's declaration: each is a local the source declared in a block of its own.
   */
  private static BitSet handoverStarts(StructMethod method) {
    BitSet starts = new BitSet();
    if (!selector("bareblock")) {
      return starts;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return starts;
    }
    List<LocalVariable> rows = table.getVariables().toList();
    for (LocalVariable first : rows) {
      if (first.getEnd() <= first.getStart()) {
        continue;
      }
      for (LocalVariable second : rows) {
        if (handoverPair(method, first, second)) {
          starts.set(second.getStart());
        }
      }
    }
    return starts;
  }

  /**
   * The slot a value return's preceding load reads and the instruction store writes. -1 unless the
   * target's last three instructions before the return are exactly {@code store N; load N; ret}.
   */
  /**
   * The try-shaped `store S; goto M` / `M: load S; return` this exit belongs to, or null:
   * {@code {slot, load offset, return offset}}.
   */
  public static int[] tryStoredBeforeReturn(BitSet offsets) {
    StructMethod method = currentMethod();
    if (method == null || offsets == null || !selector("tryreturn")) {
      return null;
    }
    java.util.Map<Integer, int[]> stores = TRY_RETURN_STORES.get(method);
    if (stores == null) {
      return null;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      int[] info = stores.get(offset);
      if (info != null) {
        return info;
      }
    }
    return null;
  }

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
    return opensTrailingBlock(firstTail, -1);
  }

  /**
   * The same, for a trailing block that ends where the enclosing statement does instead of at
   * the method's close: a guard's else arm inside an enclosing else ends at that arm's brace.
   */
  public static boolean opensTrailingBlock(Statement firstTail, int boundaryEnd) {
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
    if (first == null) {
      return false;
    }
    boolean boundary = first.getEnd() == boundaryEnd && boundaryEnd >= 0;
    if (boundary) {
      // The tail's block closed before an enclosing block local that was written later and lives
      // longer: only then did the source brace the tail inside the arm. A block-scoped local is
      // written before the parameters; the method body's own locals are written after them and
      // outlive every arm, so they are not evidence about the arm's braces.
      boundary = false;
      for (LocalVariable other : vars) {
        if (other.getStart() > 0 && other.getOrder() > first.getOrder()
            && other.getOrder() < paramsStart && other.getEnd() >= first.getEnd()) {
          boundary = true;
          break;
        }
      }
    }
    return first.getStart() > 0 && first.getOrder() >= 0
        && first.getOrder() < paramsStart
        && (first.getEnd() == maxEnd || boundary);
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
    if (first == null || first.getStart() <= 0 || first.getOrder() < 0) {
      return false;
    }
    if (first.getOrder() > paramsEnd) {
      return true;
    }
    // A local declared in a nested block closes when that block does, so every one of its rows is
    // written before the parameter group. A local declared in the method body closes with it, and
    // its last alive range is written after the parameters. The declaration exprent carries only
    // one row — the first store's — and a local assigned in both arms of an if has an early row
    // there even when the declaration stood outside the branch: the row the table writes last is
    // the one that proves the method scope.
    for (LocalVariable v : vars) {
      if (v.getOrder() > paramsEnd && v.getIndex() == first.getIndex()
          && v.getName().equals(first.getName()) && v.getDescriptor().equals(first.getDescriptor())) {
        return true;
      }
    }
    return false;
  }

  private static boolean spansMethod(List<LocalVariable> vars, int maxEnd) {
    for (LocalVariable v : vars) {
      if (v.getStart() == 0 && v.getEnd() == maxEnd) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when the statement's first local lives in the enclosing block's scope rather than a block
   * of its own. javac writes a local variable's table entry when its scope closes, so a local
   * nested in a block is written before every local of the enclosing block; one written after them
   * shares the enclosing block.
   */
  public static boolean sharesEnclosingScope(Statement stat, int enclosingStart) {
    if (!selector("switchjoin")) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null || enclosingStart < 0) {
      return false;
    }
    LocalVariable local = firstDefinedLvt(stat);
    if (local == null || local.getOrder() < 0) {
      return false;
    }
    // Only a local of the block our own declaration lives in closes with it; parameters and
    // method-scope locals are written after both and say nothing about the nesting.
    boolean anyEnclosing = false;
    for (LocalVariable var : table.getVariables().toList()) {
      if (var.getEnd() == local.getEnd() && var.getOrder() != local.getOrder()
          && var.getStart() <= enclosingStart) {
        if (var.getOrder() > local.getOrder()) {
          return false;
        }
        anyEnclosing = true;
      }
    }
    return anyEnclosing;
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

  /** Join offsets of the arms an enclosing print is emitting as an else, innermost last. */
  private static final ThreadLocal<java.util.ArrayDeque<Integer>> JOIN_PRINTS =
    ThreadLocal.withInitial(java.util.ArrayDeque::new);

  /** Tells a nested print that the code after its enclosing else starts at this offset. */
  public static void pushJoinOffset(int offset) {
    JOIN_PRINTS.get().push(offset);
  }

  public static void popJoinOffset() {
    java.util.ArrayDeque<Integer> stack = JOIN_PRINTS.get();
    if (!stack.isEmpty()) {
      stack.poll();
    }
  }

  /** The join offset the enclosing else print reaches, or -1. */
  public static int joinOffset() {
    Integer top = JOIN_PRINTS.get().peek();
    return top == null ? -1 : top;
  }

  /**
   * True when this block is a copy of the method's final return: the return instruction is the
   * method's last, and the same instruction is printed by the statement the tree prints last.
   * The arm's copy stands for the jump the source took there; printing it would emit a second
   * areturn, so the arm falls out to the return the tail prints.
   */
  public static boolean isTailReturnCopy(Statement stat) {
    return tailReturnCopyOffset(stat) >= 0;
  }

  /** True when this exprent is a return at the method's last instruction. */
  public static boolean isMethodFinalReturn(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || !(exprent instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN || exprent.bytecode == null
        || exprent.bytecode.isEmpty()) {
      return false;
    }
    Integer last = LAST_INSTRUCTION.get(method);
    return last != null && exprent.bytecode.previousSetBit(Integer.MAX_VALUE) == last;
  }

  /** The return offset when this block is a copy of the method's final return, or -1. */
  public static int tailReturnCopyOffset(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null || stat.getExprents() == null) {
      return -1;
    }
    List<Exprent> exprents = stat.getExprents();
    if (exprents.isEmpty()) {
      return -1;
    }
    Exprent last = exprents.get(exprents.size() - 1);
    if (!(last instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit)
        || exit.getExitType() != org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
        || exit.bytecode == null) {
      return -1;
    }
    int start = exit.bytecode.nextSetBit(0);
    int ret = exit.bytecode.previousSetBit(Integer.MAX_VALUE);
    Integer methodLast = LAST_INSTRUCTION.get(method);
    if (start < 0 || ret < 0 || methodLast == null || ret != methodLast) {
      return -1;
    }
    Statement root = stat;
    while (root.getParent() != null) {
      root = root.getParent();
    }
    Statement tail = lastPrinted(root);
    if (tail == stat) {
      return -1;
    }
    BitSet tailOffsets = new BitSet();
    tail.getOffset(tailOffsets);
    int join = firstOffset(stat);
    return tailOffsets.get(start) && join >= 0 ? join : -1;
  }

  /** The statement the printer reaches last: the last printed child, through nested statements. */
  private static Statement lastPrinted(Statement stat) {
    while (true) {
      List<Statement> stats = stat.getStats();
      if (stats.isEmpty()) {
        return stat;
      }
      Statement next = null;
      for (int i = stats.size() - 1; i >= 0; i--) {
        if (!printsNothing(stats.get(i))) {
          next = stats.get(i);
          break;
        }
      }
      if (next == null) {
        return stat;
      }
      stat = next;
    }
  }

  /**
   * The first offset the enclosing flow prints after this statement, or -1 when it cannot be told.
   * Walking up through sequences and if arms: a statement falling out of an arm runs whatever
   * follows the if. A loop or switch boundary stops the walk — falling out of those goes
   * somewhere else than the next statement.
   */
  public static int printedAfter(Statement stat) {
    Statement cur = stat;
    while (cur != null) {
      Statement parent = cur.getParent();
      if (parent == null) {
        return -1;
      }
      List<Statement> siblings = parent.getStats();
      int index = -1;
      for (int i = 0; i < siblings.size(); i++) {
        if (siblings.get(i) == cur) {
          index = i;
          break;
        }
      }
      if (index < 0) {
        return -1;
      }
      for (int k = index + 1; k < siblings.size(); k++) {
        if (!printsNothing(siblings.get(k))) {
          return firstOffset(siblings.get(k));
        }
      }
      if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement
          || parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement) {
        cur = parent;
        continue;
      }
      return -1;
    }
    return -1;
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
    // An arm's entry point is the first instruction the statement covers, its own head test
    // included: a branch to an arm lands on the arm's condition, not on the code behind it.
    int thenStart = statementOffset(thenArm);
    int elseStart = statementOffset(elseArm);
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

  /**
   * True when the target proves the source's then arm was empty: the head's last branch enters
   * the arm on the printed condition being true, and the instruction right after it is a goto
   * that leaves the arm. javac lays a written {@code if (!C) { } else <arm>} out that way; the
   * plain {@code if (C) { <arm> }} branches the other way round and puts no jump between the
   * branch and the arm's first instruction. The tree dropped the empty arm and kept the source's
   * else as the then.
   */
  public static boolean emptyThenArm(Exprent head, Statement arm) {
    if (!selector("emptythen") || !swapIfArmsByLastTarget(head, arm)) {
      return false;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    BitSet offsets = head.bytecode;
    if (gotos == null || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer after = gotos.get(offsets.length());
    if (after == null || after == lastBranchTarget(head)) {
      return false;
    }
    // The jump has to skip the arm: a target inside it would be the arm's own flow.
    int armStart = statementOffset(arm);
    int armEnd = lastEnd(arm);
    return armStart >= 0 && armEnd >= armStart && (after < armStart || after >= armEnd);
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

  /** The first offset a statement covers, its head exprents included, or -1. */
  private static int rangeStart(Statement statement) {
    BitSet bits = new BitSet();
    statement.getOffset(bits);
    return bits.isEmpty() ? -1 : bits.nextSetBit(0);
  }

  /**
   * The target's proof that the source wrote a negated pattern guard around the arm at T:
   * {@code instanceof; ifeq/ifne T; [load;] checkcast; astore; goto U} with T exactly the
   * instruction after that goto, U the code after the whole if. The goto is the fact that
   * separates this from the positive test {@code if (x instanceof T t) { … } rest}, where the
   * pattern store's path falls straight into the arm and no jump skips anything. The arm at T
   * also has to leave the test — a return/athrow of its own, or a jump past U — or it would run
   * into the code the source ran after the if.
   *
   * <p>Returns the offset of the arm's last instruction, or -1 when the class file is not this
   * shape.
   */
  public static int negatedPatternGuard(Exprent head, Statement thenArm, Statement guardArm) {
    if (!selector("patternguard") || !(head instanceof IfExprent ifHead)) {
      return -1;
    }
    StructMethod method = currentMethod();
    if (method == null || thenArm == null || guardArm == null) {
      return -1;
    }
    Exprent condition = ifHead.getCondition();
    if (condition == null || !declaresPatternVariable(condition)) {
      return -1;
    }
    // The tree has to print the test positively: a test that is already negated is the source's
    // own polarity, and flipping it here would print the double negation as a positive test.
    if (condition instanceof FunctionExprent function
        && function.getFuncType() == FunctionExprent.FunctionType.BOOL_NOT) {
      return -1;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    BitSet noFallThrough = NO_FALLTHROUGH.get(method);
    if (ends == null || gotos == null || noFallThrough == null) {
      return -1;
    }
    int target = lastBranchTarget(ifHead.bytecode);
    int guardStart = rangeStart(guardArm);
    int thenStart = rangeStart(thenArm);
    if (target < 0 || target != guardStart || thenStart <= target) {
      return -1;
    }
    boolean skips = false;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      Integer end = ends.get(entry.getKey());
      if (end != null && end == guardStart && entry.getValue() == thenStart) {
        skips = true;
        break;
      }
    }
    if (!skips) {
      return -1;
    }
    int exit = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : ends.entrySet()) {
      if (entry.getValue() == thenStart) {
        exit = entry.getKey();
        break;
      }
    }
    if (exit < 0) {
      return -1;
    }
    if (noFallThrough.get(exit)) {
      return exit;
    }
    Integer merge = gotos.get(exit);
    return merge != null && merge >= thenStart ? exit : -1;
  }

  /** Whether the instruction at this offset is a void return, which prints as {@code return;}. */
  public static boolean isVoidReturn(int offset) {
    StructMethod method = currentMethod();
    BitSet returns = method == null ? null : VOID_RETURNS.get(method);
    return returns != null && returns.get(offset);
  }

  /**
   * The offset of the void return whose instruction ends exactly where {@code end} begins, or -1.
   * An arm that falls through to the code printed next ends with this instruction in the target;
   * the writer folded the return into the method's end and dropped it from the arm.
   */
  public static int voidReturnEndingAt(int end) {
    StructMethod method = currentMethod();
    if (method == null || end < 0) {
      return -1;
    }
    java.util.Map<Integer, Integer> byEnd = INSTRUCTION_BY_END.get(method);
    BitSet returns = VOID_RETURNS.get(method);
    Integer start = byEnd == null ? null : byEnd.get(end);
    return start != null && returns != null && returns.get(start) ? start : -1;
  }

  /** Whether the instruction at this offset ends the path: a return, a throw, or a ret. */
  public static boolean exitsAt(int offset) {
    StructMethod method = currentMethod();
    BitSet ends = method == null ? null : NO_FALLTHROUGH.get(method);
    return ends != null && ends.get(offset);
  }

  /**
   * Pins a synthesized line to the target instruction it reproduces. The mapping carries the class
   * and method names: the writer records a method's removed returns under no class so that every
   * one of them lands on the method's last line, and that record would otherwise overwrite this
   * one and undo the alignment.
   */
  public static void mapSynthesizedLine(org.jetbrains.java.decompiler.util.TextBuffer line, int offset) {
    StructMethod method = currentMethod();
    org.jetbrains.java.decompiler.struct.StructClass cl =
      DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
    if (method == null || cl == null) {
      return;
    }
    line.addBytecodeMappingAt(0, offset, cl.qualifiedName,
      org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(method.getName(), method.getDescriptor()));
  }

  /** The destination of the first conditional branch inside the head's offsets, or -1. */
  public static int firstBranchTarget(Exprent head) {
    StructMethod method = currentMethod();
    BitSet bytecode = head == null ? null : head.bytecode;
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    if (ends == null || targets == null || bytecode == null) {
      return -1;
    }
    int first = -1;
    int bestStart = Integer.MAX_VALUE;
    for (int offset = bytecode.nextSetBit(0); offset >= 0; offset = bytecode.nextSetBit(offset + 1)) {
      Integer end = ends.get(offset);
      if (end != null && targets.containsKey(end) && offset < bestStart) {
        bestStart = offset;
        first = targets.get(end);
      }
    }
    return first;
  }

  /**
   * True when an if the tree prints as {@code if (C) continue;} at the end of its loop body is
   * really the source's {@code if (!C) break;}. A written continue sends the condition's first
   * test back to the loop's head; the target sends it to the statement past the loop, and the
   * guard pair at the condition's end leaves by that same break. Only a condition whose top-level
   * connective is {@code &&} has that layout, and the fall-through after the if has to reach the
   * loop's end so the negated test skips nothing a continue would not.
   */
  public static boolean breakGuardByTarget(Exprent head, Statement around) {
    if (!selector("breakguard") || !(head instanceof IfExprent ifHead) || around == null) {
      return false;
    }
    if (currentMethod() == null || lastAtomUnderOr(ifHead.getCondition(), false)) {
      return false;
    }
    int firstTarget = firstBranchTarget(ifHead);
    return firstTarget >= 0 && targetBreaks(firstTarget, around) && reachesLoopEnd(around);
  }

  /**
   * True when control falling out of this statement runs nothing else on the way to the loop's
   * back edge: every enclosing sequence has it last (empty blocks aside), and an enclosing if
   * converges after itself whichever arm ran, so the arm it sits in only has to end at the if.
   */
  public static boolean reachesLoopEnd(Statement stat) {
    Statement cur = stat;
    for (Statement parent = cur.getParent(); parent != null; parent = cur.getParent()) {
      if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement) {
        return true;
      }
      if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement sequence) {
        java.util.List<Statement> stats = sequence.getStats();
        int last = stats.size() - 1;
        while (last >= 0 && printsNothing(stats.get(last))) {
          last--;
        }
        if (last < 0 || stats.get(last) != cur) {
          return false;
        }
      } else if (!(parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement)) {
        return false;
      }
      cur = parent;
    }
    return false;
  }

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
   * True when the target proves the source wrote a break guard around this arm: the condition's
   * last branch enters the arm, and the instruction right after that branch is an unconditional
   * jump to the break's destination. javac lays a written {@code if (!C) break; arm} out that way;
   * the plain {@code if (C) { arm } break;} branches past the arm to the break instead.
   */
  public static boolean breakGuardEntersArm(Exprent head, Statement arm, Statement breakTarget) {
    if (!selector("breakarm") || !(head instanceof IfExprent ifHead) || arm == null || breakTarget == null) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    BitSet offsets = ifHead.bytecode;
    int armStart = statementOffset(arm);
    int breakStart = statementOffset(breakTarget);
    if (targets == null || gotos == null || offsets == null || offsets.isEmpty()
        || armStart < 0 || breakStart < 0) {
      return false;
    }
    Integer target = targets.get(offsets.length());
    Integer after = gotos.get(offsets.length());
    return target != null && target == armStart && after != null && after == breakStart;
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
          // A comparison the decompiler still holds as `__dcmpl__(a, b) > 0` is javac's single
          // `dcmpl; if<op>` on the sign, not a two-operand int compare: the result of a lcmp/fcmp/
          // dcmp tested against the literal 0 keeps the wide comparison's opcode.
          boolean cmpZero = isCmpResult(function.getLstOperands().get(0), function.getLstOperands().get(1))
            || isCmpResult(function.getLstOperands().get(1), function.getLstOperands().get(0));
          boolean ints = !cmpZero && isIntegerFamily(left) && isIntegerFamily(right);
          // long/float/double compare through lcmp/fcmp and then branch on the int result.
          boolean wide = cmpZero
            || (left.typeFamily == TypeFamily.LONG && right.typeFamily == TypeFamily.LONG)
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

  /**
   * True when {@code value} is a {@code lcmp}/{@code fcmp}/{@code dcmp} call and {@code other} is
   * the literal int 0: javac keeps the compare's result on the stack and branches on its sign, so
   * the test is the wide comparison's, not an int compare of two values.
   */
  private static boolean isCmpResult(Exprent value, Exprent other) {
    if (!(value instanceof FunctionExprent call) || !(other instanceof ConstExprent constant)
        || !(constant.getValue() instanceof Integer zero) || zero != 0) {
      return false;
    }
    return switch (call.getFuncType()) {
      case LCMP, FCMPL, FCMPG, DCMPL, DCMPG -> true;
      default -> false;
    };
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

  /**
   * The target's source line for the first instruction the exprent covers, or the line of the
   * first operand that carries one. A merged condition (two tests joined into one {@code &&}) is a
   * FunctionExprent the rewrite passes built without its own instruction range, but its operands
   * still carry the lines the source gave them, and a condition's first operand begins it.
   */
  public static int sourceLineDeep(Exprent exprent) {
    int line = sourceLine(exprent);
    if (line >= 0 || exprent == null) {
      return line;
    }
    for (Exprent child : exprent.getAllExprents(true)) {
      line = sourceLine(child);
      if (line >= 0) {
        return line;
      }
    }
    return -1;
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
   * The index in {@code exprents} where the loop's update block starts, or -1 when the target
   * records no proof. javac sends every {@code continue} inside the loop to the first instruction
   * of the update block, and the scan records those jumps; an exprent that starts exactly where a
   * recorded continue lands begins the source's for-update, so it and every exprent after it
   * belong in the header rather than in the body.
   */
  public static int updateBlockStart(Statement loop, java.util.List<Exprent> exprents) {
    if (!selector("forupdate")) {
      return -1;
    }
    StructMethod method = currentMethod();
    if (method == null || loop == null || exprents == null || exprents.size() < 2) {
      return -1;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    if (guards == null || guards.isEmpty()) {
      return -1;
    }
    BitSet range = new BitSet();
    loop.getOffset(range);
    int start = range.nextSetBit(0);
    int end = range.length();
    if (start < 0) {
      return -1;
    }
    java.util.Set<Integer> targets = new java.util.HashSet<>(guards.values());
    for (int k = 0; k < exprents.size(); k++) {
      Exprent exprent = exprents.get(k);
      if (exprent.bytecode == null || exprent.bytecode.isEmpty()) {
        continue;
      }
      int offset = exprent.bytecode.nextSetBit(0);
      if (offset >= start && offset < end && targets.contains(offset)) {
        return k;
      }
    }
    return -1;
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
   * True when the target's line table puts this increment on the loop head's own line, proving the
   * source wrote it in the for header. The two forms compile to the same instructions, so only the
   * table separates them: a header's update carries the header's line, a body statement its own.
   * This is the hoisting direction only — a distinct line is handled where the update already sits
   * in the body, and the demotion of an existing for is never decided here.
   */
  public static boolean updateOnHeaderLine(Exprent condition, Exprent update) {
    if (!selector("forheadline")) {
      return false;
    }
    if (!(update instanceof FunctionExprent function)) {
      return false;
    }
    FunctionExprent.FunctionType type = function.getFuncType();
    if (type != FunctionExprent.FunctionType.PPI && type != FunctionExprent.FunctionType.IPP
        && type != FunctionExprent.FunctionType.MMI && type != FunctionExprent.FunctionType.IMM) {
      return false;
    }
    int updateLine = sourceLine(update);
    int conditionLine = sourceLine(condition);
    return updateLine >= 0 && conditionLine >= 0 && updateLine == conditionLine;
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

  /** The first handler offset of the try/catch whose body is being printed right now, or -1. */
  private static final ThreadLocal<Integer> TRY_BODY_HANDLER = new ThreadLocal<>();
  /** Returns a try body's print hands to the try, to print after its catch, in print order. */
  private static final ThreadLocal<java.util.List<Exprent>> DEFERRED_TRY_RETURNS = new ThreadLocal<>();

  /** Marks the try/catch whose body is about to print; returns the previous handler offset. */
  public static Integer pushTryBody(int handlerOffset) {
    Integer previous = TRY_BODY_HANDLER.get();
    if (handlerOffset >= 0) {
      TRY_BODY_HANDLER.set(handlerOffset);
    }
    return previous;
  }

  public static void popTryBody(Integer previous) {
    if (previous == null) {
      TRY_BODY_HANDLER.remove();
    }
    else {
      TRY_BODY_HANDLER.set(previous);
    }
  }

  /**
   * A body's trailing exit the source wrote after the try/catch: javac's skip-goto lands on it,
   * so its instruction sits past the protected range. A rule that would print it inside the body
   * hands it here instead, and the try prints it after its catch.
   */
  public static Exprent deferTryReturn(Statement stat) {
    Integer handler = TRY_BODY_HANDLER.get();
    if (!selector("tryreturntail") || handler == null || stat == null
        || stat.getExprents() == null || stat.getExprents().size() != 1) {
      return null;
    }
    Exprent only = stat.getExprents().get(0);
    if (!(only instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit)
        || exit.getExitType() != org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
        || !returnPastTry(only, handler)) {
      return null;
    }
    java.util.List<Exprent> deferred = DEFERRED_TRY_RETURNS.get();
    if (deferred == null) {
      deferred = new java.util.ArrayList<>();
      DEFERRED_TRY_RETURNS.set(deferred);
    }
    deferred.add(only);
    return only;
  }

  /** The exits a try body handed over while printing; the caller prints them after the catch. */
  public static java.util.List<Exprent> takeDeferredTryReturns() {
    java.util.List<Exprent> deferred = DEFERRED_TRY_RETURNS.get();
    DEFERRED_TRY_RETURNS.remove();
    return deferred == null ? java.util.List.of() : deferred;
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
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> exits = method == null ? null : TRY_EXIT_TARGETS.get(method);
    Integer target = exits == null ? null : exits.get(handlerOffset);
    int skip = target != null ? target : handlerExitOffset(handlerOffset);
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

  /** The first instruction offset the exprent covers, nested expressions included, or -1. */
  public static int exprentStart(Exprent exprent) {
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

  /** The target of the last branch instruction inside {@code [from, to)}, or -1. */
  public static int branchTargetInRange(Exprent condition, int from, int to) {
    StructMethod method = currentMethod();
    BitSet offsets = condition == null ? null : condition.bytecode;
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    if (offsets == null || offsets.isEmpty() || ends == null || targets == null) {
      return -1;
    }
    int lastStart = -1;
    int lastTarget = -1;
    for (int o = offsets.nextSetBit(Math.max(from, 0)); o >= 0 && (to < 0 || o < to); o = offsets.nextSetBit(o + 1)) {
      Integer end = ends.get(o);
      if (end != null && targets.containsKey(end) && o > lastStart) {
        lastStart = o;
        lastTarget = targets.get(end);
      }
    }
    return lastTarget;
  }

  /**
   * True when the target chains the test before an operand past the operand's own test: javac
   * resolves a nested if's false exit through the inner test to the final destination beyond the
   * arm, while one {@code &&} chain sends every test to the same target. A guard whose test jumps
   * into the arm sends the first branch backwards relative to the second and is not this shape, so
   * only a strictly farther outer target counts.
   */
  public static boolean chainedIfTests(Exprent head, int afterStart, int afterEnd) {
    if (!selector("ifnesttarget") || head == null || head.bytecode == null || head.bytecode.isEmpty()
        || afterStart < 0 || afterEnd <= afterStart) {
      return false;
    }
    int outer = branchTargetInRange(head, 0, afterStart);
    int inner = branchTargetInRange(head, afterStart, afterEnd);
    return outer > inner && inner >= 0;
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
    // A branch to an arm lands on the first instruction the arm covers, which for an if arm is
    // its own test's first operand; firstOffset alone would skip past the head and find nothing.
    int start = stat == null ? -1 : statementOffset(stat);
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
   * True when a pattern variable this operand declares takes a slot the target already stored a
   * temporary into. A nested if starts after the enclosing condition, so javac can hand the
   * variable a slot a temporary of that condition has since freed; in one flat condition the
   * earlier operand's temporaries are still held, and the variable gets a fresh slot.
   */
  public static boolean patternSlotReused(Exprent operand) {
    if (!selector("ifnest")) {
      return false;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, java.util.List<int[]>> tempStores = method == null ? null : TEMP_STORES.get(method);
    if (tempStores == null || tempStores.isEmpty() || operand == null) {
      return false;
    }
    for (Exprent part : operand.getAllExprents(true, true)) {
      if (!(part instanceof FunctionExprent function)
          || function.getFuncType() != FunctionExprent.FunctionType.INSTANCEOF
          || function.getLstOperands().size() < 3
          || !(function.getLstOperands().get(2) instanceof VarExprent var)
          || var.getLVT() == null) {
        continue;
      }
      java.util.List<int[]> stores = tempStores.get(var.getLVT().getIndex());
      if (stores == null) {
        continue;
      }
      // The pattern's own store is the row-less store that ends where its row begins; a temporary
      // is one that ended earlier.
      for (int[] store : stores) {
        if (store[1] < var.getLVT().getStart()) {
          return true;
        }
      }
    }
    return false;
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
   * True when the loop's condition was written inside the body as a guard whose arm exits the
   * loop: the condition's own branch lands on the body's start -- a written {@code while (C)}
   * branches to the exit instead -- and the block the guard's break reaches sits before that
   * start in the instruction layout. The source wrote
   * {@code while (true) { if (!C) { exit-block; break; } body }}.
   */
  public static boolean whileGuardInsideBody(Exprent condition, Statement loop) {
    if (!selector("loopguard") || condition == null || loop == null) {
      return false;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> targets = method == null ? null : BRANCH_TARGETS.get(method);
    if (targets == null) {
      return false;
    }
    Integer branchTarget = targets.get(condition.bytecode == null ? -1 : condition.bytecode.length());
    java.util.List<StatEdge> successors = loop.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (branchTarget == null || successors.size() != 1
        || (successors.get(0).getType() != StatEdge.TYPE_BREAK
            && successors.get(0).getType() != StatEdge.TYPE_REGULAR)) {
      return false;
    }
    Statement exit = successors.get(0).getDestination();
    Statement body = loop.getFirst();
    if (exit == null || body == null) {
      return false;
    }
    int bodyStart = firstOffset(body);
    int exitStart = firstOffset(exit);
    int exitEnd = lastEnd(exit);
    // A written `while (C)` branches to the exit block itself; the guard's test branches past it
    // into the body, and the exit block sits wholly before the body in the target's layout. A
    // statement that only reaches low offsets through a descendant's exprents (a merged head or a
    // nested loop's own test) is not a block before the body.
    boolean beforeBody = bodyStart >= 0 && exitStart >= 0 && exitStart < bodyStart
      && branchTarget > exitStart;
    return beforeBody && (!selector("wgibexit") || exitEnd >= 0 && exitEnd < bodyStart);
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
    // The loop's header exprents count: a for-update the tree moved into the header sits past the
    // body, and lastOffset only walks child statements.
    BitSet loopBits = new BitSet();
    loop.getOffset(loopBits);
    int loopEnd = loopBits.length() - 1;
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
  /**
   * The exit block a folded increment loop's break leaves by; the loop prints it after its
   * closing brace, where the source's `return …;` sat.
   */
  private static final ThreadLocal<Statement> INCREMENT_LOOP_EXIT = new ThreadLocal<>();

  /** Defers the exit of a folded increment loop to its loop's closing brace. */
  public static void deferIncrementLoopExit(Statement exit) {
    INCREMENT_LOOP_EXIT.set(exit);
  }

  /** The deferred exit, consumed once: the loop that prints next after the body takes it. */
  public static Statement takeIncrementLoopExit() {
    Statement exit = INCREMENT_LOOP_EXIT.get();
    INCREMENT_LOOP_EXIT.remove();
    return exit;
  }

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
    java.util.Map<Integer, Integer> branches = BRANCH_TARGETS.get(method);
    int[] exit = loopExitOffsets(loop);
    if (exit == null) {
      return out;
    }
    int head = exit[0];
    int loopEnd = exit[1];
    int backEdge = exit[2];
    int tail = exit[3];
    if (branches != null) {
      for (java.util.Map.Entry<Integer, Integer> entry : branches.entrySet()) {
        Integer to = entry.getValue();
        if (to != null && to >= tail && entry.getKey() > head && entry.getKey() <= backEdge
            && !(selector("looptest") && isLeadingTestOffset(loop, entry.getKey()))) {
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
    boolean reads = false;
    for (Statement stat : deferred) {
      if (readsAny(stat, defined)) {
        reads = true;
        break;
      }
    }
    if (!reads) {
      return false;
    }
    // A local the moved block reads can still be in scope: the target's table keeps its row open
    // past the loop's last instruction, which a declaration inside the body cannot do. The source
    // wrote the declaration above the loop and only the store inside; the declaration is hoisted
    // when the loop prints, so the moved block reads a local that is still in scope.
    return !(selector("deferlvt") && deferredReadsDeclaredAbove(loop, deferred, defined));
  }

  /** True when every loop-defined local the moved block reads is proven declared above the loop. */
  private static boolean deferredReadsDeclaredAbove(Statement loop, java.util.List<Statement> deferred,
      java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> defined) {
    int loopEnd = lastOffset(loop);
    if (loopEnd < 0) {
      return false;
    }
    for (Statement stat : deferred) {
      for (org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair : readPairs(stat)) {
        if (!defined.contains(pair)) {
          continue;
        }
        VarExprent definition = definitionInLoop(loop, deferred, pair);
        if (definition == null || definition.getLVT() == null) {
          return false;
        }
        org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable lvt = definition.getLVT();
        if (lvt.getStartPC() + lvt.getLength() <= loopEnd) {
          // The row closes inside the loop: the body declared the local.
          return false;
        }
      }
    }
    return true;
  }

  /** The definition the loop body holds for this pair, skipping the statements that move. */
  private static VarExprent definitionInLoop(Statement stat, java.util.List<Statement> deferred,
      org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair) {
    for (Exprent exprent : ownExprents(stat)) {
      if (exprent instanceof VarExprent var && var.isDefinition() && pair.equals(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var))) {
        return var;
      }
    }
    for (Statement child : stat.getStats()) {
      if (deferred.contains(child)) {
        continue;
      }
      VarExprent found = definitionInLoop(child, deferred, pair);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  /**
   * Prints the declarations of the locals the moved block reads above the loop: the target's table
   * proves the source declared them there, and the store stays where it is. A declaration inside
   * the loop would close the row at the loop's end; a bare declaration above it keeps the row open.
   */
  public static void hoistDeferredDeclarations(Statement loop, java.util.List<Statement> deferred) {
    if (deferred.isEmpty() || !selector("deferlvt")) {
      return;
    }
    java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> defined = new java.util.HashSet<>();
    collectDefinitions(loop, deferred, defined);
    if (defined.isEmpty()) {
      return;
    }
    int loopEnd = lastOffset(loop);
    for (Statement stat : deferred) {
      for (org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair : readPairs(stat)) {
        if (!defined.contains(pair)) {
          continue;
        }
        VarExprent definition = definitionInLoop(loop, deferred, pair);
        if (definition == null || definition.getLVT() == null
            || definition.getLVT().getStartPC() + definition.getLVT().getLength() <= loopEnd) {
          continue;
        }
        Statement owner = directOwner(loop, definition);
        Exprent declaration;
        if (owner != null && owner.getExprents() != null && owner.getExprents().contains(definition)) {
          // A bare declaration the tree kept where it stood: it moves itself.
          removeIdentity(owner.getExprents(), definition);
          definition.bytecode = null;
          declaration = definition;
        }
        else {
          declaration = definition.copy();
          ((VarExprent) declaration).bytecode = null;
          definition.setDefinition(false);
        }
        java.util.List<Exprent> defs = loop.getVarDefinitions();
        int slot = definition.getLVT().getIndex();
        int at = defs.size();
        for (int i = 0; i < defs.size(); i++) {
          if (defs.get(i) instanceof VarExprent other && other.getLVT() != null
              && other.getLVT().getIndex() > slot) {
            at = i;
            break;
          }
        }
        defs.add(at, declaration);
      }
    }
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

  /** The first offset any exprent in the statement carries, head exprents included. */
  private static int headOffsetDeep(Statement stat) {
    int min = -1;
    List<Exprent> exprents = stat.getExprents();
    List<Exprent> own = exprents;
    if (own == null) {
      // Only the condition/head exprent carries a real offset; a switch's case values keep the
      // offsets of the code that produced them, which are not this statement's position.
      if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat) {
        own = ifstat.getHeadexprent() == null ? List.of() : List.of(ifstat.getHeadexprent());
      }
      else if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement sw) {
        own = sw.getHeadexprent() == null ? List.of() : List.of(sw.getHeadexprent());
      }
      else {
        own = List.of();
      }
    }
    for (Exprent exprent : own) {
      if (exprent == null) {
        continue;
      }
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
    for (Statement child : stat.getStats()) {
      int offset = headOffsetDeep(child);
      if (offset >= 0 && (min < 0 || offset < min)) {
        min = offset;
      }
    }
    return min;
  }

  /** True when the offset belongs to the condition of the test at the loop's head. */
  private static boolean isLeadingTestOffset(Statement loop, int offset) {
    Statement first = loop.getFirst();
    while (first instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement
        && !first.getStats().isEmpty()) {
      first = first.getFirst();
    }
    if (!(first instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat)
        || ifstat.getHeadexprent() == null) {
      return false;
    }
    Exprent condition = ifstat.getHeadexprent().getCondition();
    if (condition == null) {
      return false;
    }
    // Branch entries are keyed by the instruction's end offset; the condition's last bit is its
    // final byte.
    for (Exprent inner : condition.getAllExprents(true, true)) {
      BitSet bits = inner.bytecode;
      if (bits != null && offset > 0 && bits.get(offset - 1)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The layout of a loop's exit block when the target laid it out past the back edge:
   * {@code {head, loopEnd, backEdge, tail}}, or null when the loop has no such block. The head is
   * the first instruction of the loop's test (its back edge's target), and the tail is the first
   * instruction after the back edge that a jump reaches.
   */
  public static int[] loopExitOffsets(Statement loop) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (gotos == null) {
      return null;
    }
    int head = selector("loophead") ? headOffsetDeep(loop) : firstOffset(loop);
    int loopEnd = lastOffset(loop);
    if (head < 0 || loopEnd < 0) {
      return null;
    }
    int backEdge = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getValue() != null && entry.getValue() == head && entry.getKey() > backEdge) {
        backEdge = entry.getKey();
      }
    }
    if (backEdge < 0) {
      return null;
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
      return null;
    }
    return new int[]{head, loopEnd, backEdge, tail};
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

  /** Statements an if prints after its closing brace, where the target laid them out. */
  private static final ThreadLocal<java.util.Map<StructMethod, java.util.Set<Statement>>> AFTER_IF =
    ThreadLocal.withInitial(java.util.concurrent.ConcurrentHashMap::new);

  /** Each method's catch parameters: the catch header declares them and they cannot be hoisted. */
  private static final java.util.Map<StructMethod, java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair>> CATCH_PARAMS =
    new java.util.concurrent.ConcurrentHashMap<>();

  /** Statements that printed the break their trailing jump edge would otherwise add. */
  private static final ThreadLocal<java.util.Map<StructMethod, java.util.Set<Statement>>> PRINTED_BREAKS =
    ThreadLocal.withInitial(java.util.concurrent.ConcurrentHashMap::new);

  public static void markBreakPrinted(Statement stat) {
    StructMethod method = currentMethod();
    if (method != null && stat != null) {
      PRINTED_BREAKS.get().computeIfAbsent(method,
        key -> java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>())).add(stat);
    }
  }

  /** Statements a branch printed inside its braces; the sequence must not print them again. */
  private static final ThreadLocal<java.util.Map<StructMethod, java.util.Set<Statement>>> PRINTED_IN_BRANCH =
    ThreadLocal.withInitial(java.util.concurrent.ConcurrentHashMap::new);

  public static void markPrintedInBranch(Statement stat) {
    StructMethod method = currentMethod();
    if (method != null && stat != null) {
      PRINTED_IN_BRANCH.get().computeIfAbsent(method,
        key -> java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>())).add(stat);
    }
  }

  /** True when a branch already printed this statement where the source ran it. */
  public static boolean isPrintedInBranch(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null) {
      return false;
    }
    java.util.Set<Statement> set = PRINTED_IN_BRANCH.get().get(method);
    return set != null && set.contains(stat);
  }

  /** The offset of the goto that returns to this loop's head, or -1. */
  public static int backEdgeOffset(Statement loop) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    int head = firstOffset(loop);
    if (gotos == null || head < 0) {
      return -1;
    }
    int back = -1;
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getValue() != null && entry.getValue() == head && entry.getKey() > back) {
        back = entry.getKey();
      }
    }
    return back >= 0 ? back : tailJumpOffset(loop);
  }

  /**
   * The return a loop's exit block holds when the target laid that block's code inside the loop:
   * javac placed the return before the back edge, so the source wrote {@code return ...;} in the
   * branch and the tree only moved the exit block after the loop. A block the compiler laid out
   * past the back edge is a real statement after the loop.
   */
  public static Statement returnInsideLoop(Statement loop, Statement target) {
    if (!selector("returninloop") || !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)
        || target == null || !(loop.getParent() instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement sequence)) {
      return null;
    }
    java.util.List<Statement> siblings = sequence.getStats();
    int at = siblings.indexOf(loop);
    if (at < 0 || at + 1 >= siblings.size() || siblings.get(at + 1) != target) {
      return null;
    }
    int back = backEdgeOffset(loop);
    int start = firstOffset(target);
    if (back < 0 || start < 0 || start >= back) {
      return null;
    }
    if (target.getExprents() == null || target.getExprents().size() != 1
        || !(target.getExprents().get(0) instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() == null) {
      return null;
    }
    return target;
  }

  /**
   * A local the loop declares before its brace whose first store is inside the body, and which
   * only the guard's return reads: with the return printed inside the loop the source declared it
   * at that assignment, so move the definition there. The class file's table agrees — the row
   * starts at the store.
   */
  public static void moveDeclarationIntoBody(Statement loop, Statement insideReturn, Statement body) {
    if (!selector("returninloop") || insideReturn == null || body == null || loop.getVarDefinitions().isEmpty()) {
      return;
    }
    java.util.Set<Integer> used = new java.util.HashSet<>();
    if (insideReturn.getExprents() != null) {
      for (Exprent exprent : insideReturn.getExprents()) {
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          if (inner instanceof VarExprent var) {
            used.add(var.getIndex());
          }
        }
      }
    }
    java.util.Iterator<Exprent> declarations = loop.getVarDefinitions().iterator();
    while (declarations.hasNext()) {
      Exprent declaration = declarations.next();
      if (!(declaration instanceof VarExprent decl) || !used.contains(decl.getIndex())) {
        continue;
      }
      org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assign =
        firstAssignment(body, decl.getIndex());
      if (assign == null || !(assign.getLeft() instanceof VarExprent left) || left.isDefinition()) {
        continue;
      }
      left.setDefinition(true);
      declarations.remove();
    }
  }

  /**
   * The assignment that first mentions the slot in print order, or null. A read before the store
   * means the declaration has to stay where it is.
   */
  private static org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent firstAssignment(
      Statement stat, int index) {
    if (stat.getExprents() != null) {
      for (Exprent exprent : stat.getExprents()) {
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          if (inner instanceof VarExprent var && var.getIndex() == index) {
            if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assign
                && assign.getLeft() == inner) {
              return assign;
            }
            return null;
          }
        }
      }
    }
    for (Statement child : stat.getStats()) {
      org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent found = firstAssignment(child, index);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  /** True when this statement's print already carries the break its trailing edge stands for. */
  public static boolean printedBreak(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null) {
      return false;
    }
    java.util.Set<Statement> set = PRINTED_BREAKS.get().get(method);
    return set != null && set.contains(stat);
  }

  /**
   * The statements of this run the target laid out past the branch shell, whose last instruction
   * ends at {@code shellEnd}: they are the code the source ran after the if, not part of the arm
   * the run was folded into. Empty when the whole run sits before the shell, and when a moved
   * block reads a variable the arm declares — a declaration cannot leave the arm with it.
   */
  public static java.util.List<Statement> afterShell(Statement arm, java.util.List<Statement> rest, int shellEnd) {
    java.util.List<Statement> out = new java.util.ArrayList<>();
    if (shellEnd <= 0 || arm == null) {
      return out;
    }
    for (Statement stat : rest) {
      collectAfterShell(stat, shellEnd, out);
    }
    if (!out.isEmpty()) {
      // What the arm prints is the rest before the split; a variable it declares there is out of
      // scope after the brace, so a moved block that reads one would not compile — unless the
      // source declared the variable above the if, which the moved block's own use after the
      // brace proves it did. The declaration moves out bare and its store stays in the arm.
      java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> defined = new java.util.HashSet<>();
      collectArmDefinitions(arm, out, defined);
      for (Statement stat : rest) {
        collectArmDefinitions(stat, out, defined);
      }
      java.util.List<VarExprent> hoisted = new java.util.ArrayList<>();
      boolean blocked = false;
      for (Statement stat : out) {
        for (org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair : readPairs(stat)) {
          if (!defined.contains(pair)) {
            continue;
          }
          VarExprent declaration = findDefinition(arm, pair);
          if (declaration == null) {
            for (Statement fromRest : rest) {
              if (!out.contains(fromRest)) {
                declaration = findDefinition(fromRest, pair);
              }
              if (declaration != null) {
                break;
              }
            }
          }
          if (declaration == null
              || isCatchParameter(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(declaration))) {
            blocked = true;
            break;
          }
          if (!hoisted.contains(declaration)) {
            hoisted.add(declaration);
          }
        }
        if (blocked) {
          break;
        }
      }
      if (blocked || (!hoisted.isEmpty() && !hoistBeforeArm(arm, hoisted))) {
        out.clear();
      }
    }
    return out;
  }

  private static void collectExprentDefinitions(java.util.List<Exprent> exprents,
                                                java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> out) {
    for (Exprent exprent : exprents) {
      if (exprent instanceof VarExprent var && var.isDefinition()) {
        out.add(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var));
      }
    }
  }

  private static void collectArmDefinitions(Statement stat, java.util.List<Statement> moved,
                                            java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> out) {
    if (moved.contains(stat)) {
      return;
    }
    for (Exprent exprent : ownExprents(stat)) {
      if (exprent instanceof VarExprent var && var.isDefinition()) {
        out.add(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var));
      }
    }
    for (Statement child : stat.getStats()) {
      collectArmDefinitions(child, moved, out);
    }
  }

  /**
   * True when this local is a catch parameter. The catch header declares it, so a bare
   * declaration elsewhere in its scope would redeclare it and not compile; it cannot be hoisted.
   */
  public static boolean isCatchParameter(org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair) {
    StructMethod method = currentMethod();
    Statement root = methodRoot();
    if (method == null || root == null) {
      return false;
    }
    java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> params =
      CATCH_PARAMS.computeIfAbsent(method, key -> {
        java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> out = new java.util.HashSet<>();
        collectCatchParameters(root, out);
        return out;
      });
    return params.contains(pair);
  }

  private static void collectCatchParameters(Statement stat,
                                             java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> out) {
    if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement catchStatement) {
      for (Exprent exprent : catchStatement.getStatExprents()) {
        if (exprent == null) {
          continue;
        }
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          if (inner instanceof VarExprent var) {
            out.add(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var));
          }
        }
      }
    }
    for (Statement child : stat.getStats()) {
      collectCatchParameters(child, out);
    }
  }

  /** The variable a declaration exprent defines, bare or initialized, or null. */
  private static VarExprent definedVar(Exprent exprent) {
    if (exprent instanceof VarExprent var) {
      return var;
    }
    if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assignment
        && assignment.getLeft() instanceof VarExprent var) {
      return var;
    }
    return null;
  }

  /**
   * The locals a statement reads, which a move out of the arm must keep in scope. A definition of
   * the statement itself is not a read.
   */
  private static java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> readPairs(Statement stat) {
    java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> out = new java.util.HashSet<>();
    for (Exprent exprent : ownExprents(stat)) {
      if (exprent instanceof VarExprent var && !var.isDefinition()) {
        out.add(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var));
      }
    }
    for (Statement child : stat.getStats()) {
      if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat
          && child == ifstat.getFirst()) {
        continue;
      }
      out.addAll(readPairs(child));
    }
    return out;
  }

  /** The definition of this local inside the arm, or null. */
  private static VarExprent findDefinition(Statement arm, org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair) {
    for (Exprent exprent : ownExprents(arm)) {
      if (exprent instanceof VarExprent var && var.isDefinition()
          && pair.equals(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var))) {
        return var;
      }
    }
    for (Statement child : arm.getStats()) {
      VarExprent found = findDefinition(child, pair);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  /**
   * Prints the declarations above the if the arm belongs to: the source declared them before the
   * test, and the moved block's use after the brace proves the wider scope. The stores stay.
   */
  private static boolean hoistBeforeArm(Statement arm, java.util.List<VarExprent> declarations) {
    Statement parent = arm.getParent();
    if (!(parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement)) {
      return false;
    }
    for (VarExprent var : declarations) {
      VarExprent bare = (VarExprent)var.copy();
      // A bare declaration has no instruction of its own; carrying the store's offsets would
      // place it where the store runs.
      bare.bytecode = null;
      var.setDefinition(false);
      // The declaration has to print after every statement the if's head block carries and
      // before the test: that is the last list printed ahead of the `if`.
      Statement head = parent.getFirst();
      java.util.List<Exprent> list = head != null && head.getExprents() != null && !head.getExprents().isEmpty()
        ? head.getExprents() : parent.getVarDefinitions();
      int slot = var.getLVT() == null ? -1 : var.getLVT().getIndex();
      int at = list.size();
      for (int i = 0; i < list.size(); i++) {
        VarExprent other = definedVar(list.get(i));
        int otherSlot = other == null || other.getLVT() == null ? -1 : other.getLVT().getIndex();
        if (otherSlot > slot && slot >= 0) {
          at = i;
          break;
        }
      }
      list.add(at, bare);
    }
    return true;
  }

  /**
   * Moves the declarations of the locals the join exprents read out of the arm, so the join can
   * print after the if's brace: the moved code's own use proves the source declared them before
   * the test. A bare declaration exprent moves itself; an initialized one leaves its store and
   * only a bare copy moves. A definition the arm does not hold directly blocks the move.
   */
  public static boolean hoistJoinDeclarations(
      org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStat, Statement arm,
      java.util.List<Exprent> moved) {
    java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> reads = new java.util.HashSet<>();
    for (Exprent exprent : moved) {
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof VarExprent var && !var.isDefinition()) {
          reads.add(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var));
        }
      }
    }
    java.util.List<Exprent> bares = new java.util.ArrayList<>();
    for (org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair pair : reads) {
      VarExprent definition = findDefinition(arm, pair);
      if (definition == null) {
        // A parameter, or a local the if's head block already declares: still in scope.
        continue;
      }
      Statement host = directOwner(arm, definition);
      if (host != null && host.getExprents() != null) {
        removeIdentity(host.getExprents(), definition);
        definition.bytecode = null;
        bares.add(definition);
        continue;
      }
      org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent initialized =
        assignmentOwning(arm, definition);
      if (initialized == null) {
        return false;
      }
      VarExprent bare = (VarExprent)definition.copy();
      bare.bytecode = null;
      definition.setDefinition(false);
      bares.add(bare);
    }
    if (bares.isEmpty()) {
      return true;
    }
    Statement head = ifStat.getFirst();
    java.util.List<Exprent> list = head != null && head.getExprents() != null && !head.getExprents().isEmpty()
      ? head.getExprents() : ifStat.getVarDefinitions();
    for (Exprent bare : bares) {
      int slot = bare instanceof VarExprent var && var.getLVT() != null ? var.getLVT().getIndex() : -1;
      int at = list.size();
      for (int i = 0; i < list.size(); i++) {
        VarExprent other = definedVar(list.get(i));
        int otherSlot = other == null || other.getLVT() == null ? -1 : other.getLVT().getIndex();
        if (otherSlot > slot && slot >= 0) {
          at = i;
          break;
        }
      }
      list.add(at, bare);
    }
    return true;
  }

  /** The statement whose direct exprent list holds this exprent itself, or null. */
  private static Statement directOwner(Statement stat, Exprent target) {
    java.util.List<Exprent> direct = stat.getExprents();
    if (direct != null) {
      for (Exprent exprent : direct) {
        if (exprent == target) {
          return stat;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      Statement found = directOwner(child, target);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  /** The assignment exprent whose left side this variable is, or null. */
  private static org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assignmentOwning(
      Statement stat, VarExprent target) {
    java.util.List<Exprent> direct = stat.getExprents();
    if (direct != null) {
      for (Exprent exprent : direct) {
        if (exprent instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent assignment
            && assignment.getLeft() == target) {
          return assignment;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent found = assignmentOwning(child, target);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  private static void removeIdentity(java.util.List<Exprent> list, Exprent target) {
    for (int i = 0; i < list.size(); i++) {
      if (list.get(i) == target) {
        list.remove(i);
        return;
      }
    }
  }

  /** True when the statement's print already ends on a bare `return;`. */
  public static boolean printsVoidReturn(Statement stat) {
    if (stat == null) {
      return false;
    }
    java.util.List<Exprent> exprents = stat.getExprents();
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
      return printsVoidReturn(stat.getStats().get(stat.getStats().size() - 1));
    }
    return false;
  }

  /** Prints `return;` where the target has a void return ending exactly at this offset. */
  public static void appendVoidReturnEnding(org.jetbrains.java.decompiler.util.TextBuffer buf, int end, int indent) {
    int exit = voidReturnEndingAt(end);
    if (exit < 0) {
      return;
    }
    org.jetbrains.java.decompiler.util.TextBuffer line = new org.jetbrains.java.decompiler.util.TextBuffer();
    line.appendIndent(indent).append("return;").appendLineSeparator();
    mapSynthesizedLine(line, exit);
    buf.append(line);
  }

  private static void collectAfterShell(Statement stat, int shellEnd, java.util.List<Statement> out) {
    int start = firstOffset(stat);
    if (start >= 0 && start >= shellEnd) {
      out.add(stat);
      return;
    }
    for (Statement child : stat.getStats()) {
      collectAfterShell(child, shellEnd, out);
    }
  }

  /**
   * The exprents of a moved block that ran after the if's brace. A basic block can hold exprents
   * from both sides of the arm's shell: the ones at or past it were laid out after the arm, in
   * the source's order, and only they move out of the then arm. Empty when the block does not
   * straddle the shell, and when a tail exprent reads a variable the arm declares.
   */
  public static java.util.List<Exprent> exprentsAfterShell(Statement stat, Statement arm,
                                                           java.util.List<Statement> rest, int shellEnd) {
    if (stat == null || arm == null || shellEnd <= 0) {
      return java.util.Collections.emptyList();
    }
    java.util.List<Exprent> exprents = stat.getExprents();
    if (exprents == null) {
      return java.util.Collections.emptyList();
    }
    int split = exprents.size();
    for (int i = 0; i < exprents.size(); i++) {
      int start = firstOffsetOf(exprents.get(i));
      if (start >= shellEnd) {
        split = i;
        break;
      }
    }
    if (split <= 0 || split >= exprents.size()) {
      return java.util.Collections.emptyList();
    }
    java.util.List<Exprent> tail = new java.util.ArrayList<>(exprents.subList(split, exprents.size()));
    java.util.Set<org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair> defined = new java.util.HashSet<>();
    collectExprentDefinitions(ownExprents(arm), defined);
    collectExprentDefinitions(exprents.subList(0, split), defined);
    for (Statement other : rest) {
      if (other != stat) {
        collectArmDefinitions(other, java.util.Collections.emptyList(), defined);
      }
    }
    for (Exprent exprent : tail) {
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof VarExprent var
            && defined.contains(new org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair(var))) {
          return java.util.Collections.emptyList();
        }
      }
    }
    return tail;
  }

  /**
   * True when the arm folds in a bare void return the target placed past the statements the run
   * prints after the if: the return is the method's last instruction, a goto inside the arm lands
   * on it, and those statements end just before it. The source wrote `if (C) { A } else { rest }`
   * and the closing brace stands for the return.
   */
  public static boolean returnsPastRest(Statement arm, Statement restFirst, Statement restLast) {
    StructMethod method = currentMethod();
    if (method == null || arm == null || restFirst == null || restLast == null || !arm.getStats().isEmpty()) {
      return false;
    }
    List<Exprent> exprents = arm.getExprents();
    if (exprents == null || exprents.size() < 2) {
      return false;
    }
    if (!(exprents.get(exprents.size() - 1) instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit)
        || exit.getExitType() != org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
        || exit.getValue() != null || exit.bytecode == null) {
      return false;
    }
    int exitStart = exit.bytecode.nextSetBit(0);
    Integer last = LAST_INSTRUCTION.get(method);
    if (exitStart < 0 || last == null || exitStart != last) {
      return false;
    }
    int restEnd = lastEnd(restLast);
    // Synthetic code may sit between the else block and the method's return — a record pattern's
    // match handler is laid out right there — so the rest need not end on the return. The arm's
    // own goto over the rest to it is the same proof in that case.
    if (restEnd != exitStart
        && !(restEnd >= 0 && restEnd < exitStart && armJumpsOverRestToFinalReturn(arm, restFirst))) {
      return false;
    }
    int armStart = firstOffset(arm);
    int restStart = firstOffset(restFirst);
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    if (armStart < 0 || restStart < 0 || gotos == null) {
      return false;
    }
    for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
      if (entry.getKey() >= armStart && entry.getKey() < restStart
          && entry.getValue() != null && entry.getValue() == exitStart) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when the arm's code ends in a goto laid out immediately before the statements after the
   * if, and that goto jumps to the method's own final return. The source wrote
   * {@code if (C) { A } else { rest }}: javac lays the else block right after the arm's code and
   * the arm's completion jumps over it to the method's end. Synthetic code (a record pattern's
   * match handler) may sit between the else block and that return, so the rest need not end on it.
   */
  public static boolean armJumpsOverRestToFinalReturn(Statement arm, Statement restFirst) {
    if (!selector("elseblock")) {
      return false;
    }
    StructMethod method = currentMethod();
    Integer last = method == null ? null : LAST_INSTRUCTION.get(method);
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (last == null || gotos == null || arm == null || restFirst == null) {
      return false;
    }
    int restStart = firstOffset(restFirst);
    int armStart = firstOffset(arm);
    if (restStart < 3 || armStart < 0 || restStart - 3 < armStart) {
      return false;
    }
    Integer target = gotos.get(restStart - 3);
    return target != null && target == last;
  }

  /**
   * Hides the method's own final void return from the last block the body prints when the target
   * reaches that return with a goto laid out after the block's own code. The source did not write
   * the return: its flow fell out of the body and javac laid the method's one return past the
   * synthetic code — a record pattern's match handler sits there — so the closing brace compiles
   * to the same instruction. Returns an action that puts the exprent back, or null.
   */
  public static Runnable hideImplicitFinalReturn(Statement body) {
    if (!selector("silentreturn") || body == null) {
      return null;
    }
    StructMethod method = currentMethod();
    Integer last = method == null ? null : LAST_INSTRUCTION.get(method);
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (last == null || gotos == null) {
      return null;
    }
    Statement tail = body;
    while (true) {
      List<Exprent> exprents = tail.getExprents();
      if (exprents != null) {
        if (exprents.size() < 2) {
          return null;
        }
        Exprent candidate = exprents.get(exprents.size() - 1);
        if (!(candidate instanceof ExitExprent exit)
            || exit.getExitType() != ExitExprent.Type.RETURN || exit.getValue() != null
            || exit.bytecode == null || exit.bytecode.isEmpty()) {
          return null;
        }
        int exitStart = exit.bytecode.nextSetBit(0);
        int start = firstOffset(tail);
        if (exitStart != last || start < 0) {
          return null;
        }
        for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
          int from = entry.getKey();
          if (from >= start && from < exitStart
              && entry.getValue() != null && entry.getValue() == exitStart) {
            int index = exprents.size() - 1;
            exprents.remove(index);
            return () -> exprents.add(index, candidate);
          }
        }
        return null;
      }
      // Only the statements whose completion falls out of the method are followed: a block printed
      // last inside a loop, a switch or a handler continues after its brace, and a return hidden
      // there would let control run on.
      if (!(tail instanceof SequenceStatement) && !(tail instanceof IfStatement)) {
        return null;
      }
      Statement next = null;
      if (tail instanceof IfStatement branching) {
        next = branching.getElsestat() != null ? branching.getElsestat() : branching.getIfstat();
      }
      else {
        List<Statement> children = tail.getStats();
        if (!children.isEmpty()) {
          next = children.get(children.size() - 1);
        }
      }
      if (next == null || next == tail) {
        return null;
      }
      tail = next;
    }
  }

  /** Records the statements an if prints after its closing brace, so the arm prints nothing there. */
  public static void markAfterIf(java.util.List<Statement> statements) {
    StructMethod method = currentMethod();
    if (method == null || statements.isEmpty()) {
      return;
    }
    AFTER_IF.get().computeIfAbsent(method, key -> java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>())).addAll(statements);
  }

  /** Forgets the recorded statements once the if has printed them. */
  public static void releaseAfterIf(java.util.List<Statement> statements) {
    StructMethod method = currentMethod();
    if (method == null || statements.isEmpty()) {
      return;
    }
    java.util.Set<Statement> set = AFTER_IF.get().get(method);
    if (set != null) {
      set.removeAll(statements);
    }
  }

  /** True when the enclosing if prints this statement after its closing brace. */
  public static boolean isAfterIf(Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || stat == null) {
      return false;
    }
    java.util.Set<Statement> set = AFTER_IF.get().get(method);
    return set != null && set.contains(stat);
  }

  /**
   * A break that leaves its closure has to name it: the same {@code break;} inside a switch would
   * only leave the switch. The tree's labelled flag is recomputed by the label passes and a break
   * to a block hoisted out of a loop can lose it; the jump itself proves the name is needed.
   */
  public static boolean leavesClosure(StatEdge edge) {
    if (edge == null || edge.getType() != StatEdge.TYPE_BREAK || edge.closure == null
        || edge.getDestination() == null || edge.getDestination() instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement) {
      return false;
    }
    Statement destination = edge.getDestination();
    Statement closure = edge.closure;
    // Only a loop prints its label purely because a break names it ({@link #carriesBreakOut}); a
    // switch's or block's label is owned by its own print rule, and naming it here could leave the
    // label undefined.
    if (!selector("breakout")
        || !(closure instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      return false;
    }
    // The jump has to start inside the loop: a break printed after the loop's closing brace can no
    // longer name its label. And something between the two has to swallow an unnamed break first —
    // a switch or another loop — or a plain `break;` would already leave the loop.
    return destination != closure && !closure.containsStatementStrict(destination)
      && closure.containsStatementStrict(edge.getSource()) && shielded(edge.getSource(), closure);
  }

  /**
   * True when a plain {@code break;} at the source would leave some statement inside the closure
   * rather than the closure itself: a switch or another loop stands between the two.
   */
  private static boolean shielded(Statement source, Statement closure) {
    if ((source instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement
        || source instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)
        && source != closure) {
      return true;
    }
    for (Statement parent = source.getParent(); parent != null && parent != closure; parent = parent.getParent()) {
      if (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement
          || parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement) {
        return true;
      }
    }
    return false;
  }

  /** True when a break inside this statement names it as its closure: its print needs a label. */
  public static boolean carriesBreakOut(Statement stat) {
    return carriesBreakOut(stat, stat);
  }

  private static boolean carriesBreakOut(Statement stat, Statement closure) {
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      if (edge.closure == closure && leavesClosure(edge)) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (carriesBreakOut(child, closure)) {
        return true;
      }
    }
    return false;
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
    // The branch has to leave the loop entirely: the exit is past everything the loop covers,
    // and it cannot land on the loop's own back edge — that is the continue a written test
    // falls into, not a jump past the loop.
    int loopEnd = lastOffset(loop);
    if (target == null || loopEnd < 0 || target <= loopEnd) {
      return false;
    }
    // A continue guard's branch goes to the loop's head, not past the loop; the break guard's
    // does not, so only the continue-shaped test can land on the back edge by coincidence.
    if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStatement
        && ifStatement.getIfEdge() != null
        && ifStatement.getIfEdge().getType() == StatEdge.TYPE_CONTINUE
        && landsOnBackEdge(loop, target)) {
      return false;
    }
    return guards == null || !guards.containsKey(end);
  }

  /** True when {@code offset} is a jump back to this loop's head: its back edge or a copy of it. */
  private static boolean landsOnBackEdge(Statement loop, int offset) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    Integer dest = gotos == null ? null : gotos.get(offset);
    if (dest == null || !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    // The destination has to be this loop's own head, not just any offset before its body: a
    // break out of a nested loop lands on the outer loop's back edge, which also sits there.
    Exprent head = switch (doStatement.getLooptype()) {
      case WHILE, DO_WHILE -> doStatement.getConditionExprent();
      case FOR, FOR_EACH -> doStatement.getIncExprent() != null ? doStatement.getIncExprent() : doStatement.getConditionExprent();
      default -> null;
    };
    if (head == null || head.bytecode == null || head.bytecode.isEmpty()) {
      return false;
    }
    // The loop's first instruction is the leftmost one any part of its test owns; the receiver
    // chain a field access owns counts, so the destination is compared with that, not the test's
    // own first byte.
    int start = firstOffsetOf(head);
    return start >= 0 && dest <= start && dest >= start - 3;
  }

  /**
   * Whether a guard whose test skips to the loop's back edge is really an arm: the source wrote
   * {@code if (cond) { rest }} and the branch over the arm lands on the jump back to the head.
   * A written {@code if (!cond) continue;} compiles to a jump over a goto to the head instead,
   * which {@link #CONTINUE_GUARDS} records.
   */
  public static boolean branchFallsToBackEdge(Exprent head, Statement stat) {
    StructMethod method = currentMethod();
    if (method == null || head == null || head.bytecode == null || head.bytecode.isEmpty() || stat == null) {
      return false;
    }
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
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
    Integer target = targets.get(head.bytecode.length());
    return target != null && landsOnBackEdge(loop, target);
  }

  /**
   * Hides a labelled block's jumps while a caller prints that block as an else-if chain. The arms'
   * terminal breaks are the chain's own exits, so the source has no `break label` there; every
   * edge to the closure is dropped for the duration of the print.
   */
  public static Statement hideClosure(Statement closure) {
    Statement old = HIDDEN_CLOSURE.get();
    HIDDEN_CLOSURE.set(closure);
    return old;
  }

  public static void restoreClosure(Statement old) {
    if (old == null) {
      HIDDEN_CLOSURE.remove();
    }
    else {
      HIDDEN_CLOSURE.set(old);
    }
  }

  public static boolean isClosureHidden(StatEdge edge) {
    Statement hidden = HIDDEN_CLOSURE.get();
    return hidden != null && edge != null && edge.closure == hidden;
  }

  /** The block being printed as an else-if chain right now, or null. */
  public static Statement hiddenClosure() {
    return HIDDEN_CLOSURE.get();
  }

  /**
   * A statement the caller has already accounted for: an arm's trailing copy of the exit the
   * chain prints once after it, which is the same instruction and must not be printed twice.
   */
  public static Statement skipStatement(Statement stat) {
    Statement old = SKIPPED_STATEMENT.get();
    SKIPPED_STATEMENT.set(stat);
    return old;
  }

  public static void restoreStatement(Statement old) {
    if (old == null) {
      SKIPPED_STATEMENT.remove();
    }
    else {
      SKIPPED_STATEMENT.set(old);
    }
  }

  public static boolean isStatementSkipped(Statement stat) {
    Statement skipped = SKIPPED_STATEMENT.get();
    return skipped != null && skipped == stat;
  }

  /**
   * Marks an if whose closing brace the caller prints on the next line with `else`, the way the
   * source writes a chain: `} else if (c) {`. Returns whether the printer honoured it.
   */
  public static Statement openArm(Statement stat) {
    Statement old = OPEN_ARM.get();
    OPEN_ARM.set(stat);
    ARM_CLOSED.set(Boolean.FALSE);
    return old;
  }

  public static boolean closeArm(Statement old) {
    boolean closed = Boolean.TRUE.equals(ARM_CLOSED.get());
    if (old == null) {
      OPEN_ARM.remove();
    }
    else {
      OPEN_ARM.set(old);
    }
    ARM_CLOSED.remove();
    return closed;
  }

  public static boolean isArmOpen(Statement stat) {
    return stat != null && stat == OPEN_ARM.get();
  }

  /** Called by the arm the caller left open once it has printed its closing brace. */
  public static void armClosed() {
    ARM_CLOSED.set(Boolean.TRUE);
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

  /** The end offset of the bare block being printed; a nested run ending there is that brace. */
  private static final ThreadLocal<Integer> HANDOVER_END = new ThreadLocal<>();

  /** Marks the block a handover run prints as open until its closing brace; returns the old. */
  public static int handoverEnd(int end) {
    Integer old = HANDOVER_END.get();
    HANDOVER_END.set(end);
    return old == null ? -1 : old;
  }

  public static void restoreHandoverEnd(int old) {
    if (old < 0) {
      HANDOVER_END.remove();
    } else {
      HANDOVER_END.set(old);
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

  /**
   * The break edge the enclosing print will emit after a closing brace, or null. Set while a
   * switch arm is printed whose break the target's table proves stood outside the arm's block;
   * the statement that holds the edge must not print it, since the caller prints it back there.
   */
  private static final ThreadLocal<Statement> DEFERRED_BREAK = new ThreadLocal<>();

  /** Defers the break edges closing over {@code closure} to the caller; returns the previous. */
  public static Statement deferBreakTo(Statement closure) {
    Statement old = DEFERRED_BREAK.get();
    DEFERRED_BREAK.set(closure);
    return old;
  }

  public static void restoreDeferredBreak(Statement old) {
    if (old == null) {
      DEFERRED_BREAK.remove();
    } else {
      DEFERRED_BREAK.set(old);
    }
  }

  /** True when this edge is a break to the switch whose break the caller prints after a brace. */
  public static boolean isDeferredBreak(StatEdge edge) {
    Statement closure = DEFERRED_BREAK.get();
    return edge != null && closure != null && edge.getType() == StatEdge.TYPE_BREAK
      && edge.explicit && edge.closure == closure;
  }

  /** True when a break edge to the deferred switch hangs off this statement or its head block. */
  public static boolean holdsDeferredBreak(Statement stat) {
    if (stat == null || DEFERRED_BREAK.get() == null) {
      return false;
    }
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      if (isDeferredBreak(edge)) {
        return true;
      }
    }
    Statement head = stat.getFirst();
    return head != null && head != stat && holdsDeferredBreak(head);
  }

  /** True when the arm holds a break edge closing over {@code switchStat}. */
  public static boolean breaksTo(Statement stat, Statement switchStat) {
    if (stat == null) {
      return false;
    }
    for (StatEdge edge : stat.getAllSuccessorEdges()) {
      if (edge.getType() == StatEdge.TYPE_BREAK && edge.explicit && edge.closure == switchStat) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (breaksTo(child, switchStat)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The offset of a jumped-onto goto that a local the statement declares ends at — the target's
   * table closes the block holding that local right before the jump, so the jump is the break the
   * source wrote after the closing brace.
   */
  public static int blockClosingBreak(Statement stat) {
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute table =
      method == null ? null : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    int start = firstOffset(stat);
    int end = lastOffset(stat);
    if (table == null || start < 0 || end < 0) {
      return -1;
    }
    for (LocalVariable row : table.getVariables().toList()) {
      int close = row.getEnd();
      if (row.getStart() < start || row.getStart() > end || close <= row.getStart()) {
        continue;
      }
      if (jumpTargetAt(close) < 0 || !jumpsOnto(close)) {
        continue;
      }
      return close;
    }
    return -1;
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
   * True when the target compiled this if as {@code if (!C) { continue; } <arm>}: the branch's
   * fall-through goto lands on the head of the loop that directly encloses the test — the narrow
   * landing test, where the join of a written {@code if (!C) { } else <arm>} could not — and the
   * line table puts the goto on a line of its own before the arm. The arm the tree hung off the
   * test is the source's next statement, not an else. Only the innermost loop is asked: a
   * {@code break} out of it lands on the enclosing loop's increment, which is no continue of this
   * test's loop.
   */
  public static boolean printContinueGuardAtHead(Exprent head, Statement around) {
    if (!selector("continueguard") || !(head instanceof IfExprent) || around == null
        || head.bytecode == null || head.bytecode.isEmpty()) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    Statement loop = around.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    int end = head.bytecode.length();
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    Integer target = guards == null ? null : guards.get(end);
    if (target == null || !isLoopHeadTarget(doStatement, target)) {
      return false;
    }
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
   * True when the target compiled this if as {@code if (C) continue;} inside a try-with-resources
   * body that ends the loop body: the branch skips the synthetic {@code close()} and the goto
   * right after it, so the branch-then-goto pair is broken by the close call. The jump the source's
   * continue compiled to is the one at the close's normal exit; the table must put a line of its
   * own there, before the body's first line. A written continue prints inside the try body, so the
   * close still runs on its path.
   */
  public static boolean printContinueThroughClose(Exprent head, Statement sequence) {
    CONTINUE_CLOSE_SITE.get()[0] = -1;
    if (!selector("continueguard") || head == null || head.bytecode == null || head.bytecode.isEmpty()
        || !endsLoopBodyAcrossTry(sequence)) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    int end = head.bytecode.length();
    java.util.Map<Integer, Integer> guards = CONTINUE_ELSE_GUARDS.get(method);
    Integer target = guards == null ? null : guards.get(end);
    if (target == null || !targetContinues(target, sequence)) {
      return false;
    }
    java.util.Map<Integer, int[]> sites = CONTINUE_ELSE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(end);
    if (site == null) {
      return false;
    }
    // The jump before the branch's target has to be the close's normal exit: the instruction right
    // before that goto is the synthetic close() call, not the tail of an arm the branch skipped.
    java.util.Map<Integer, Integer> byEnd = INSTRUCTION_BY_END.get(method);
    Integer close = byEnd == null ? null : byEnd.get(site[0]);
    BitSet closes = CLOSE_CALLS.get(method);
    if (close == null || closes == null || !closes.get(close)) {
      return false;
    }
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table != null) {
      int continueLine = table.findLineNumber(site[0]);
      int bodyLine = table.findLineNumber(site[1]);
      if (continueLine >= 0 && bodyLine >= 0 && continueLine >= bodyLine) {
        return false;
      }
    }
    CONTINUE_CLOSE_SITE.get()[0] = site[0];
    return true;
  }

  /**
   * The goto the last {@link #printContinueThroughClose} proved, for the printer to pin the printed
   * {@code continue;} to, exactly as {@link #continueElseSite} serves the else form.
   */
  public static int continueCloseSite() {
    return CONTINUE_CLOSE_SITE.get()[0];
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
   * The goto the guard written just before this next test compiles to, or -1. The printed
   * {@code continue;} takes its line from the target's table entry at that jump, exactly as
   * {@link #continueGoto} does for the last guard of a merged condition.
   */
  public static int continueGotoBefore(Exprent next, Statement around) {
    if (!selector("continueguard")) {
      return -1;
    }
    int start = firstOffsetOf(next);
    if (start < 3 || !continuesAt(start - 3, around)) {
      return -1;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, int[]> sites = method == null ? null : CONTINUE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(start - 3);
    return site == null ? -1 : site[0];
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
    // The key filter is the condition's own byte range, not the head's bits: the merge drops the
    // comparison wrapper of a boolean field or call, so the head's bits keep only the last guard's
    // branch ([136,150) for BlockCollisions) and filtering on them loses every earlier one.
    int[] range = head instanceof IfExprent ifHead ? byteRange(ifHead.getCondition()) : null;
    if (range == null) {
      return null;
    }
    java.util.List<Integer> keys = new java.util.ArrayList<>();
    for (Integer end : guards.keySet()) {
      if (end <= range[0] || end > range[1]) {
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

  /**
   * The operand groups of a condition that folded a run of {@code if (G) continue;} statements
   * whose continues run through a try-with-resources close. A written guard's branch jumps past
   * the close and the goto behind it, so the target records it as an else guard: the statement
   * after the guard begins at the branch's target, not right after the branch. Groups at those
   * targets, or null when the target records fewer than two such guards.
   */
  public static java.util.List<java.util.List<Exprent>> closeGuardGroups(Exprent head,
                                                                         java.util.List<Exprent> operands,
                                                                         Statement around) {
    if (!selector("continueguard") || !(head instanceof IfExprent ifHead) || operands.size() < 2) {
      return null;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> guards = CONTINUE_ELSE_GUARDS.get(method);
    java.util.Map<Integer, int[]> sites = CONTINUE_ELSE_SITES.get(method);
    int[] range = byteRange(ifHead.getCondition());
    if (guards == null || guards.isEmpty() || sites == null || range == null) {
      return null;
    }
    java.util.List<int[]> boundaries = new java.util.ArrayList<>();
    for (Integer end : guards.keySet()) {
      if (end <= range[0] || end > range[1]) {
        continue;
      }
      Integer target = guards.get(end);
      int[] site = sites.get(end);
      if (target == null || site == null || !targetContinues(target, around)) {
        continue;
      }
      boundaries.add(new int[]{end, site[1]});
    }
    if (boundaries.isEmpty()) {
      return null;
    }
    boundaries.sort(java.util.Comparator.comparingInt(b -> b[1]));
    // The branches of one written guard's `&&` chain share its continue block, so they record
    // the same next statement; only the last branch of such a run ends the statement.
    java.util.List<int[]> distinct = new java.util.ArrayList<>();
    for (int[] boundary : boundaries) {
      if (distinct.isEmpty() || distinct.get(distinct.size() - 1)[1] != boundary[1]) {
        distinct.add(boundary);
      } else {
        distinct.set(distinct.size() - 1, boundary);
      }
    }
    boundaries = distinct;
    int[] starts = new int[operands.size()];
    for (int i = 0; i < starts.length; i++) {
      starts[i] = firstOffsetOf(operands.get(i));
      if (starts[i] < 0) {
        return null;
      }
    }
    java.util.List<java.util.List<Exprent>> groups = new java.util.ArrayList<>();
    int from = 0;
    for (int[] boundary : boundaries) {
      int next = from;
      while (next < starts.length && starts[next] < boundary[1]) {
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

  /**
   * The goto the head's own last guard compiles to when its continue runs through a
   * try-with-resources close: the jump the target records behind the close for the branch that
   * ends the head, or -1.
   */
  public static int continueCloseSiteForHead(Exprent head) {
    if (!selector("continueguard") || head == null || head.bytecode == null || head.bytecode.isEmpty()) {
      return -1;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, int[]> sites = method == null ? null : CONTINUE_ELSE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(head.bytecode.length());
    return site == null ? -1 : site[0];
  }

  /**
   * The goto a written guard before this next test compiles to when its continue runs through a
   * try-with-resources close: the jump the target records behind the close, so the printed
   * {@code continue;} takes its line from it.
   */
  public static int continueCloseSiteBefore(Exprent next, Statement around) {
    if (!selector("continueguard")) {
      return -1;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, int[]> sites = method == null ? null : CONTINUE_ELSE_SITES.get(method);
    int start = firstOffsetOf(next);
    if (sites == null || start < 0) {
      return -1;
    }
    for (java.util.Map.Entry<Integer, int[]> entry : sites.entrySet()) {
      if (entry.getValue() != null && entry.getValue()[1] == start) {
        return entry.getValue()[0];
      }
    }
    return -1;
  }

  /**
   * The operand groups a condition that folded a run of {@code if (G) continue;} statements splits
   * into at the target's recorded guards, or null when it holds fewer than two. The key filter is
   * the condition's own byte range, not the head's bits: the merge drops the comparison wrapper of
   * a boolean field or call, so the head's bits keep only the last guard's branch and filtering on
   * them loses every earlier one. A key K ends the branch of one written guard and the statement
   * after it began at K+3, so a group boundary must be exactly an operand start. Unlike
   * {@link #guardGroups} this reads the condition the caller hands over, so a group can be a chain
   * of several tests rather than one guard per operand. {@code breaks} selects which enclosing
   * statement's exit the target's jump has to be: a loop's continue target or the break target of
   * the enclosing loop or switch, the same shapes with a {@code break} instead of a
   * {@code continue}.
   */
  public static GuardSplit mergedGuards(Exprent head,
                                        java.util.List<Exprent> operands,
                                        Statement around,
                                        boolean breaks) {
    if (!selector("continueguard") || !(head instanceof IfExprent ifHead) || operands.size() < 2) {
      return null;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(currentMethod());
    int[] range = byteRange(ifHead.getCondition());
    if (guards == null || guards.isEmpty() || range == null) {
      return null;
    }
    java.util.List<Integer> keys = new java.util.ArrayList<>();
    for (Integer end : guards.keySet()) {
      if (end <= range[0] || end > range[1]) {
        continue;
      }
      if (exitsAt(end, around, breaks)) {
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
    int headGroup = -1;
    int from = 0;
    for (Integer key : keys) {
      int boundary = key + 3;
      int next = from;
      while (next < starts.length && starts[next] < boundary) {
        next++;
      }
      // A key with no operand of its own would print a guard with no test; a boundary inside an
      // operand means the key belongs to something the condition only contains.
      if (next == from || (next < starts.length && starts[next] != boundary)) {
        return null;
      }
      groups.add(new java.util.ArrayList<>(operands.subList(from, next)));
      from = next;
      if (from >= operands.size()) {
        break;
      }
    }
    if (from < operands.size()) {
      headGroup = groups.size();
      groups.add(new java.util.ArrayList<>(operands.subList(from, operands.size())));
    }
    return groups.size() > 1 ? new GuardSplit(groups, headGroup) : null;
  }

  /** A condition split at the target's recorded guards. */
  public static final class GuardSplit {
    public final java.util.List<java.util.List<Exprent>> groups;
    /**
     * Index of the group no guard closes — the head's own test, which the merge kept as written —
     * or -1 when a guard closed the last group as well.
     */
    public final int headGroup;

    GuardSplit(java.util.List<java.util.List<Exprent>> groups, int headGroup) {
      this.groups = groups;
      this.headGroup = headGroup;
    }
  }

  /**
   * The byte range [first, end) the expression's parts own, or null when none carries an offset.
   * The end is exclusive, matching {@link BitSet#length()}: a guard key is the offset just past a
   * branch, so it sits at or below the end of the last part that covers that branch.
   */
  private static int[] byteRange(Exprent exprent) {
    int first = -1;
    int end = -1;
    for (Exprent part : exprent.getAllExprents(true, true)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int start = part.bytecode.nextSetBit(0);
      if (first < 0 || start < first) {
        first = start;
      }
      if (part.bytecode.length() > end) {
        end = part.bytecode.length();
      }
    }
    return first < 0 ? null : new int[]{first, end};
  }

  /**
   * True when the head's own branch jumps to the enclosing loop's continue target. The last guard a
   * merge folded into the condition keeps no goto: javac collapses {@code if (G) goto L} whose
   * fall-through is also L into the opposite branch, so its bytes live in the head and that branch
   * is the only proof the trailing test was a guard of its own.
   */
  public static boolean headBranchContinues(Exprent head, Statement around) {
    StructMethod method = currentMethod();
    if (method == null || head == null || head.bytecode == null || head.bytecode.isEmpty()) {
      return false;
    }
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> targets = BRANCH_TARGETS.get(method);
    if (ends == null || targets == null) {
      return false;
    }
    int lastStart = -1;
    for (int offset = head.bytecode.nextSetBit(0); offset >= 0; offset = head.bytecode.nextSetBit(offset + 1)) {
      if (ends.containsKey(offset) && offset > lastStart) {
        lastStart = offset;
      }
    }
    Integer end = lastStart < 0 ? null : ends.get(lastStart);
    Integer target = end == null ? null : targets.get(end);
    return target != null && targetContinues(target, around);
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

  /** Whether this offset is the continue target of the loop the statement sits in. */
  private static boolean targetContinues(int target, Statement around) {
    Statement loop = around == null ? null : around.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    return loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement
      && isContinueTarget(doStatement, target);
  }

  /**
   * Whether this offset is where a {@code break} of the statement would land: the target must be
   * the instruction just past the innermost enclosing loop or switch, the statement a bare
   * {@code break} leaves.
   */
  private static boolean targetBreaks(int target, Statement around) {
    Statement inner = around == null ? null : around.getParent();
    while (inner != null && !(inner instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)
        && !(inner instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement)) {
      inner = inner.getParent();
    }
    if (inner == null) {
      return false;
    }
    int exit = exitAfter(inner);
    return exit >= 0 && exit == target;
  }

  /**
   * The first instruction offset after a statement's own extent. The statement's exprents stop at
   * its last covered instruction, but the jumps that close it — a loop's back edge, a break it
   * takes, a switch arm's join — belong to no exprent, so the statement ends after them.
   */
  private static int exitAfter(Statement stat) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (ends == null || gotos == null) {
      return -1;
    }
    BitSet bits = new BitSet();
    stat.getOffset(bits);
    int end = bits.length();
    if (end <= 0) {
      return -1;
    }
    // A contiguous instruction layout puts at most a few closing jumps past the last covered
    // instruction; a longer run means the offsets do not describe this statement's layout.
    for (int jump = 0; jump < 8 && gotos.containsKey(end); jump++) {
      Integer next = ends.get(end);
      if (next == null) {
        return -1;
      }
      end = next;
    }
    return end;
  }

  private static boolean continuesAt(int end, Statement around) {
    return exitsAt(end, around, false);
  }

  /**
   * Whether the recorded guard key at this offset ends a statement whose jump leaves for the
   * enclosing statement's {@code continue} target ({@code breaks} false) or break target
   * ({@code breaks} true).
   */
  private static boolean exitsAt(int end, Statement around, boolean breaks) {
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    Integer target = guards == null ? null : guards.get(end);
    if (target == null
        || (breaks ? !targetBreaks(target, around) : !targetContinues(target, around))) {
      return false;
    }
    // The target's table must put the jump's line before the statement after it; the source wrote
    // the `continue;` or `break;` on a line of its own above the rest of the body.
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
   * The target's local-table rows a statement's own straight-line chain declares, as
   * {@code {slot, start, end}}: the statement itself and the head blocks of the ifs it contains.
   * `if (C) { …; } break;` keeps its statements in the head, and the source wrote them in the same
   * block. A local declared in a loop (its init included), in an if arm or a nested block keeps
   * that construct's scope instead, and a pattern variable is declared by the label, not here.
   */
  public static java.util.List<int[]> declarationRows(Statement stat) {
    java.util.List<int[]> rows = new java.util.ArrayList<>();
    collectDeclarationRows(stat, rows);
    return rows;
  }

  private static void collectDeclarationRows(Statement stat, java.util.List<int[]> rows) {
    addDeclarationRows(stat.getVarDefinitions(), rows);
    if (stat.getExprents() != null) {
      addDeclarationRows(stat.getExprents(), rows);
    }
    if (stat instanceof SequenceStatement) {
      for (Statement child : stat.getStats()) {
        collectDeclarationRows(child, rows);
      }
    } else if (stat instanceof IfStatement ifStat) {
      collectDeclarationRows(ifStat.getFirst(), rows);
    }
  }

  private static void addDeclarationRows(java.util.List<? extends Exprent> exprents, java.util.List<int[]> rows) {
    for (Exprent exprent : exprents) {
      if (exprent == null) {
        continue;
      }
      for (Exprent part : exprent.getAllExprents(true, true)) {
        if (part instanceof VarExprent var && var.isDefinition() && var.getLVT() != null) {
          rows.add(new int[]{var.getLVT().getIndex(), var.getLVT().getStart(), var.getLVT().getEnd()});
        }
      }
    }
  }

  /**
   * Whether a local this statement's block declares ends inside the block, so that a brace around
   * the block would scope it. A row that starts in the block but ends past the block's last
   * instruction belongs to a local declared outside it, which the block only re-assigns.
   */
  public static boolean declaresBlockLocal(Statement statement) {
    if (statement == null) {
      return false;
    }
    int end = lastEnd(statement);
    if (end < 0) {
      return false;
    }
    for (int[] row : declarationRows(statement)) {
      if (row[2] <= end) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when the table proves the source braced this block: the first local the block declares
   * itself has a row that ends exactly where the block's last instruction does. javac closes an
   * alive range at the scope it lives in or at a merge it does not survive; a row ending on the
   * block's own last instruction is the source's closing brace around the block. An unbraced
   * block's local would keep its range open until the enclosing construct closed.
   */
  public static boolean closesAtOwnEnd(Statement statement) {
    if (!selector("bareblock") || statement == null) {
      return false;
    }
    int end = lastEnd(statement);
    if (end < 0) {
      return false;
    }
    java.util.List<int[]> rows = declarationRows(statement);
    return !rows.isEmpty() && rows.get(0)[2] == end;
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
   * The goto that leaves the then arm for the loop head when a detached block stands between it and
   * the arm that follows: {loop head, goto offset, next arm start}, or null. The block is the else
   * part of an inner if, which javac places after the arm's last jump; the jump is still the arm's
   * written continue, and the arm's own end is the last condition branch's target.
   */
  private static int[] armContinueGoto(Exprent head) {
    if (!selector("continuearm")) {
      return null;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return null;
    }
    BitSet offsets = head.bytecode;
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    java.util.Map<Integer, Integer> branches = BRANCH_TARGETS.get(method);
    if (gotos == null || branches == null || offsets == null || offsets.isEmpty()) {
      return null;
    }
    // The condition's last branch is the fall-through into the then arm; its target is the arm
    // that follows the if.
    int armStart = offsets.length();
    Integer armEnd = branches.get(armStart);
    if (armEnd == null || armEnd <= armStart) {
      return null;
    }
    java.util.Map<Integer, Integer> branchEnds = BRANCHES.get(method);
    int best = -1;
    for (java.util.Map.Entry<Integer, Integer> goto_ : gotos.entrySet()) {
      int offset = goto_.getKey();
      int dest = goto_.getValue();
      if (offset < armStart || offset >= armEnd) {
        continue;
      }
      if (branchEnds != null && branchEnds.containsKey(offset)) {
        // The jump half of an `if (C) continue;` guard, not a statement ending the arm.
        continue;
      }
      if (dest >= armStart && dest < armEnd) {
        // A jump inside the arm is an inner loop's continue, not the arm's own exit.
        continue;
      }
      if (offset > best) {
        best = offset;
      }
    }
    // The destination is checked against the enclosing loop by the caller.
    return best < 0 ? null : new int[]{gotos.get(best), best, armEnd};
  }

  /**
   * The mirror of {@link #printContinueGuard} for an else arm: {@code if (C) { ...; continue; } rest}
   * where the decompiler kept {@code rest} as the else arm. The branch jumps over the then arm and
   * the goto ending that arm is the continue. The caller proves the arm is the rest of the loop
   * body, so hoisting it keeps every scope's end where it was and no local can change slot.
   */
  public static boolean printContinueElse(Exprent head, Statement sequence) {
    CONTINUE_ELSE_SITE.get()[0] = -1;
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
    Statement loop = sequence.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    Integer target = guards.get(offsets.length());
    java.util.Map<Integer, int[]> sites = CONTINUE_ELSE_SITES.get(method);
    int[] site = sites == null ? null : sites.get(offsets.length());
    boolean adjacent = target != null && site != null;
    if (!adjacent) {
      // The written continue need not stand immediately before the arm that follows: when it ends
      // the arm's last statement, javac places the else block of an inner if between the two. The
      // goto that leaves the arm for the loop head then sits before that block, and the arm's own
      // end is the branch target that begins the arm we print next. Only an arm whose own end edge
      // is that continue can have written it; any other arm's jump belongs to a nested statement.
      if (!(sequence instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifStatement)
          || !endsWithContinueEdge(ifStatement.getIfstat(), doStatement)) {
        return false;
      }
      int[] found = armContinueGoto(head);
      if (found == null) {
        return false;
      }
      target = found[0];
      site = new int[]{found[1], found[2]};
    }
    // A jump the table marks as starting a line is a statement of the source. A jump to the loop's
    // own head — everything the loop builds before its body — is one too: the loop's back edge is
    // a jump instruction at the body's end, so nothing else in the middle of the body left one
    // there. A jump to the update or to a join cannot be told apart from an if/else's closing jump
    // without the table, and javac only anchors that jump when the source wrote a statement there.
    int bodyStart = firstOffset(doStatement.getFirst());
    boolean headTarget = target >= 0 && bodyStart >= 0 && target < bodyStart;
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null || !headTarget && !startsLine(table, site[0])) {
      return false;
    }
    if (!isLoopHeadTarget(doStatement, target)) {
      return false;
    }
    // The jump half of an `if (C) continue;` follows its branch; it is that guard's, not a
    // statement of its own at the arm's end.
    java.util.Map<Integer, Integer> branches = BRANCHES.get(method);
    if (branches != null && branches.containsKey(site[0])) {
      return false;
    }
    // The printed continue keeps the line the target's table gives its jump when that line starts
    // there; otherwise the arm's own last line is the only line the jump can belong to.
    int continueLine = table.findLineNumber(site[0]);
    int bodyLine = table.findLineNumber(site[1]);
    if (continueLine >= 0 && bodyLine >= 0 && continueLine >= bodyLine) {
      return false;
    }
    CONTINUE_ELSE_SITE.get()[0] = site[0];
    return true;
  }

  /**
   * The goto the last {@link #printContinueElse} proved, for the printer to pin the printed
   * {@code continue;} to: the line alignment has to see the jump to place it on the source's line.
   */
  public static int continueElseSite() {
    return CONTINUE_ELSE_SITE.get()[0];
  }

  /** True when the statement's own last edge is a continue to this loop. */
  private static boolean endsWithContinueEdge(Statement stat, Statement loop) {
    if (stat == null) {
      return false;
    }
    Statement last = stat;
    while (last.getExprents() == null && !last.getStats().isEmpty()) {
      last = last.getStats().get(last.getStats().size() - 1);
    }
    for (StatEdge edge : last.getAllSuccessorEdges()) {
      if (edge.getType() == StatEdge.TYPE_CONTINUE && edge.getDestination() == loop) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when this statement is the last thing printed on the way out of its loop body, so a
   * {@code continue} at its end jumps to the loop head having skipped nothing.
   */
  public static boolean endsLoopBody(Statement stat) {
    return endsLoopBody(stat, false);
  }

  /**
   * {@link #endsLoopBody} through a try: a statement at the end of a try body that ends the loop
   * body still leaves for the loop's head, because the close or finally the fall-out runs is the
   * same one a {@code continue} written there would run.
   */
  public static boolean endsLoopBodyAcrossTry(Statement stat) {
    return endsLoopBody(stat, true);
  }

  private static boolean endsLoopBody(Statement stat, boolean acrossTry) {
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
        // The then arm tails the loop when nothing printable follows; the else arm tails it when
        // the enclosing if itself reaches the loop's end (the sibling guard hoists it out).
        boolean thenTail = ifStatement.getIfstat() == cur
          && (ifStatement.getElsestat() == null || printsNothing(ifStatement.getElsestat()));
        boolean elseTail = ifStatement.getElsestat() == cur && endsLoopBody(ifStatement, acrossTry);
        if (!thenTail && !elseTail) {
          return false;
        }
      } else if (acrossTry && (parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement
                               || parent instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement)) {
        if (parent.getFirst() != cur) {
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

  /** The jump offset a statement's print drops, where its block's old instruction list ends. */
  public static int droppedJumpOffset(Statement stat) {
    if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement basic) {
      java.util.List<Integer> offsets = basic.getBlock().getInstrOldOffsets();
      if (!offsets.isEmpty() && offsets.size() > basic.getBlock().getSeq().length()) {
        return offsets.get(offsets.size() - 1);
      }
    }
    return -1;
  }

  /**
   * The enclosing loop whose own end a labelled continue's jump lands on through a trampoline
   * goto: {@code goto L; L: goto head} is the target's record of a {@code break} out of the loop
   * that ends at L, not of a {@code continue} of the named outer loop, which compiles to the head
   * jump directly. Null when the edge is not that shape.
   */
  public static Statement trampolineBreakLoop(
      org.jetbrains.java.decompiler.modules.decompiler.StatEdge edge, Statement source, int jumpOffset) {
    if (!selector("trampolinebreak") || edge == null || source == null) {
      return null;
    }
    if (edge.getType() != org.jetbrains.java.decompiler.modules.decompiler.StatEdge.TYPE_CONTINUE
        || !edge.labeled || edge.closure == null) {
      return null;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    if (gotos == null) {
      return null;
    }
    if (jumpOffset < 0) {
      // The edge's jump may hang off a nested block the printer does not expose: take the last
      // recorded goto inside the source that itself lands on a goto, which is the trampoline.
      int start = firstOffset(source);
      int end = lastEnd(source);
      if (start < 0 || end <= start) {
        return null;
      }
      for (java.util.Map.Entry<Integer, Integer> entry : gotos.entrySet()) {
        if (entry.getKey() >= start && entry.getKey() <= end && gotos.containsKey(entry.getValue())) {
          jumpOffset = Math.max(jumpOffset, entry.getKey());
        }
      }
      if (jumpOffset < 0) {
        return null;
      }
    }
    Integer trampoline = gotos.get(jumpOffset);
    if (trampoline == null || !gotos.containsKey(trampoline)) {
      return null;
    }
    Integer onward = gotos.get(trampoline);
    if (onward == null
        || !(edge.closure instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement outer)
        || !atLoopContinueTarget(outer, onward)) {
      return null;
    }
    for (Statement cur = source; cur != null && cur != edge.closure; cur = cur.getParent()) {
      if (cur instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop
          && loopOwnEnd(loop) == trampoline) {
        return loop;
      }
    }
    // The loop that ends where the trampoline stands: its own back edge is the instruction just
    // before it, jumping back into the loop. `break label;` leaves the loop right there.
    java.util.Map<Integer, Integer> byEnd = INSTRUCTION_BY_END.get(method);
    Integer backEdge = byEnd == null ? null : byEnd.get(trampoline);
    Integer backTarget = backEdge == null ? null : gotos.get(backEdge);
    if (backEdge != null && backTarget != null && backTarget < backEdge) {
      // The loop whose own head the back edge jumps to: the nearest head above its target. The
      // back edge sits immediately before the break's destination, so this loop is the one the
      // source left; the named outer loop is not it (its head is farther up).
      org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement best = null;
      int bestDistance = Integer.MAX_VALUE;
      for (Statement cur = source; cur != null && cur != edge.closure; cur = cur.getParent()) {
        if (!(cur instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop)) {
          continue;
        }
        int head = loopHeadStartAfter(loop, backTarget);
        if (head < 0) {
          continue;
        }
        int distance = head - backTarget;
        if (distance < bestDistance) {
          best = loop;
          bestDistance = distance;
        }
      }
      if (best != null) {
        return best;
      }
    }
    return null;
  }

  /**
   * The nearest offset of a loop's head at or after the given target: its condition, increment, or
   * body, whichever the back edge can have jumped to. A for-each keeps the iterator increment
   * before the hasNext test, so the increment may sit below the continue target.
   */
  private static int loopHeadStartAfter(org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop, int target) {
    int head = -1;
    for (Exprent exprent : java.util.Arrays.asList(loop.getConditionExprent(), loop.getIncExprent())) {
      if (exprent != null && exprent.bytecode != null && !exprent.bytecode.isEmpty()) {
        int start = exprent.bytecode.nextSetBit(0);
        if (start >= target && (head < 0 || start < head)) {
          head = start;
        }
      }
    }
    int body = firstOffset(loop.getFirst());
    if (body >= target && (head < 0 || body < head)) {
      head = body;
    }
    return head;
  }

  /**
   * True when a labelled continue nested in this loop is really a {@code break label;} of it: its
   * jump lands on the loop's own end, where another goto continues the enclosing loop.
   */
  /** True when the loop's print emits a label a `break label;` can name. */
  public static boolean printsLabel(Statement loop) {
    return loop != null && (loop.isLabeled() || carriesOutwardBreak(loop) || carriesBreakOut(loop)
      || carriesTrampolineBreak(loop));
  }

  public static boolean carriesTrampolineBreak(Statement loop) {
    if (!selector("trampolinebreak") || loop == null) {
      return false;
    }
    return carriesTrampolineBreak(loop, loop);
  }

  private static boolean carriesTrampolineBreak(Statement stat, Statement loop) {
    // Only an edge the jump printer will actually emit as this statement's single exit can become
    // the printed `break label;`; any other edge is printed by its own rule, which would leave
    // the label this decision adds dangling.
    java.util.List<org.jetbrains.java.decompiler.modules.decompiler.StatEdge> successors =
      stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (successors.size() == 1) {
      org.jetbrains.java.decompiler.modules.decompiler.StatEdge edge = successors.get(0);
      if (edge.getType() == org.jetbrains.java.decompiler.modules.decompiler.StatEdge.TYPE_CONTINUE
          && edge.labeled && edge.explicit && !isClosureHidden(edge) && !isJumpSuppressed(stat)
          && !printedBreak(stat) && !isDeferredBreak(edge)
          && !(edge.getDestination() instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement)
          && trampolineBreakLoop(edge, stat, droppedJumpOffset(stat)) == loop) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (carriesTrampolineBreak(child, loop)) {
        return true;
      }
    }
    return false;
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
    int[] site = outwardBreak(exit);
    return site == null ? null : "label" + site[1];
  }

  /**
   * The jump a value return prints as, when the expression is a copy of the method's own final
   * return and a jump out of an enclosing loop lands on it: the source wrote {@code break label;}
   * there, which compiles to exactly that jump. Returns the jump's offset, or -1.
   */
  public static int valuedBreakJump(Exprent exit) {
    if (exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return -1;
    }
    StructMethod method = currentMethod();
    Integer last = method == null ? null : LAST_INSTRUCTION.get(method);
    if (last == null || exit.bytecode.previousSetBit(Integer.MAX_VALUE) != last) {
      return -1;
    }
    int[] site = outwardBreak(exit);
    return site == null ? -1 : site[0];
  }

  /** The jump offset and the enclosing loop's id for a return a loop's outward break lands on. */
  private static int[] outwardBreak(Exprent exit) {
    if (!selector("breaklabel") || exit == null || exit.bytecode == null || exit.bytecode.isEmpty()) {
      return null;
    }
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> gotos = method == null ? null : GOTO_TARGETS.get(method);
    // A valued return starts at its expression's first instruction; the exit's own offsets begin
    // at the return instruction, which the jump does not land on.
    int exitStart = exitStart(exit);
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
          return new int[]{edge.getKey(), loop.id};
        }
      }
    }
    return null;
  }

  /** The first instruction the whole exit covers, its value's operands included. */
  private static int exitStart(Exprent exit) {
    BitSet range = new BitSet();
    exit.getBytecodeRange(range);
    return range.isEmpty() ? -1 : range.nextSetBit(0);
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
    int end = -1;
    if (headStart >= 0) {
      for (java.util.Map.Entry<Integer, Integer> edge : gotos.entrySet()) {
        if (edge.getValue() == headStart) {
          Integer instructionEnd = ends.get(edge.getKey());
          if (instructionEnd != null && instructionEnd > end) {
            end = instructionEnd;
          }
        }
      }
    }
    if (end >= 0) {
      return end;
    }
    // A composed condition names no head to jump back to. Cut the copies of the method's final
    // return out of the loop, and the instruction that then ends its body is the back edge: a
    // jump backwards to the head. A nested loop's back edge does not end where the last exprent
    // does, so it cannot be mistaken for this one.
    BitSet skip = new BitSet();
    Integer last = LAST_INSTRUCTION.get(method);
    java.util.ArrayDeque<Statement> queue = new java.util.ArrayDeque<>();
    queue.add(loop);
    while (!queue.isEmpty()) {
      Statement cur = queue.poll();
      List<Exprent> exprents = cur.getExprents();
      if (exprents != null) {
        for (Exprent e : exprents) {
          for (Exprent part : e.getAllExprents(true, true)) {
            if (part instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent exit
                && exit.getExitType() == org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent.Type.RETURN
                && exit.bytecode != null && !exit.bytecode.isEmpty()
                && last != null && exit.bytecode.previousSetBit(Integer.MAX_VALUE) == last) {
              exit.getBytecodeRange(skip);
            }
          }
        }
      }
      queue.addAll(cur.getStats());
    }
    int bodyEnd = lastEndExcept(loop, skip);
    Integer backEnd = bodyEnd < 0 ? null : ends.get(bodyEnd);
    if (backEnd == null) {
      return -1;
    }
    Integer target = gotos.get(bodyEnd);
    if (target == null) {
      target = BRANCH_STARTS.getOrDefault(method, java.util.Map.of()).get(bodyEnd);
    }
    return target != null && target <= bodyEnd ? backEnd : -1;
  }

  /** Offsets where a bare void return sits anywhere inside this statement. */
  private static java.util.Set<Integer> copiedExitOffsets(Statement stat) {
    StructMethod method = currentMethod();
    Integer last = method == null ? null : LAST_INSTRUCTION.get(method);
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
                && exit.bytecode != null && !exit.bytecode.isEmpty()
                // A bare return is the loop's break outright; a valued one is a copy of the
                // method's final return the break jumps to.
                && (exit.getValue() == null
                    || last != null && exit.bytecode.previousSetBit(Integer.MAX_VALUE) == last)) {
              int start = exitStart(exit);
              if (start >= 0) {
                offsets.add(start);
              }
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
    if (landing == null) {
      return false;
    }
    // A head whose last branch is one of the target's written `continue;` guards, recorded as an
    // else guard behind a try-with-resources close, is a run of guard statements rather than an
    // if/else: its branch lands on the next written test, and the source's rest follows the run.
    java.util.Map<Integer, Integer> elseGuards = CONTINUE_ELSE_GUARDS.get(method);
    if (selector("continueguard") && elseGuards != null && elseGuards.containsKey(lastEnd)) {
      return false;
    }
    if (!isContinueTarget(loop, landing)) {
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
   * The locals the target's table declares inside this switch arm's own instruction range and that
   * the arm declares itself, keyed by slot. A slot that two arms declare is proof the earlier arm
   * was braced: unbraced arms share the switch's block, so javac would have to give the later local
   * a fresh slot instead of reusing a dead one. {@code own} holds the table rows the arm's own
   * declaration exprents own, as {@code {slot, start, end}}; a row of the table belongs to one of
   * them only when both the slot and the start agree, so a pattern variable or a reassignment the
   * table records inside the arm is not counted as the arm's declaration.
   */
  public static java.util.Map<Integer, int[]> targetSlotsDeclaredIn(Statement arm, java.util.List<int[]> own) {
    java.util.Map<Integer, int[]> slots = new java.util.HashMap<>();
    if (!selector("armbraces") || arm == null || own == null || own.isEmpty()) {
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
      .filter(v -> ownedRow(own, v))
      .forEach(v -> slots.put(v.getIndex(), new int[]{v.getStart(), v.getEnd()}));
    return slots;
  }

  private static boolean ownedRow(java.util.List<int[]> own, StructLocalVariableTableAttribute.LocalVariable row) {
    for (int[] candidate : own) {
      if (candidate[0] == row.getIndex() && candidate[1] == row.getStart()) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when the table proves this switch arm's body was a block of its own: a case pattern's
   * variables are declared by the label and close with the switch's block, so their rows are
   * written after every row of a body block that closed where the arm's code ends. When the
   * table writes all of the arm's own rows that end there before all of the pattern's rows that
   * end there, the source braced the arm's body — an unbraced arm shares the switch's block, and
   * javac writes its locals and the pattern's in one ascending run. Rows that end earlier than
   * the arm close at a merge inside the body and say nothing about the arm's scope.
   */
  public static boolean armClosesBeforePatternVars(
      Statement arm, java.util.List<int[]> own, java.util.List<Exprent> values) {
    if (!selector("armbraces") || arm == null || own == null || own.isEmpty() || values == null) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    java.util.Set<Integer> patternSlots = new java.util.HashSet<>();
    for (Exprent value : values) {
      if (value instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent function
          && function.getFuncType() == org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType.INSTANCEOF
          && function.getAllExprents().size() > 2
          && function.getAllExprents().get(2) instanceof org.jetbrains.java.decompiler.modules.decompiler.exps.Pattern pattern) {
        for (org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent var : pattern.getPatternVars()) {
          patternSlots.add(var.getIndex());
        }
      }
    }
    if (patternSlots.isEmpty()) {
      return false;
    }
    int end = lastEnd(arm);
    if (end < 0) {
      return false;
    }
    int ownLast = -1;
    int patternFirst = Integer.MAX_VALUE;
    for (StructLocalVariableTableAttribute.LocalVariable row : table.getVariables().toList()) {
      if (row.getEnd() != end || row.getOrder() < 0) {
        continue;
      }
      if (patternSlots.contains(row.getIndex())) {
        patternFirst = Math.min(patternFirst, row.getOrder());
      } else if (ownedRow(own, row)) {
        ownLast = Math.max(ownLast, row.getOrder());
      }
    }
    return ownLast >= 0 && patternFirst != Integer.MAX_VALUE && ownLast < patternFirst;
  }

  /** Last instruction end covered by a statement, or -1. */
  /** Every recorded goto, keyed by its own start offset, or null without a current method. */
  public static java.util.Map<Integer, Integer> gotosHere() {
    StructMethod method = currentMethod();
    return method == null ? null : GOTO_TARGETS.get(method);
  }

  public static int blockEnd(Statement stat) {
    return stat == null ? -1 : lastEnd(stat);
  }

  /**
   * The run of exprents the target's table proves was a block, or null. A local declared by one of
   * this statement's leading exprents has its slot handed to a later local at the offset its row
   * ends; the exprent whose last instruction ends exactly there is the run's last. Returns
   * {@code {open statement, open exprent, close statement, close exprent or -1 for the whole
   * statement, slot, start, end, next row start, next row end}}. Every boundary is an exprent's
   * own end, so the printer can cut the run out of the exprent lists it was going to print.
   */
  public static int[] handoverRun(List<Statement> stats, int from, int blockEnd) {
    if (!selector("bareblock") || stats == null || from < 0 || from >= stats.size()) {
      return null;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return null;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null || blockEnd <= 0) {
      return null;
    }
    List<Exprent> leading = leadingExprents(stats.get(from));
    if (leading == null) {
      return null;
    }
    List<LocalVariable> rows = table.getVariables().toList();
    for (int a = 0; a < leading.size(); a++) {
      int s1 = lastEndOf(leading.get(a));
      if (s1 < 0) {
        continue;
      }
      for (LocalVariable row : rows) {
        if (row.getStart() != s1 || row.getEnd() <= s1 || row.getEnd() > blockEnd) {
          continue;
        }
        int e1 = row.getEnd();
        // A row that ends exactly where the enclosing block does leaves its closing brace to the
        // construct that prints its own; only the table's entry order can prove a nested block
        // closed on that same brace, so the run is printed only when it does.
        boolean atBlockEnd = e1 == blockEnd;
        if (atBlockEnd && !closedInNestedBlock(row, rows, firstOffset(stats.get(0)))) {
          continue;
        }
        Integer openEnd = HANDOVER_END.get();
        if (openEnd != null && openEnd == e1) {
          // The block this run would print is the one already open: one brace, not two.
          continue;
        }
        LocalVariable next = slotHandover(row.getIndex(), s1, e1);
        if (next == null) {
          continue;
        }
        // A run that starts and ends inside one block is that block's own print, unless the block
        // is an if's head, whose closing boundary is the end of the whole statement.
        if (!(stats.get(from) instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement)
            && printEnd(stats.get(from)) <= e1) {
          continue;
        }
        for (int j = from; j < stats.size(); j++) {
          int end = printEnd(stats.get(j));
          if (end == e1) {
            // The run ends with this statement; the rest of the sequence prints outside. A run that
            // reaches the sequence's end closes on the same brace as the enclosing construct, so it
            // is only printed when the row ends there and the table proved a nested block.
            if ((j == stats.size() - 1) != atBlockEnd) {
              break;
            }
            return new int[]{from, a, j, -1, row.getIndex(), s1, e1, next.getStart(), next.getEnd()};
          }
          if (end > e1) {
            // The boundary is inside this statement's leading exprents: the statement itself is
            // split, and what follows the boundary prints outside the brace.
            List<Exprent> inside = leadingExprents(stats.get(j));
            if (inside != null) {
              for (int b = 0; b < inside.size(); b++) {
                if (printedEnd(inside.get(b)) == e1) {
                  return new int[]{from, a, j, b, row.getIndex(), s1, e1, next.getStart(), next.getEnd()};
                }
              }
            }
            // A nested sequence prints its statements in order: a boundary between two of them
            // is where that sequence's print splits, and the run closes there.
            if (stats.get(j) instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.SequenceStatement nested
                && !nested.isLabeled() && nested.getVarDefinitions().isEmpty()) {
              List<Statement> children = nested.getStats();
              for (int k = 0; k < children.size() - 1; k++) {
                if (printEnd(children.get(k)) == e1) {
                  return new int[]{from, a, j, -1, row.getIndex(), s1, e1, next.getStart(), next.getEnd(), k};
                }
              }
            }
            break;
          }
        }
      }
    }
    return null;
  }

  /**
   * True when the table's entry order proves this row's scope closed in a block of its own that
   * ended where the enclosing block does. javac writes a block's entries when the block closes, so
   * a row written before a local the same enclosing block declared earlier was written after the
   * enclosing block's own locals — only a nested block closing at the same offset puts one before
   * the other. The enclosing block's own locals are the rows that open after its first instruction;
   * a loop's variable opens before it, and a parameter at offset zero, so neither is evidence.
   */
  private static boolean closedInNestedBlock(LocalVariable row, List<LocalVariable> rows, int blockStart) {
    if (row.getOrder() < 0 || blockStart < 0) {
      return false;
    }
    for (LocalVariable other : rows) {
      if (other.getOrder() < 0 || other.getEnd() != row.getEnd()
          || other.getStart() <= blockStart || other.getStart() >= row.getStart()) {
        continue;
      }
      if (other.getOrder() > row.getOrder()) {
        return true;
      }
    }
    return false;
  }

  /**
   * The offset this exprent's statement ends at: its last instruction, plus the {@code pop} that
   * discards a void call's value — that instruction belongs to the statement but no exprent owns
   * it, so the target's table ends the local past it.
   */
  public static int printedEnd(Exprent exprent) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    BitSet pops = method == null ? null : POP_SITES.get(method);
    if (ends == null) {
      return -1;
    }
    int end = lastEndOf(exprent);
    while (end >= 0 && pops != null && pops.get(end)) {
      Integer next = ends.get(end);
      if (next == null || next <= end) {
        break;
      }
      end = next;
    }
    return end;
  }

  /**
   * The offset this statement's own print ends at: the last body instruction of it and its
   * children, ignoring the stores carried by declarations hoisted to its head. Those print as
   * `Type name;` first and their store runs inside the body, so they cannot mark an end.
   */
  public static int printEnd(Statement stat) {
    if (stat == null) {
      return -1;
    }
    int max = -1;
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent instanceof VarExprent var && var.isDefinition()) {
          continue;
        }
        int end = printedEnd(exprent);
        if (end > max) {
          max = end;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      int end = printEnd(child);
      if (end > max) {
        max = end;
      }
    }
    return max;
  }

  /**
   * Prints these exprents, wrapping the runs the target's table proves were blocks. A run is
   * wholly inside the list: the exprent whose last instruction ends where a local's row does, and
   * the exprent whose last instruction ends where the slot is handed over. Runs that cross into a
   * later statement are the sequence printer's, since only it can close them there. A run ending
   * with the list is only ours when {@code closeAtEnd}: otherwise the construct around the list
   * already prints the brace that ends the scope.
   */
  public static org.jetbrains.java.decompiler.util.TextBuffer withBlocks(List<Exprent> exprents, int from, int to,
                                                                         int indent, boolean closeAtEnd) {
    if (!selector("bareblock") || exprents == null) {
      return ExprProcessor.listToJava(exprents == null ? null : exprents.subList(from, to), indent);
    }
    org.jetbrains.java.decompiler.util.TextBuffer buf = new org.jetbrains.java.decompiler.util.TextBuffer();
    int at = from;
    while (at < to) {
      int[] run = innerRun(exprents, at, to, closeAtEnd);
      if (run == null) {
        buf.append(ExprProcessor.listToJava(exprents.subList(at, to), indent));
        break;
      }
      if (run[0] > at) {
        buf.append(ExprProcessor.listToJava(exprents.subList(at, run[0]), indent));
      }
      armSplitDeclarations(run[2], run[3]);
      buf.appendIndent(indent).append("{").appendLineSeparator();
      buf.append(ExprProcessor.listToJava(exprents.subList(run[0], run[1] + 1), indent + 1));
      buf.appendIndent(indent).append("}").appendLineSeparator();
      at = run[1] + 1;
    }
    return buf;
  }

  /**
   * The first block run inside this list as {@code {open exprent, close exprent, start, end}}, or
   * null.
   */
  private static int[] innerRun(List<Exprent> exprents, int from, int to, boolean closeAtEnd) {
    StructMethod method = currentMethod();
    StructLocalVariableTableAttribute table =
      method == null ? null : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return null;
    }
    List<LocalVariable> rows = table.getVariables().toList();
    for (int a = from; a < to; a++) {
      int s1 = lastEndOf(exprents.get(a));
      if (s1 < 0) {
        continue;
      }
      for (LocalVariable row : rows) {
        if (row.getStart() != s1 || row.getEnd() <= s1) {
          continue;
        }
        int e1 = row.getEnd();
        if (slotHandover(row.getIndex(), s1, e1) == null) {
          continue;
        }
        for (int b = a + 1; b < to; b++) {
          if (printedEnd(exprents.get(b)) == e1 && closesCleanly(s1, e1)) {
            // The list's own end is the closing brace of whatever prints it — a try, a loop, an
            // arm — unless nothing does, and then the block the source closed is ours.
            if (b == to - 1) {
              // Nothing after this run proves the boundary: the next row's store has to sit behind
              // the declaration on every path, which a row that merely reuses the slot does not.
              if (!closeAtEnd || slotHandoverAcrossPaths(row.getIndex(), s1, e1) == null) {
                continue;
              }
            }
            return new int[]{a, b, s1, e1};
          }
        }
      }
    }
    return null;
  }

  /** The exprents a statement prints before its own body, or null when its print cannot split. */
  public static List<Exprent> leadingExprents(Statement stat) {
    if (stat == null) {
      return null;
    }
    if (stat.getExprents() != null) {
      return stat.getExprents();
    }
    if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat) {
      Statement head = ifstat.getFirst();
      return head == null ? null : head.getExprents();
    }
    return null;
  }

  /** Last instruction end covered by one exprent, or -1. */
  public static int lastEndOf(Exprent exprent) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> ends = method == null ? null : INSTRUCTION_ENDS.get(method);
    if (ends == null || exprent == null) {
      return -1;
    }
    int max = -1;
    for (Exprent part : exprent.getAllExprents(true, true)) {
      BitSet bits = part.bytecode;
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
    return max;
  }

  /**
   * True when this store is the one the target's table opens a new local with: its slot's previous
   * row ended before it, every path here passes that declaration, and the row starts at this
   * store's own end. The source wrote a declaration here, whatever the tree merged it into.
   */
  public static boolean opensHandover(VarExprent variable) {
    StructMethod method = currentMethod();
    BitSet armed = method == null ? null : SPLIT_DECLARATIONS.get().get(method);
    if (armed == null || armed.isEmpty() || variable == null || variable.bytecode == null) {
      return false;
    }
    int end = lastEndOf(variable);
    return end >= 0 && armed.get(end) && storesInto(method, originalSlot(variable), end);
  }

  /**
   * Registers the declarations a brace closing these locals at {@code end} leaves behind: each
   * slot may be read past the boundary only inside the row that takes it over at a store, and
   * that store now has to print as a declaration. Called just before the brace prints, so no
   * declaration appears where no brace closed the earlier local.
   */
  public static void armSplitDeclarations(int start, int end) {
    StructMethod method = currentMethod();
    BitSet starts = method == null ? null : HANDOVER_STARTS.get(method);
    if (starts == null || starts.isEmpty()) {
      return;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return;
    }
    List<LocalVariable> rows = table.getVariables().toList();
    BitSet armed = SPLIT_DECLARATIONS.get().computeIfAbsent(method, key -> new BitSet());
    for (LocalVariable closed : rows) {
      if (closed.getStart() < start || closed.getStart() >= end || closed.getEnd() != end) {
        continue;
      }
      for (LocalVariable next : rows) {
        if (next.getIndex() == closed.getIndex() && next.getStart() > end && starts.get(next.getStart())) {
          armed.set(next.getStart());
        }
      }
    }
  }

  /** The slot the class file gave this local; the tree's index is a renumbering of it. */
  private static int originalSlot(VarExprent variable) {
    org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor processor = variable.getProcessor();
    Integer original = processor == null ? null : processor.getVarOriginalIndex(variable.getIndex());
    if (original != null) {
      return original;
    }
    return variable.getLVT() != null ? variable.getLVT().getIndex() : variable.getIndex();
  }

  /**
   * True when every local this run declares is out of scope past {@code end}: no use of a slot
   * whose row ends there may follow, unless it falls inside the row that takes the slot over at a
   * store — the printer writes a declaration at that store, so the use has a local to name. A use
   * anywhere else would name a variable the closing brace took out of scope.
   */
  public static boolean closesCleanly(int start, int end) {
    StructMethod method = currentMethod();
    Statement root = methodRoot();
    if (method == null || root == null) {
      return false;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return false;
    }
    List<LocalVariable> rows = table.getVariables().toList();
    BitSet handovers = HANDOVER_STARTS.get(method);
    if (handovers == null) {
      handovers = new BitSet();
    }
    for (LocalVariable closed : rows) {
      if (closed.getStart() < start || closed.getStart() >= end || closed.getEnd() != end) {
        continue;
      }
      if (slotUseOutside(root, closed.getIndex(), end, rows, handovers)) {
        return false;
      }
    }
    return true;
  }

  /** True when a use of this slot lands past {@code end} outside every row opened by a handover. */
  private static boolean slotUseOutside(Statement stat, int slot, int end, List<LocalVariable> rows,
                                        BitSet handovers) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        for (Exprent part : exprent.getAllExprents(true, true)) {
          if (!(part instanceof VarExprent var) || originalSlot(var) != slot) {
            continue;
          }
          int pos = lastEndOf(var);
          if (pos < end) {
            continue;
          }
          boolean placed = false;
          for (LocalVariable row : rows) {
            if (row.getIndex() != slot || row.getStart() <= end || row.getStart() > pos
                || pos >= row.getEnd() || !handovers.get(row.getStart())) {
              continue;
            }
            placed = true;
            break;
          }
          if (!placed) {
            return true;
          }
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (slotUseOutside(child, slot, end, rows, handovers)) {
        return true;
      }
    }
    return false;
  }

  /** The method's root statement, the scope every printed exprent belongs to. */
  private static Statement methodRoot() {
    MethodWrapper wrapper = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    return wrapper == null ? null : wrapper.root;
  }

  /**
   * The later local that takes over this slot after {@code e1}, or null. The table must hold a
   * second row that opens after {@code e1} with a store to the slot right before it, and either it
   * names a different local or every path from the method's entry to that store passes {@code s1} —
   * else the two rows are one variable whose scope the branches cut, and closing a block between
   * them would be wrong.
   */
  public static LocalVariable slotHandover(int slot, int s1, int e1) {
    StructMethod method = currentMethod();
    if (method == null || slot < 0 || s1 < 0 || e1 <= s1) {
      return null;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return null;
    }
    return slotHandover(method, table, slot, s1, e1);
  }

  /**
   * The handover only when every path to the next row's store passes this row's start: the proof
   * a run that ends at its own block's boundary needs, where nothing after the run stands between.
   */
  private static LocalVariable slotHandoverAcrossPaths(int slot, int s1, int e1) {
    StructMethod method = currentMethod();
    if (method == null || slot < 0 || s1 < 0 || e1 <= s1) {
      return null;
    }
    StructLocalVariableTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return null;
    }
    return slotHandover(method, table, slot, s1, e1, true);
  }

  /** The same handover over a known method and table, for callers that already hold both. */
  private static LocalVariable slotHandover(StructMethod method, StructLocalVariableTableAttribute table,
                                            int slot, int s1, int e1) {
    return slotHandover(method, table, slot, s1, e1, false);
  }

  private static LocalVariable slotHandover(StructMethod method, StructLocalVariableTableAttribute table,
                                            int slot, int s1, int e1, boolean acrossPathsRequired) {
    List<LocalVariable> rows = table.getVariables().toList();
    LocalVariable first = null;
    for (LocalVariable row : rows) {
      if (row.getIndex() == slot && row.getStart() == s1 && row.getEnd() == e1) {
        first = row;
        break;
      }
    }
    for (LocalVariable second : rows) {
      if (second.getIndex() != slot || second.getStart() <= e1 || second.getEnd() <= second.getStart()) {
        continue;
      }
      int s2 = second.getStart();
      if (!storesInto(method, slot, s2)) {
        continue;
      }
      if (acrossPathsRequired ? dominates(method, s1, s2)
                              : (!sameVariable(first, second) || dominates(method, s1, s2))) {
        return second;
      }
    }
    return null;
  }

  /**
   * True when the second row provably takes the first row's slot over: it opens after the first
   * row ends, at a store. A second row that names a different local is a different variable, so it
   * needs no dominance proof; that proof only separates one variable's scope a branch cut, and one
   * variable cannot change name or type. Two rows spelled alike stay unproven without it.
   */
  private static boolean handoverPair(StructMethod method, LocalVariable first, LocalVariable second) {
    if (second.getIndex() != first.getIndex() || second.getStart() <= first.getEnd()
        || second.getEnd() <= second.getStart()) {
      return false;
    }
    int s2 = second.getStart();
    return storesInto(method, first.getIndex(), s2)
      && (!sameVariable(first, second) || dominates(method, first.getStart(), s2));
  }

  /** True when the second row may be a second scope of one variable: it keeps the name and type. */
  private static boolean sameVariable(LocalVariable first, LocalVariable second) {
    return first == null
      || (first.getName().equals(second.getName()) && first.getDescriptor().equals(second.getDescriptor()));
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

  /** True when the instruction that falls through to {@code offset} stores into this slot. */
  private static boolean storesInto(StructMethod method, int slot, int offset) {
    java.util.Map<Integer, BitSet> sites = STORE_SITES.get(method);
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    BitSet starts = sites == null ? null : sites.get(slot);
    if (starts == null || ends == null) {
      return false;
    }
    for (int at = starts.nextSetBit(0); at >= 0; at = starts.nextSetBit(at + 1)) {
      Integer end = ends.get(at);
      if (end != null && end == offset) {
        return true;
      }
    }
    return false;
  }

  /**
   * True when every path from the method's entry to {@code to} passes {@code from}. Removing
   * {@code from} from the flow graph decides it: {@code to} is then unreachable only if no path
   * skirts the node. Exception edges count, so an assignment inside a try does not dominate code
   * the catch can reach by jumping past it.
   */
  public static boolean dominates(StructMethod method, int from, int to) {
    Integer entry = METHOD_ENTRY.get(method);
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    if (entry == null || ends == null || from == to || !ends.containsKey(from) || !ends.containsKey(to)) {
      return false;
    }
    // A node no path reaches proves nothing about order; require the target to be live first.
    if (!reaches(method, entry, -1, to)) {
      return false;
    }
    return from == entry || !reaches(method, entry, from, to);
  }

  /** Whether {@code to} is reachable from {@code start} without stepping on {@code forbidden}. */
  private static boolean reaches(StructMethod method, int start, int forbidden, int to) {
    java.util.Map<Integer, Integer> ends = INSTRUCTION_ENDS.get(method);
    if (ends == null) {
      return false;
    }
    java.util.Map<Integer, Integer> gotos = GOTO_TARGETS.get(method);
    java.util.Map<Integer, Integer> branchStarts = BRANCH_STARTS.get(method);
    java.util.Map<Integer, int[]> switches = SWITCH_TARGETS.get(method);
    BitSet noFall = NO_FALLTHROUGH.get(method);
    java.util.List<int[]> excepts = EXCEPTION_RANGES.get(method);
    BitSet seen = new BitSet();
    java.util.ArrayDeque<Integer> work = new java.util.ArrayDeque<>();
    work.add(start);
    while (!work.isEmpty()) {
      int at = work.poll();
      if (at == forbidden || seen.get(at)) {
        continue;
      }
      if (at == to) {
        return true;
      }
      if (!ends.containsKey(at)) {
        continue;
      }
      seen.set(at);
      Integer target = gotos == null ? null : gotos.get(at);
      if (target != null) {
        work.add(target);
      } else {
        Integer branch = branchStarts == null ? null : branchStarts.get(at);
        int[] table = switches == null ? null : switches.get(at);
        if (table != null) {
          for (int destination : table) {
            work.add(destination);
          }
        } else {
          if (branch != null) {
            work.add(branch);
          }
          if ((noFall == null || !noFall.get(at)) && ends.containsKey(ends.get(at))) {
            work.add(ends.get(at));
          }
        }
      }
      if (excepts != null) {
        for (int[] range : excepts) {
          if (range[0] <= at && at < range[1]) {
            work.add(range[2]);
          }
        }
      }
    }
    return false;
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
   * True when the offset is the head an enclosing loop's {@code continue} jumps to, read from the
   * loop's own exprents. This is the narrow test: {@link #enclosingContinueTarget} also calls an
   * offset inside the loop a continue landing, which would hide the join of a switch that is the
   * loop body's last statement — there the update block the switch's {@code break;} lands on is
   * inside the loop by construction.
   */
  public static boolean continuesAtLoopHead(Statement statement, int target) {
    for (Statement cur = statement == null ? null : statement.getParent(); cur != null; cur = cur.getParent()) {
      if (cur instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop
          && atLoopContinueTarget(loop, target)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the offset is where a {@code continue} of this loop actually goes: its head, the
   * increment/condition before the body, or the loop top a load sits up to three bytes before.
   * An offset merely inside the loop is not one — a merged guard's last branch lands on the body.
   */
  private static boolean atLoopContinueTarget(
      org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop, int target) {
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
      int start = head.bytecode.nextSetBit(0);
      if (target <= start && target >= start - 3) {
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

  /**
   * The protected range's start when the target's table proves a catch body starting at this
   * offset was empty (javac writes no parameter entry for an empty body), or -1.
   */
  public static int emptyCatchFrom(int bodyStart) {
    StructMethod method = currentMethod();
    java.util.Map<Integer, Integer> empties = method == null ? null : EMPTY_CATCHES.get(method);
    if (empties == null || bodyStart < 0) {
      return -1;
    }
    Integer from = empties.get(bodyStart);
    return from == null ? -1 : from;
  }

  /** Reads the update a for-each's index loop carried, so the switch's default label is not printed. */
  public static void recordLoopUpdateArm(Statement arm) {
    LOOP_UPDATE_ARMS.add(arm);
  }

  public static boolean isLoopUpdateArm(Statement arm) {
    return arm != null && LOOP_UPDATE_ARMS.contains(arm);
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

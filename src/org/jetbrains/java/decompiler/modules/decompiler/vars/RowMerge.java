// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler.vars;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SynchronizedStatement;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.StatementIterator;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Merges the SSA versions of a slot that the target's local variable table records as one
 * variable.
 *
 * <p>The table is authoritative for identity in one direction only: javac writes one row per
 * variable per lexical range, and two rows of one slot never overlap in the corpus, so two stores
 * the same row covers are one source variable. The reverse direction — separate rows meaning
 * separate variables — is not proven, and no split is attempted here; a variable whose stores span
 * more than one row keeps the versions the data flow gave it.
 *
 * <p>Merging removes a local, which shifts every later local's slot, and that shift is what broke
 * the earlier unguarded attempts. The merge is therefore kept only when simulating the printed
 * order's slot allocation reproduces the target's slot for every declared local: each local takes
 * the lowest free slot at its declaration, parameters keep theirs for the whole method, and a
 * local's slot is released where its block ends. A method whose simulation disagrees is left
 * completely untouched.
 *
 * <p>The pass runs after {@code VarDefinitionHelper} has marked the declarations and after its
 * existing slot-based merge. The expression simplifications have already run by then, so the
 * merged identity cannot change them — in particular no assignment is re-folded into a compound
 * form whose evaluation order the target never had.
 */
public final class RowMerge {
  private RowMerge() {
  }

  /**
   * Plans and applies the same-row merges of one method.
   *
   * @param implicit the indices of locals the printer declares implicitly (parameters, catch
   *                 variables, synchronized monitors); they have no declaration to remove
   */
  public static void merge(VarProcessor varproc, RootStatement root, StructMethod mt, Set<Integer> implicit) {
    if (!RoundTrip.selector("rowmerge") || varproc == null || root == null || mt == null || !varproc.hasLVT()) {
      return;
    }
    StructLocalVariableTableAttribute table = mt.getLocalVariableAttr();
    FullInstructionSequence seq = mt.getInstructionSequence();
    if (table == null || seq == null) {
      return;
    }
    List<LocalVariable> rows = table.getVariables().toList();
    if (rows.size() < 2) {
      return;
    }

    Map<Integer, VarInfo> vars = new TreeMap<>();
    boolean[] unverifiable = {false};
    StatementIterator.iterate(root, exprent -> {
      if (exprent instanceof VarExprent var && !var.isStack() && var.getIndex() >= 0) {
        Integer slot = varproc.getVarOriginalIndex(var.getIndex());
        if (slot == null) {
          // Without the recorded slot the table cannot say which rows cover this variable.
          unverifiable[0] = true;
          return 0;
        }
        VarInfo info = vars.computeIfAbsent(var.getIndex(), index -> new VarInfo(index, slot));
        int end = storeEnd(var, mt, slot, seq);
        if (end >= 0 && !info.stores.contains(end)) {
          info.stores.add(end);
        }
        if (var.isDefinition() && info.definition == null) {
          info.definition = var;
        }
      }
      return 0;
    });
    if (unverifiable[0]) {
      debug(mt, "left untouched: a local has no slot in the table");
      return;
    }

    Map<Integer, List<LocalVariable>> bySlot = new HashMap<>();
    for (LocalVariable row : rows) {
      bySlot.computeIfAbsent(row.getIndex(), k -> new ArrayList<>()).add(row);
    }

    // Every local gets the one row its stores all fall in, if such a row exists. Locals declared
    // implicitly (parameters, catch variables) belong to the row that opens at the method entry.
    Map<LocalVariable, List<VarInfo>> groups = new IdentityHashMap<>();
    for (VarInfo info : vars.values()) {
      info.type = varproc.getVarType(new VarVersionPair(info.index, 0));
      info.row = info.stores.isEmpty()
        ? entryRow(bySlot.get(info.slot), implicit.contains(info.index))
        : coveringRow(bySlot.get(info.slot), info.stores);
      if (info.row != null) {
        groups.computeIfAbsent(info.row, k -> new ArrayList<>()).add(info);
      }
    }

    Map<Integer, List<Integer>> rawStores = rawStores(seq);
    Set<VarExprent> loopInits = loopInits(root);

    Map<Integer, Integer> victims = new TreeMap<>();
    Map<Integer, LocalVariable> survivorRows = new TreeMap<>();
    for (Map.Entry<LocalVariable, List<VarInfo>> entry : groups.entrySet()) {
      LocalVariable row = entry.getKey();
      List<VarInfo> group = entry.getValue();
      if (group.size() < 2) {
        continue;
      }
      // The proof is complete only when every store the method makes to this slot has exactly one
      // row around it; a store outside the rows, or on a boundary two rows claim, proves nothing.
      if (!allCovered(bySlot.get(row.getIndex()), rawStores.getOrDefault(row.getIndex(), List.of()))) {
        debug(mt, "slot " + row.getIndex() + ": a store is not covered by exactly one row");
        continue;
      }
      VarInfo survivor = null;
      boolean ok = true;
      for (VarInfo info : group) {
        if (info.type == null || !joinable(survivor == null ? info.type : survivor.type, info.type)) {
          ok = false;
          break;
        }
        if (survivor == null || before(info, survivor, implicit)) {
          survivor = info;
        }
      }
      if (!ok) {
        debug(mt, "slot " + row.getIndex() + ": the versions have no common type");
        continue;
      }
      Map<Integer, Integer> planned = new TreeMap<>();
      for (VarInfo info : group) {
        if (info == survivor) {
          continue;
        }
        if (!removable(info, implicit, loopInits)) {
          ok = false;
          break;
        }
        planned.put(info.index, survivor.index);
      }
      if (!ok) {
        debug(mt, "slot " + row.getIndex() + ": a version has no declaration to remove");
        continue;
      }
      victims.putAll(planned);
      survivorRows.put(survivor.index, row);
    }

    if (victims.isEmpty()) {
      return;
    }

    Order order = new Order(victims.keySet());
    order.walk(root);
    if (!inScope(order, vars, victims)) {
      debug(mt, "merge reverted: a merged store prints outside the declaration's block");
      return;
    }
    if (!slotsMatch(order, paramSlots(mt), varproc, mt)) {
      debug(mt, "merge reverted: the printed slots would not match the table");
      return;
    }

    apply(root, victims);
    nameFromRow(varproc, survivorRows);
    debug(mt, "merged " + victims);
  }

  /**
   * A merge without a shared declaration is only printed correctly when every mention of the
   * absorbed version lies inside the block that declares the survivor; otherwise the source would
   * name a local outside its scope. The table proves identity, not that our block structure
   * already contains both halves.
   */
  private static boolean inScope(Order order, Map<Integer, VarInfo> vars, Map<Integer, Integer> victims) {
    Map<Integer, Statement> scopes = new HashMap<>();
    for (Map.Entry<Integer, Integer> entry : victims.entrySet()) {
      VarInfo survivor = vars.get(entry.getValue());
      Statement scope = survivor != null && survivor.definition != null
        ? order.declarationScopes.get(survivor.definition)
        : null;
      // An implicit declaration (a parameter or catch variable) is scoped to the whole method.
      scopes.put(entry.getKey(), scope == null ? order.root : scope);
    }
    boolean[] ok = {true};
    StatementIterator.iterate(order.root, exprent -> {
      if (exprent instanceof VarExprent var && !var.isStack() && victims.containsKey(var.getIndex())) {
        Statement owner = order.owners.get(var);
        Statement scope = scopes.get(var.getIndex());
        if (owner == null || scope == null || !isAncestorOrSelf(scope, owner)) {
          ok[0] = false;
        }
      }
      return 0;
    });
    return ok[0];
  }

  private static boolean isAncestorOrSelf(Statement ancestor, Statement stat) {
    for (Statement current = stat; current != null; current = current.getParent()) {
      if (current == ancestor) {
        return true;
      }
    }
    return false;
  }

  /**
   * The table names the variable, not the SSA version: the merged local is the row's variable, so
   * the name lookup has to use the row's own version pair.
   */
  private static void nameFromRow(VarProcessor varproc, Map<Integer, LocalVariable> survivorRows) {
    if (varproc.getVarVersions() == null) {
      return;
    }
    Map<Integer, VarVersionPair> originals = varproc.getVarVersions().getMapOriginalVarIndices();
    for (Map.Entry<Integer, LocalVariable> entry : survivorRows.entrySet()) {
      originals.put(entry.getKey(), entry.getValue().getVersion());
    }
  }

  // *****************************************************************************
  // evidence
  // *****************************************************************************

  /** One local's identity evidence: its recorded slot, the rows of its stores and its declaration. */
  private static final class VarInfo {
    final int index;
    final int slot;
    final List<Integer> stores = new ArrayList<>();
    LocalVariable row;
    VarExprent definition;
    VarType type;

    VarInfo(int index, int slot) {
      this.index = index;
      this.slot = slot;
    }

    /** The end of the first store, or {@code Integer.MAX_VALUE} for a local with no store. */
    int declaredAt() {
      int min = Integer.MAX_VALUE;
      for (int store : stores) {
        min = Math.min(min, store);
      }
      return min;
    }
  }

  /**
   * The end offset of the store this var exprent performs, or -1. The last instruction the exprent
   * covers is the store itself: the value operands evaluate first.
   */
  private static int storeEnd(VarExprent var, StructMethod mt, int slot, FullInstructionSequence seq) {
    BitSet bytecode = var.bytecode;
    if (bytecode == null || bytecode.isEmpty()) {
      return -1;
    }
    int offset = RoundTrip.lastInstructionStart(bytecode, mt);
    Integer index = offset < 0 ? null : seq.offsetToIndex().get(offset);
    if (index == null || index < 0 || index >= seq.length()) {
      return -1;
    }
    Instruction instr = seq.getInstr(index);
    boolean store = instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore
      || instr.opcode == CodeConstants.opc_iinc;
    if (!store || instr.operand(0) != slot) {
      return -1;
    }
    return instr.startOffset + instr.length;
  }

  /** The end offsets of every store instruction the method makes to this slot. */
  private static Map<Integer, List<Integer>> rawStores(FullInstructionSequence seq) {
    Map<Integer, List<Integer>> stores = new HashMap<>();
    for (Instruction instr : seq) {
      if (instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore
        || instr.opcode == CodeConstants.opc_iinc) {
        stores.computeIfAbsent(instr.operand(0), k -> new ArrayList<>()).add(instr.startOffset + instr.length);
      }
    }
    return stores;
  }

  /** The one row all these stores fall in, or null when one of them falls outside or in a second. */
  private static LocalVariable coveringRow(List<LocalVariable> rows, List<Integer> stores) {
    if (rows == null || rows.isEmpty() || stores.isEmpty()) {
      return null;
    }
    LocalVariable row = null;
    for (int store : stores) {
      LocalVariable found = rowAt(rows, store);
      if (found == null || (row != null && row != found)) {
        return null;
      }
      row = found;
    }
    return row;
  }

  /** The row of this slot that opens at the method entry, for an implicitly declared local. */
  private static LocalVariable entryRow(List<LocalVariable> rows, boolean implicit) {
    if (rows == null || !implicit) {
      return null;
    }
    for (LocalVariable row : rows) {
      if (row.getStart() == 0) {
        return row;
      }
    }
    return null;
  }

  /**
   * The row of this slot covering the store end, or null when none does or two rows claim it. A
   * range is half-open in the source but its end offset is the first instruction past the last
   * instruction of the scope, so a store may end exactly on it; the row that opens there owns
   * that store.
   */
  private static LocalVariable rowAt(List<LocalVariable> rows, int offset) {
    if (rows == null) {
      return null;
    }
    LocalVariable best = null;
    int containing = 0;
    for (LocalVariable row : rows) {
      if (offset < row.getStart() || offset > row.getEnd()) {
        continue;
      }
      containing++;
      if (best == null || row.getStart() > best.getStart()) {
        best = row;
      }
    }
    if (best == null || (containing > 1 && offset != best.getStart())) {
      return null;
    }
    return best;
  }

  private static boolean allCovered(List<LocalVariable> rows, List<Integer> stores) {
    for (int store : stores) {
      if (rowAt(rows, store) == null) {
        return false;
      }
    }
    return true;
  }

  private static boolean joinable(VarType a, VarType b) {
    return a.equals(b) || VarType.join(a, b) != null;
  }

  /** True when {@code a} is the version that should carry the merged declaration. */
  private static boolean before(VarInfo a, VarInfo b, Set<Integer> implicit) {
    boolean implicitA = implicit.contains(a.index);
    boolean implicitB = implicit.contains(b.index);
    if (implicitA != implicitB) {
      return implicitA;
    }
    int declaredA = a.declaredAt();
    int declaredB = b.declaredAt();
    return declaredA != declaredB ? declaredA < declaredB : a.index < b.index;
  }

  /** True when this version's declaration can be dropped without leaving a broken statement. */
  private static boolean removable(VarInfo info, Set<Integer> implicit, Set<VarExprent> loopInits) {
    if (implicit.contains(info.index) || info.definition == null) {
      return false;
    }
    // A bare `for (int x; …)` head prints the var exprent itself; dropping the declaration would
    // leave `for (x; …)`.
    return !loopInits.contains(info.definition);
  }

  /** The var exprents standing as a loop's own init exprent (a declaration with no assignment). */
  private static Set<VarExprent> loopInits(Statement stat) {
    Set<VarExprent> inits = new HashSet<>();
    collectLoopInits(stat, inits);
    return inits;
  }

  private static void collectLoopInits(Statement stat, Set<VarExprent> inits) {
    if (stat instanceof DoStatement loop && loop.getInitExprent() instanceof VarExprent var) {
      inits.add(var);
    }
    for (Statement child : stat.getStats()) {
      collectLoopInits(child, inits);
    }
  }

  // *****************************************************************************
  // printed order and slot simulation
  // *****************************************************************************

  private static int paramSlots(StructMethod mt) {
    int slots = mt.hasModifier(CodeConstants.ACC_STATIC) ? 0 : 1;
    for (VarType param : MethodDescriptor.parseDescriptor(mt.getDescriptor()).params) {
      slots += param.stackSize;
    }
    return slots;
  }

  /** A declaration in printed order, or the closing of the scope that holds one. */
  private static final class Event {
    final int variable;
    final int scope;

    Event(int variable, int scope) {
      this.variable = variable;
      this.scope = scope;
    }
  }

  /** The method's declarations in the order the printer emits them, with their scopes. */
  private static final class Order {
    final Set<Integer> victims;
    final List<Event> events = new ArrayList<>();
    final Map<Statement, Integer> scopes = new IdentityHashMap<>();
    final Map<Integer, Statement> scopeStatements = new HashMap<>();
    final Map<VarExprent, Statement> owners = new IdentityHashMap<>();
    final Map<VarExprent, Statement> declarationScopes = new IdentityHashMap<>();
    final Set<VarExprent> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    Statement root;

    Order(Set<Integer> victims) {
      this.victims = victims;
    }

    void walk(Statement stat) {
      if (root == null) {
        root = stat;
      }
      int scope = scopeOf(stat);
      for (Exprent exprent : stat.getVarDefinitions()) {
        declaration(exprent, stat, scope);
      }
      switch (stat.type) {
        case ROOT: {
          if (stat.getFirst() != null) {
            walk(stat.getFirst());
          }
          break;
        }
        case SEQUENCE: {
          for (Statement child : stat.getStats()) {
            walk(child);
          }
          break;
        }
        case BASIC_BLOCK: {
          List<Exprent> exprents = stat.getExprents();
          if (exprents != null) {
            for (Exprent exprent : exprents) {
              declaration(exprent, stat, scope);
            }
          }
          for (Statement child : stat.getStats()) {
            walk(child);
          }
          break;
        }
        case IF: {
          IfStatement ifstat = (IfStatement)stat;
          if (ifstat.getFirst() != null) {
            walk(ifstat.getFirst());
          }
          declaration(ifstat.getHeadexprent(), stat, scope);
          if (ifstat.getIfstat() != null) {
            walk(ifstat.getIfstat());
          }
          if (ifstat.getElsestat() != null) {
            walk(ifstat.getElsestat());
          }
          break;
        }
        case DO: {
          DoStatement loop = (DoStatement)stat;
          Exprent init = loop.getInitExprent();
          if (init != null) {
            // A for header's declaration is scoped to the loop itself.
            declaration(init, loop, scope(loop));
          }
          if (loop.getFirst() != null) {
            walk(loop.getFirst());
          }
          break;
        }
        case SWITCH: {
          SwitchStatement sw = (SwitchStatement)stat;
          if (sw.getFirst() != null) {
            walk(sw.getFirst());
          }
          declaration(sw.getHeadexprent(), stat, scope);
          for (Statement arm : sw.getCaseStatements()) {
            walk(arm);
          }
          break;
        }
        case TRY_CATCH: {
          CatchStatement tryCatch = (CatchStatement)stat;
          if (tryCatch.getFirst() != null) {
            walk(tryCatch.getFirst());
          }
          for (int i = 1; i < tryCatch.getStats().size(); i++) {
            Statement handler = tryCatch.getStats().get(i);
            if (i - 1 < tryCatch.getVars().size()) {
              declaration(tryCatch.getVars().get(i - 1), handler, scope(handler));
            }
            walk(handler);
          }
          break;
        }
        case CATCH_ALL: {
          CatchAllStatement catchAll = (CatchAllStatement)stat;
          if (catchAll.getFirst() != null) {
            walk(catchAll.getFirst());
          }
          if (catchAll.getHandler() != null) {
            walk(catchAll.getHandler());
          }
          break;
        }
        case SYNCHRONIZED: {
          SynchronizedStatement sync = (SynchronizedStatement)stat;
          if (sync.getFirst() != null) {
            walk(sync.getFirst());
          }
          if (sync.getBody() != null) {
            walk(sync.getBody());
          }
          break;
        }
        default: {
          for (Statement child : stat.getStats()) {
            walk(child);
          }
        }
      }
      // Resources, conditions and case guards print somewhere in the statement; their mentions
      // only matter for the scope check, not for the declaration order.
      for (Exprent statExprent : stat.getStatExprents()) {
        mention(statExprent, stat);
      }
      close(stat);
    }

    private void mention(Exprent exprent, Statement owner) {
      if (exprent == null) {
        return;
      }
      List<Exprent> all = exprent.getAllExprents(true);
      all.add(exprent);
      for (Exprent inner : all) {
        if (inner instanceof VarExprent var && !var.isStack()) {
          owners.putIfAbsent(var, owner);
        }
      }
    }

    /** Records the locals this exprent mentions and the declarations it prints, in order. */
    void declaration(Exprent exprent, Statement owner, int scope) {
      if (exprent == null) {
        return;
      }
      List<Exprent> all = exprent.getAllExprents(true);
      all.add(exprent);
      for (Exprent inner : all) {
        if (inner instanceof VarExprent var && !var.isStack()) {
          owners.putIfAbsent(var, owner);
          if (var.isDefinition() && seen.add(var) && !victims.contains(var.getIndex())) {
            declarationScopes.put(var, scopeStatements.get(scope));
            events.add(new Event(var.getIndex(), scope));
          }
        }
      }
    }

    void close(Statement stat) {
      Integer id = scopes.get(stat);
      if (id != null) {
        events.add(new Event(-1, id));
      }
    }

    int scope(Statement stat) {
      Integer id = scopes.get(stat);
      if (id == null) {
        id = scopes.size();
        scopes.put(stat, id);
        scopeStatements.put(id, stat);
      }
      return id;
    }

    /** The nearest enclosing statement whose own print opens a block around the declaration. */
    int scopeOf(Statement stat) {
      Statement current = stat;
      while (true) {
        if (current.isLabeled()) {
          return scope(current);
        }
        Statement parent = current.getParent();
        if (parent == null || bracedChild(parent, current)) {
          return scope(current);
        }
        current = parent;
      }
    }

    private static boolean bracedChild(Statement parent, Statement child) {
      switch (parent.type) {
        case DO: {
          return ((DoStatement)parent).getFirst() == child;
        }
        case IF: {
          IfStatement ifstat = (IfStatement)parent;
          return ifstat.getIfstat() == child || ifstat.getElsestat() == child;
        }
        case SWITCH: {
          return ((SwitchStatement)parent).getCaseStatements().contains(child);
        }
        case TRY_CATCH:
        case CATCH_ALL: {
          // The try body and every handler print inside braces of their own.
          return true;
        }
        case SYNCHRONIZED: {
          return ((SynchronizedStatement)parent).getBody() == child;
        }
        default: {
          return false;
        }
      }
    }
  }

  /**
   * True when allocating slots in printed order reproduces the table's slot for every declared
   * local. Parameters hold their slots for the whole method; any other local takes the lowest free
   * slot wide enough at its declaration and releases it when its block closes.
   */
  private static boolean slotsMatch(Order order, int paramSlots, VarProcessor varproc, StructMethod mt) {
    Map<Integer, Integer> closeAt = new HashMap<>();
    for (int i = 0; i < order.events.size(); i++) {
      Event event = order.events.get(i);
      if (event.variable < 0) {
        closeAt.put(event.scope, i);
      }
    }

    boolean[] used = new boolean[paramSlots + 128];
    for (int i = 0; i < paramSlots; i++) {
      used[i] = true;
    }
    List<int[]> live = new ArrayList<>();
    for (int i = 0; i < order.events.size(); i++) {
      Event event = order.events.get(i);
      if (event.variable < 0) {
        continue;
      }
      for (Iterator<int[]> it = live.iterator(); it.hasNext(); ) {
        int[] scope = it.next();
        if (scope[2] < i) {
          for (int slot = scope[0]; slot < scope[0] + scope[1]; slot++) {
            used[slot] = false;
          }
          it.remove();
        }
      }

      Integer expected = varproc.getVarOriginalIndex(event.variable);
      if (expected == null) {
        debug(mt, "local " + event.variable + " has no slot in the table");
        return false;
      }
      VarType type = varproc.getVarType(new VarVersionPair(event.variable, 0));
      int width = type == null || type.stackSize <= 0 ? 1 : type.stackSize;
      int slot = firstFree(used, paramSlots, width);
      if (slot < 0) {
        return false;
      }
      if (slot != expected) {
        debug(mt, "local " + event.variable + " would take slot " + slot + ", table says " + expected);
        return false;
      }
      for (int at = slot; at < slot + width; at++) {
        used[at] = true;
      }
      live.add(new int[]{slot, width, closeAt.getOrDefault(event.scope, order.events.size())});
    }
    return true;
  }

  private static int firstFree(boolean[] used, int from, int width) {
    for (int slot = from; slot + width <= used.length; slot++) {
      boolean free = true;
      for (int at = slot; at < slot + width; at++) {
        if (used[at]) {
          free = false;
          break;
        }
      }
      if (free) {
        return slot;
      }
    }
    return -1;
  }

  // *****************************************************************************
  // application
  // *****************************************************************************

  private static void apply(RootStatement root, Map<Integer, Integer> victims) {
    // The declarations are dropped before the indices change: the removal keys on the versions'
    // own indices, and the rewrite below turns every remaining mention into the survivor's.
    removeDeclarations(root, victims.keySet());
    StatementIterator.iterate(root, exprent -> {
      if (exprent instanceof VarExprent var && !var.isStack()) {
        Integer to = victims.get(var.getIndex());
        if (to != null) {
          var.setIndex(to);
          var.setVersion(0);
        }
      }
      return 0;
    });
  }

  /** Drops the victims' declarations; their first store stays where it was, as an assignment. */
  private static void removeDeclarations(Statement stat, Set<Integer> victims) {
    for (Iterator<Exprent> it = stat.getVarDefinitions().iterator(); it.hasNext(); ) {
      Exprent exprent = it.next();
      if (exprent instanceof VarExprent var && !var.isStack() && victims.contains(var.getIndex())) {
        it.remove();
      }
    }
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Iterator<Exprent> it = exprents.iterator(); it.hasNext(); ) {
        Exprent exprent = it.next();
        if (exprent instanceof VarExprent var && !var.isStack() && victims.contains(var.getIndex())) {
          it.remove();
          continue;
        }
        unmark(exprent, victims);
      }
    }
    else {
      for (Exprent exprent : stat.getStatExprents()) {
        unmark(exprent, victims);
      }
    }
    for (Statement child : stat.getStats()) {
      removeDeclarations(child, victims);
    }
  }

  private static void unmark(Exprent exprent, Set<Integer> victims) {
    if (exprent == null) {
      return;
    }
    List<Exprent> all = exprent.getAllExprents(true);
    all.add(exprent);
    for (Exprent inner : all) {
      if (inner instanceof VarExprent var && !var.isStack() && var.isDefinition()
        && victims.contains(var.getIndex())) {
        var.setDefinition(false);
      }
    }
  }

  private static void debug(StructMethod mt, String message) {
    if (System.getenv("NEUROFLOWER_ROWMERGE") != null) {
      System.err.println("rowmerge " + (mt == null ? "?" : mt.getName() + mt.getDescriptor()) + ": " + message);
    }
  }
}

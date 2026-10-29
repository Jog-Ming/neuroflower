// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SynchronizedStatement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * javac allocates local slots in declaration order. A source that declares a variable without an
 * initializer before another local's declaration still gives it the lower slot, even though our
 * printer emits the bare declaration at its first assignment. The target's LocalVariableTable is
 * the evidence: when a bare declaration sits after a declaration whose slot is higher, the source
 * must have written it earlier.
 *
 * <p>Moving a declaration within one exprent list never changes evaluation order, so it needs no
 * analysis. Moving it across statements to the start of its sequence widens the region in which
 * the variable is in scope: the hoist is only taken when no use of the variable is reachable
 * from the sequence start without an assignment (a definite-assignment walk over the statement
 * structure), when no other local shares its printed name, and when the region contains no field
 * access of that name that the new local would capture.
 */
public final class LocalDeclarationOrder {
  private LocalDeclarationOrder() {
  }

  public static void reorder(Statement root) {
    MethodWrapper wrapper = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    VarProcessor varproc = wrapper == null ? null : wrapper.varproc;
    String method = wrapper == null ? "?" : wrapper.classStruct.qualifiedName + "." + wrapper.methodStruct.getName()
      + wrapper.methodStruct.getDescriptor();

    NameTable names = NameTable.build(root);
    hoistAcrossStatements(root, varproc, names, method);
    reorderWithinList(root, varproc);
    hoistToPrintedOrder(root, varproc, names, method);
  }

  /**
   * A local whose table entry starts before the block that assigns it was declared bare at the
   * enclosing level: the source wrote `T v;` above the loop and assigned inside it. Only the
   * declaration moves; the value is still computed where it was printed.
   */
  private static void hoistNestedOut(Statement seq, VarProcessor varproc, NameTable names, String method) {
    if (!RoundTrip.selector("decllvt")) {
      return;
    }
    int maxSlot = -1;
    for (Exprent definition : seq.getVarDefinitions()) {
      maxSlot = Math.max(maxSlot, targetSlot(definition));
    }
    List<Statement> children = new ArrayList<>(seq.getStats());
    for (Statement child : children) {
      Statement body = nestedBody(child);
      if (body != null) {
        // Everything printed before this block counts as already declared: a sibling's plain
        // statements print above the switch just as the sequence's own definitions do.
        for (Statement sibling : siblingsBefore(children, child)) {
          maxSlot = Math.max(maxSlot, printedDeclarationsUpTo(sibling));
        }
        List<Exprent> candidates = new ArrayList<>(body.getVarDefinitions());
        List<Exprent> firstExprents = body.getStats().isEmpty() ? null : body.getStats().get(0).getExprents();
        if (firstExprents != null) {
          candidates.addAll(firstExprents);
        }
        if (body.getExprents() != null) {
          candidates.addAll(body.getExprents());
        }
        // A catch parameter is declared after the try body, and javac hands it the lowest slot
        // free at the handler; one above the local's whole slot range proves the local was still
        // in scope there, so the source declared it before the try.
        java.util.List<Integer> handlerSlots = child instanceof CatchStatement catchStatement
          ? catchParameterSlots(catchStatement) : java.util.Collections.emptyList();
        for (Exprent exprent : candidates) {
          VarExprent var = definedVar(exprent);
          if (var == null || !isRealDefinition(var) || var.getLVT() == null) {
            continue;
          }
          int slot = var.getLVT().getIndex();
          // The target gave this local a slot below one that prints before the block: the source
          // declared it further up the sequence, bare, and assigned it here. A try body is not
          // taken by this rule: the slots the sequence saw before it may come from a sibling
          // try's own body, which is not declared at this level.
          boolean belowPrinted = slot >= 0 && slot < maxSlot && !(child instanceof CatchStatement);
          boolean reservedAtHandler = slot >= 0 && belowHandlerSlot(handlerSlots, var);
          if (!belowPrinted && !reservedAtHandler) {
            continue;
          }
          // A discontinuous table row of the same name and slot is the same source variable, so
          // its later range's declaration is not a second name the hoist could capture.
          if ((!names.uniqueName(var) && !names.sameSlotName(var)) || mentionsField(seq, var.getName())) {
            debug(method, var, "rejected: nested declaration would capture a name");
            continue;
          }
          debug(method, var, (belowPrinted
            ? "hoisted out of a nested block: slot " + slot + " below " + maxSlot
            : "hoisted out of a try: slot " + slot + " still reserved at a handler"));
          Exprent declaration;
          if (exprent == var) {
            removeIdentity(body.getVarDefinitions(), exprent);
            if (firstExprents != null) {
              removeIdentity(firstExprents, exprent);
            }
            if (body.getExprents() != null) {
              removeIdentity(body.getExprents(), exprent);
            }
            declaration = exprent;
          } else {
            declaration = var.copy();
            var.setDefinition(false);
          }
          // A switch head prints right after its siblings' statements, so the declaration belongs
          // beside them; for a loop or if body the sequence's own definitions stay the target.
          List<Exprent> target = child instanceof SwitchStatement
            ? insertionList(seq, child)
            : seq.getVarDefinitions();
          insertByTargetSlot(target, declaration);
          // The variable's other alive ranges no longer print their own declaration: one `T v;`
          // stands above and each range's store is a plain assignment.
          absorbSplitRanges(seq, (VarExprent) declaration);
        }
      }
      for (Exprent definition : child.getVarDefinitions()) {
        maxSlot = Math.max(maxSlot, targetSlot(definition));
      }
      if (child.type == Statement.StatementType.BASIC_BLOCK && child.getExprents() != null) {
        for (Exprent exprent : child.getExprents()) {
          maxSlot = Math.max(maxSlot, targetSlot(exprent));
        }
      }
    }
  }

  /**
   * javac allocates a local's slot when its declaration statement is reached, so the class file's
   * local table records where in the source each declaration was written. A declaration printed
   * below a declaration the table gives a higher slot was therefore written above it — bare, with
   * its first store left where it was. It is moved to the landing point the table proves, just
   * above the first printed declaration with a higher slot, when that point is in a block that
   * encloses the variable's store.
   */
  private static void hoistToPrintedOrder(Statement root, VarProcessor varproc, NameTable names, String method) {
    if (!RoundTrip.selector("decllvt")) {
      return;
    }
    List<DeclPos> order = new ArrayList<>();
    collectPrintedOrder(root, order);
    List<DeclPos> candidates = new ArrayList<>();
    for (DeclPos position : order) {
      if (position.list != null && position.var.getLVT() != null && position.slot >= 0) {
        candidates.add(position);
      }
    }
    // Ascending slot order: a declaration moved earlier is itself a landing point for the next.
    candidates.sort((a, b) -> Integer.compare(a.slot, b.slot));
    for (DeclPos candidate : candidates) {
      VarExprent var = candidate.var;
      if (!isRealDefinition(var)) {
        continue;
      }
      int index = indexOfPosition(order, candidate);
      if (index < 0) {
        continue;
      }
      DeclPos anchor = null;
      int anchorIndex = -1;
      for (int i = 0; i < index; i++) {
        DeclPos position = order.get(i);
        if (position.slot > candidate.slot && anchorLiveAt(position, candidate)) {
          anchor = position;
          anchorIndex = i;
          break;
        }
      }
      if (anchor == null) {
        continue;
      }
      if (!names.uniqueName(var) && !names.sameSlotName(var)) {
        debug(method, var, "rejected: another local prints as " + var.getName());
        continue;
      }
      if (RoundTrip.isCatchParameter(new VarVersionPair(var))) {
        debug(method, var, "rejected: the catch header declares it");
        continue;
      }
      if (mentionsField(root, var.getName())) {
        debug(method, var, "rejected: the method names a field " + var.getName());
        continue;
      }
      int deadEnd = slotReuseEnd(var);
      if (deadEnd >= 0 && !landsAfterDeadScope(anchor, deadEnd)) {
        debug(method, var, "rejected: landing point lies inside the dead scope " + deadEnd);
        continue;
      }
      if (!inScope(anchor, candidate.owner)) {
        debug(method, var, "rejected: landing point is outside the declaration's scope chain");
        continue;
      }
      if (!new Da(var).check(root)) {
        debug(method, var, "rejected: not definitely assigned at a use");
        continue;
      }
      Exprent declaration;
      if (candidate.top == var) {
        removeIdentity(candidate.list, candidate.top);
        declaration = candidate.top;
        declaration.bytecode = null;
      } else {
        declaration = var.copy();
        // A bare declaration has no instruction of its own. Carrying the store's offsets would
        // make the block-scope printer read the declaration as the statement that ends there.
        declaration.bytecode = null;
        var.setDefinition(false);
      }
      DeclPos inserted;
      Statement head = headLanding(candidate, order, anchorIndex);
      if (head != null && (deadEnd < 0 || firstOffsetAtLeast(head, deadEnd))) {
        // The landing point opens the head of a block that encloses the store: the source wrote
        // the declaration before that block, so it prints beside the block, not inside it. The
        // wider scope is what the target's slots for later locals record.
        int start = firstPositionIndex(order, head);
        insertByTargetSlot(head.getVarDefinitions(), declaration);
        inserted = new DeclPos((VarExprent)declaration, declaration, head.getVarDefinitions(),
          head, candidate.slot);
        order.add(start, inserted);
        debug(method, var, "hoisted to the head of a " + head.type + " before slot-" + anchor.slot);
      } else if (anchor.list == null) {
        // A loop header's declaration prints where the loop is written: the variable was declared
        // just above the loop, so it goes into the loop's own definitions.
        insertByTargetSlot(anchor.owner.getVarDefinitions(), declaration);
        inserted = new DeclPos((VarExprent)declaration, declaration, anchor.owner.getVarDefinitions(),
          anchor.owner, candidate.slot);
        order.add(anchorIndex, inserted);
        debug(method, var, "hoisted to the loop header before slot-" + anchor.slot);
      } else {
        int at = indexOfIdentity(anchor.list, anchor.top);
        anchor.list.add(at < 0 ? anchor.list.size() : at, declaration);
        inserted = new DeclPos((VarExprent)declaration, declaration, anchor.list, anchor.owner,
          candidate.slot);
        order.add(anchorIndex, inserted);
        debug(method, var, "hoisted to the printed order before slot-" + anchor.slot);
      }
      // The other alive ranges of the same source variable lose their own declarations.
      if (declaration instanceof VarExprent keptVar) {
        absorbSplitRanges(root, keptVar);
      }
    }
  }

  /**
   * The outermost enclosing statement whose first declaration is the anchor itself: everything
   * printed before it has a lower slot, so a declaration can open that block's head without
   * disturbing the order, and the block's start is a wider scope than the store's own.
   */
  private static Statement headLanding(DeclPos candidate, List<DeclPos> order, int anchorIndex) {
    int lastLower = -1;
    for (int i = 0; i < anchorIndex; i++) {
      int slot = order.get(i).slot;
      if (slot >= 0 && slot < candidate.slot) {
        lastLower = i;
      }
    }
    List<Statement> ancestors = new ArrayList<>();
    for (Statement stat = candidate.owner; stat != null; stat = stat.getParent()) {
      ancestors.add(stat);
    }
    for (int i = ancestors.size() - 1; i >= 0; i--) {
      Statement head = ancestors.get(i);
      if (firstPositionIndex(order, head) == anchorIndex && anchorIndex > lastLower) {
        return head;
      }
    }
    return null;
  }

  /** The first printed declaration inside this statement's subtree, as an index in the order. */
  private static int firstPositionIndex(List<DeclPos> order, Statement head) {
    for (int i = 0; i < order.size(); i++) {
      if (isAncestor(head, order.get(i).owner)) {
        return i;
      }
    }
    return -1;
  }

  private static boolean isAncestor(Statement ancestor, Statement stat) {
    for (Statement s = stat; s != null; s = s.getParent()) {
      if (s == ancestor) {
        return true;
      }
    }
    return false;
  }

  private static boolean firstOffsetAtLeast(Statement head, int offset) {
    int first = RoundTrip.firstOffset(head);
    return first >= 0 && first >= offset;
  }

  private static int indexOfPosition(List<DeclPos> order, DeclPos position) {
    for (int i = 0; i < order.size(); i++) {
      if (order.get(i) == position) {
        return i;
      }
    }
    return -1;
  }

  /**
   * Every declaration in the order the printer emits them: a statement's own definitions, a loop's
   * header, a block's statements, then its children. A definition nested in an expression is
   * listed at the expression's own position, and a loop header's declaration carries no list: its
   * landing point is the loop statement's definitions.
   */
  private static void collectPrintedOrder(Statement stat, List<DeclPos> out) {
    addDefinitionPositions(stat, stat.getVarDefinitions(), out);
    if (stat instanceof DoStatement loop && loop.getInitExprent() != null) {
      for (Exprent inner : loop.getInitExprent().getAllExprents(true, true)) {
        if (inner instanceof VarExprent var && isRealDefinition(var) && var.getLVT() != null) {
          out.add(new DeclPos(var, loop.getInitExprent(), null, stat, var.getLVT().getIndex()));
        }
      }
    }
    if (stat.getExprents() != null) {
      addDefinitionPositions(stat, stat.getExprents(), out);
    }
    for (Statement child : stat.getStats()) {
      collectPrintedOrder(child, out);
    }
  }

  private static void addDefinitionPositions(Statement owner, List<Exprent> exprents, List<DeclPos> out) {
    for (Exprent exprent : exprents) {
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof VarExprent var && isRealDefinition(var) && var.getLVT() != null) {
          out.add(new DeclPos(var, exprent, exprents, owner, var.getLVT().getIndex()));
        }
      }
    }
  }

  /**
   * True when the anchor's own scope is still open where the candidate gets its first value. If
   * it closed first, the slots it occupied were free when the candidate was declared, and a lower
   * slot proves nothing: javac handed one of them over instead of the candidate being written
   * earlier.
   */
  private static boolean anchorLiveAt(DeclPos anchor, DeclPos candidate) {
    if (anchor.var.getLVT() == null || candidate.var.getLVT() == null) {
      return false;
    }
    return anchor.var.getLVT().getEnd() > candidate.var.getLVT().getStart();
  }

  /** True when a declaration printed at this position lies past the end of a reused slot's scope. */
  private static boolean landsAfterDeadScope(DeclPos anchor, int deadEnd) {
    int offset = anchor.top == null ? -1 : printedOffset(anchor.top);
    if (offset < 0 && anchor.owner != null) {
      offset = RoundTrip.firstOffset(anchor.owner);
    }
    return offset >= 0 && offset >= deadEnd;
  }

  /**
   * True when the anchor's declaration is in scope where the definition is printed: it is an
   * ancestor's own declaration, or a preceding sibling's that prints in the same block — a plain
   * block or sequence prints inline, an if's head prints before its test. An arm's block is a
   * scope of its own, so a declaration there cannot land a variable used in the other arm.
   */
  private static boolean inScope(DeclPos anchor, Statement definitionOwner) {
    Statement anchorOwner = anchor.owner;
    Statement stat = definitionOwner;
    while (stat != null) {
      if (stat == anchorOwner) {
        return true;
      }
      Statement parent = stat.getParent();
      if (parent != null) {
        for (Statement sibling : parent.getStats()) {
          if (sibling == stat) {
            break;
          }
          if (sibling == anchorOwner && printsAtParentLevel(anchor)) {
            return true;
          }
        }
      }
      stat = parent;
    }
    return false;
  }

  /** True when the declaration prints in the block its owner's statement is written in. */
  private static boolean printsAtParentLevel(DeclPos anchor) {
    Statement owner = anchor.owner;
    if (owner == null) {
      return false;
    }
    if (anchor.list == null || anchor.list == owner.getVarDefinitions()) {
      return true;
    }
    if (owner.type != Statement.StatementType.BASIC_BLOCK && owner.type != Statement.StatementType.SEQUENCE) {
      return false;
    }
    Statement parent = owner.getParent();
    if (parent == null || parent.type == Statement.StatementType.SEQUENCE
        || parent.type == Statement.StatementType.ROOT) {
      return true;
    }
    return parent instanceof IfStatement ifStatement && ifStatement.getFirst() == owner;
  }

  /** One declaration in printed order. {@code list} is null for a loop header's own definition. */
  private static final class DeclPos {
    final VarExprent var;
    final Exprent top;
    final List<Exprent> list;
    final Statement owner;
    final int slot;

    DeclPos(VarExprent var, Exprent top, List<Exprent> list, Statement owner, int slot) {
      this.var = var;
      this.top = top;
      this.list = list;
      this.owner = owner;
      this.slot = slot;
    }
  }

  /**
   * The list the declarations printed just before this child live in: the exprents of the last
   * sibling that prints declarations of its own, else the sequence's own definitions.
   */
  private static List<Exprent> insertionList(Statement seq, Statement child) {
    List<Exprent> best = seq.getVarDefinitions();
    int bestSlot = -1;
    for (Exprent definition : best) {
      bestSlot = Math.max(bestSlot, targetSlot(definition));
    }
    for (Statement sibling : siblingsBefore(seq.getStats(), child)) {
      List<Exprent> candidate = declarationsList(sibling);
      if (candidate == null) {
        continue;
      }
      int slot = -1;
      for (Exprent definition : candidate) {
        slot = Math.max(slot, targetSlot(definition));
      }
      if (slot >= bestSlot && slot >= 0) {
        bestSlot = slot;
        best = candidate;
      }
    }
    return best;
  }

  /** The exprent list a statement's own declarations print from, or null. */
  private static List<Exprent> declarationsList(Statement stat) {
    Statement body = nestedBody(stat);
    if (body == null) {
      return stat.getExprents();
    }
    List<Exprent> inner = declarationsList(body);
    return inner != null && !inner.isEmpty() ? inner : body.getExprents();
  }

  /**
   * The highest target slot among the declarations this statement prints at its own level or in
   * the head of a switch, loop or if body, which print before the statement's block.
   */
  private static int printedDeclarationsUpTo(Statement stat) {
    int max = -1;
    for (Exprent definition : stat.getVarDefinitions()) {
      max = Math.max(max, targetSlot(definition));
    }
    if (stat.getExprents() != null) {
      for (Exprent definition : stat.getExprents()) {
        max = Math.max(max, targetSlot(definition));
      }
    }
    Statement body = nestedBody(stat);
    if (body != null) {
      max = Math.max(max, printedDeclarationsUpTo(body));
    }
    return max;
  }

  /** The siblings printed before this child, in print order. */
  private static List<Statement> siblingsBefore(List<Statement> children, Statement child) {
    List<Statement> before = new ArrayList<>();
    for (Statement sibling : children) {
      if (sibling == child) {
        break;
      }
      before.add(sibling);
    }
    return before;
  }

  /** True when every child prints as a plain run of statements, so the root reads like a sequence. */
  private static boolean onlyBasicBlocks(Statement stat) {
    if (stat.getStats().isEmpty()) {
      return false;
    }
    for (Statement child : stat.getStats()) {
      if (child.type != Statement.StatementType.BASIC_BLOCK) {
        return false;
      }
    }
    return true;
  }

  /** The block directly under a statement that prints as a nested block, or null. */
  private static Statement nestedBody(Statement child) {
    if (child instanceof DoStatement loop) {
      Statement body = loop.getFirst();
      return body != null && body.type == Statement.StatementType.SEQUENCE ? body : null;
    }
    if (child instanceof IfStatement ifStatement) {
      Statement body = ifStatement.getIfstat();
      return body != null && body.type == Statement.StatementType.SEQUENCE ? body : null;
    }
    if (child instanceof SwitchStatement switchStatement) {
      // The head block prints just before `switch (…)`, so its declarations can move out to the
      // sequence and keep their place relative to the switch.
      return switchStatement.getFirst();
    }
    if (child instanceof CatchStatement catchStatement) {
      // A try body's locals can be declared above the whole try: the catch parameter, allocated
      // after the body, then sits above their slots instead of reusing them. The body may be a
      // single block, so any statement type is taken here.
      return catchStatement.getFirst();
    }
    return null;
  }

  /** The slots the target gives a catch statement's exception parameters. */
  private static List<Integer> catchParameterSlots(CatchStatement catchStatement) {
    List<Integer> slots = new ArrayList<>();
    for (Exprent exprent : catchStatement.getStatExprents()) {
      if (exprent == null) {
        continue;
      }
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof VarExprent var && var.getLVT() != null && var.getLVT().getIndex() >= 0) {
          slots.add(var.getLVT().getIndex());
        }
      }
    }
    return slots;
  }

  /** True when a handler slot lies above the local's whole slot range, so it was still reserved. */
  private static boolean belowHandlerSlot(List<Integer> handlerSlots, VarExprent var) {
    VarType type = var.getVarType();
    int width = type != null && (type.type == CodeType.LONG || type.type == CodeType.DOUBLE) ? 2 : 1;
    for (int slot : handlerSlots) {
      if (slot >= var.getLVT().getIndex() + width) {
        return true;
      }
    }
    return false;
  }

  /** Inserts the declaration before the first definition the target gives a higher slot. */
  private static void insertByTargetSlot(List<Exprent> definitions, Exprent declaration) {
    int slot = targetSlot(declaration);
    int at = definitions.size();
    for (int i = 0; i < definitions.size(); i++) {
      int other = targetSlot(definitions.get(i));
      if (other >= 0 && slot >= 0 && other > slot) {
        at = i;
        break;
      }
    }
    definitions.add(at, declaration);
  }

  /** The slot the target's local table gives this definition, or -1. */
  private static int targetSlot(Exprent exprent) {
    VarExprent var = definedVar(exprent);
    return var == null || var.getLVT() == null ? -1 : var.getLVT().getIndex();
  }

  // *****************************************************************************
  // cross-statement hoist
  // *****************************************************************************

  private static void hoistAcrossStatements(Statement stat, VarProcessor varproc, NameTable names, String method) {
    if (stat.type == Statement.StatementType.SEQUENCE
        || (stat.type == Statement.StatementType.ROOT && onlyBasicBlocks(stat))) {
      hoistInSequence(stat, varproc, names, method);
    }
    for (Statement child : stat.getStats()) {
      hoistAcrossStatements(child, varproc, names, method);
    }
  }

  /**
   * The declarations printed directly in one sequence, in printed order: a statement's own
   * variable definitions, a basic block's exprents, and the pre-if exprents of an if header.
   * Declarations inside an arm, a loop body or a switch are in a nested block and are not part of
   * this sequence's declaration order.
   */
  private static List<Position> declarationOrder(Statement seq, VarProcessor varproc) {
    List<Position> order = new ArrayList<>();
    addPositions(order, seq, seq.getVarDefinitions(), varproc);
    for (Statement child : seq.getStats()) {
      if (child.type == Statement.StatementType.GENERAL || child.type == Statement.StatementType.DUMMY_EXIT) {
        continue;
      }
      addPositions(order, child, child.getVarDefinitions(), varproc);
      if (child.type == Statement.StatementType.BASIC_BLOCK) {
        List<Exprent> exprents = child.getExprents();
        if (exprents != null) {
          addPositions(order, child, exprents, varproc);
        }
      }
      else if (child instanceof IfStatement ifStatement) {
        Statement head = ifStatement.getFirst();
        if (head != null && head.type == Statement.StatementType.BASIC_BLOCK) {
          addPositions(order, ifStatement, head.getVarDefinitions(), varproc);
          List<Exprent> exprents = head.getExprents();
          if (exprents != null) {
            addPositions(order, ifStatement, exprents, varproc);
          }
        }
      }
    }
    return order;
  }

  private static void addPositions(List<Position> order, Statement owner, List<Exprent> exprents, VarProcessor varproc) {
    for (int i = 0; i < exprents.size(); i++) {
      Exprent exprent = exprents.get(i);
      if (exprent != null) {
        order.add(new Position(exprent, exprents, declarationSlot(exprent, varproc), owner, -1));
      }
    }
  }

  private static void hoistInSequence(Statement seq, VarProcessor varproc, NameTable names, String method) {
    hoistNestedOut(seq, varproc, names, method);
    if (seq.isLabeled()) {
      // A labeled sequence prints its varDefinitions before `label: {`, so a declaration moved
      // into them escapes the block and could capture a name used after it.
      return;
    }
    List<Position> order = declarationOrder(seq, varproc);
    List<Position> hoisted = new ArrayList<>();
    Position delegation = findDelegation(order);
    boolean delegationHidden = delegation == null && hasConstructorDelegation(seq);

    for (int i = 0; i < order.size(); i++) {
      Position position = order.get(i);
      VarExprent var = definedVar(position.exprent);
      if (var == null || !isRealDefinition(var)) {
        continue;
      }
      int slot = position.slot;
      if (slot < 0) {
        continue;
      }
      // javac reserves a local's slot at its declaration, so a slot freed by an earlier local
      // (a differently named one: javac writes a row per scope range, and the same name is one
      // variable) proves this declaration came after that local's scope closed. The landing
      // point must lie past it; a declaration printed inside the dead scope cannot be ours.
      int deadEnd = slotReuseEnd(var);

      Position earliest = null;
      for (int j = 0; j < i; j++) {
        if (order.get(j).slot > slot && afterDeadScope(order.get(j), deadEnd)) {
          earliest = order.get(j);
          break;
        }
      }
      if (earliest == null || earliest.list == position.list) {
        // Nothing earlier to precede, or the plain within-list pass owns this move.
        continue;
      }
      if (!names.uniqueName(var) && !names.sameSlotName(var)) {
        debug(method, var, "rejected: another local prints as " + var.getName());
        continue;
      }
      if (mentionsField(seq, var.getName())) {
        debug(method, var, "rejected: the sequence names a field " + var.getName());
        continue;
      }
      if (delegationHidden) {
        debug(method, var, "rejected: constructor delegation");
        continue;
      }
      Da da = new Da(var);
      if (!da.check(seq)) {
        debug(method, var, "rejected: not definitely assigned at a use");
        continue;
      }

      debug(method, var, "hoisted from slot-" + slot + " past slot-" + earliest.slot
        + (deadEnd >= 0 ? " after dead scope " + deadEnd : ""));
      if (position.exprent == var) {
        hoisted.add(new Position(position.exprent, position.list, slot, position.owner, deadEnd));
      } else {
        // An initialized declaration: the table proves the variable was declared before an
        // earlier one, so hoist the declaration bare and leave the store as an assignment. Only
        // the declaration order moves; the value is still computed where it was printed.
        VarExprent bare = (VarExprent) var.copy();
        var.setDefinition(false);
        hoisted.add(new Position(bare, position.list, slot, position.owner, deadEnd));
      }
    }

    if (hoisted.isEmpty()) {
      return;
    }

    for (Position position : hoisted) {
      removeIdentity(position.list, position.exprent);
    }
    // Higher slots first, so a declaration that is itself being hoisted is already back in the
    // printed order when a lower one looks for the declaration it must precede.
    hoisted.sort((a, b) -> Integer.compare(b.slot, a.slot));

    if (delegation != null) {
      // `this(...)`/`super(...)` must stay the constructor's first statement; the source
      // declared the hoisted locals right after it. Each one is inserted at the same index,
      // which turns the descending walk back into slot order.
      List<Exprent> body = delegation.list;
      int at = indexOfIdentity(body, delegation.exprent) + 1;
      if (at <= 0) {
        at = body.size(); // unreachable: never place a declaration before the delegation
      }
      for (Position position : hoisted) {
        body.add(at, position.exprent);
      }
      return;
    }

    // The source declared each variable just above the first declaration whose slot is higher:
    // the table's slot order is the source order. Placing a declaration at the sequence's top
    // would print it above every earlier declaration and diverge from the target.
    for (Position position : hoisted) {
      Position anchor = null;
      for (Position candidate : declarationOrder(seq, varproc)) {
        if (candidate.slot > position.slot && afterDeadScope(candidate, position.deadEnd)) {
          anchor = candidate;
          break;
        }
      }
      if (anchor == null) {
        // Nothing higher prints after the dead scope any more; the declaration is put back
        // where it printed before. The slot table offers no landing point that keeps its slot.
        position.list.add(position.exprent);
        continue;
      }
      int at = indexOfIdentity(anchor.list, anchor.exprent);
      anchor.list.add(at < 0 ? anchor.list.size() : at, position.exprent);
    }
  }

  private static int indexOfIdentity(List<Exprent> list, Exprent exprent) {
    for (int i = 0; i < list.size(); i++) {
      if (list.get(i) == exprent) {
        return i;
      }
    }
    return -1;
  }

  /** The constructor delegation among the sequence's own statements, or null. */
  private static Position findDelegation(List<Position> order) {
    for (Position position : order) {
      if (position.exprent instanceof InvocationExprent invocation
        && invocation.getFunctype() == InvocationExprent.Type.INIT
        && !(invocation.getInstance() instanceof NewExprent)) {
        return position;
      }
    }
    return null;
  }

  private static void removeIdentity(List<Exprent> list, Exprent exprent) {
    for (int i = 0; i < list.size(); i++) {
      if (list.get(i) == exprent) {
        list.remove(i);
        return;
      }
    }
  }

  /** A {@code this(...)}/super{@code (...)} delegation must stay the constructor's first statement. */
  private static boolean hasConstructorDelegation(Statement stat) {
    for (Exprent exprent : stat.getVarDefinitions()) {
      if (hasDelegation(exprent)) {
        return true;
      }
    }
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (hasDelegation(exprent)) {
          return true;
        }
      }
    }
    for (Exprent exprent : stat.getStatExprents()) {
      if (exprent != null && hasDelegation(exprent)) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (hasConstructorDelegation(child)) {
        return true;
      }
    }
    return false;
  }

  private static boolean hasDelegation(Exprent exprent) {
    if (exprent == null) {
      return false;
    }
    for (Exprent inner : exprent.getAllExprents(true, true)) {
      if (inner instanceof InvocationExprent invocation
        && invocation.getFunctype() == InvocationExprent.Type.INIT
        && !(invocation.getInstance() instanceof NewExprent)) {
        return true;
      }
    }
    return false;
  }

  private static boolean mentionsField(Statement stat, String name) {
    for (Exprent exprent : stat.getVarDefinitions()) {
      if (mentionsField(exprent, name)) {
        return true;
      }
    }
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (mentionsField(exprent, name)) {
          return true;
        }
      }
    }
    for (Exprent exprent : stat.getStatExprents()) {
      if (exprent != null && mentionsField(exprent, name)) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (mentionsField(child, name)) {
        return true;
      }
    }
    return false;
  }

  private static boolean mentionsField(Exprent exprent, String name) {
    if (exprent == null) {
      return false;
    }
    for (Exprent inner : exprent.getAllExprents(true, true)) {
      if (inner instanceof FieldExprent field && field.getName().equals(name)) {
        return true;
      }
    }
    return false;
  }

  // *****************************************************************************
  // definite assignment
  // *****************************************************************************

  /**
   * Whether one variable is definitely assigned at every use after the declaration has been
   * moved to the start of the sequence. Conservative where the printed shape is hard to model:
   * a loop may run zero times, a handler may see a partially assigned try body, and a switch
   * arm may be entered after another arm's fall-through.
   */
  private static final class Da {
    private final VarVersionPair target;
    private boolean violated;

    Da(VarExprent target) {
      this.target = target.getVarVersionPair();
    }

    boolean check(Statement seq) {
      stat(seq, false);
      return !violated;
    }

    private boolean stat(Statement stat, boolean assigned) {
      for (Exprent exprent : stat.getVarDefinitions()) {
        assigned = exprent(exprent, assigned);
      }

      List<Exprent> exprents = stat.getExprents();
      if (exprents != null) {
        for (Exprent exprent : exprents) {
          assigned = exprent(exprent, assigned);
        }
        return assigned;
      }

      switch (stat.type) {
        case ROOT: {
          Statement first = stat.getFirst();
          return first == null ? assigned : stat(first, assigned);
        }
        case SEQUENCE: {
          for (Statement child : stat.getStats()) {
            assigned = stat(child, assigned);
          }
          return assigned;
        }
        case IF: {
          IfStatement ifStatement = (IfStatement)stat;
          Statement head = ifStatement.getFirst();
          if (head != null) {
            assigned = stat(head, assigned);
          }
          assigned = exprent(ifStatement.getHeadexprent(), assigned);
          boolean thenState = ifStatement.getIfstat() == null ? assigned : stat(ifStatement.getIfstat(), assigned);
          boolean elseState = ifStatement.getElsestat() == null ? assigned : stat(ifStatement.getElsestat(), assigned);
          return thenState && elseState;
        }
        case DO: {
          DoStatement loop = (DoStatement)stat;
          boolean entry = assigned;
          Exprent init = loop.getInitExprent();
          if (init != null) {
            entry = exprent(init, entry);
          }
          boolean bodyEntry = entry;
          boolean conditionAfterBody = false;
          switch (loop.getLooptype()) {
            case WHILE:
              // A while loop evaluates its condition before every iteration, so what the
              // condition assigns on the way to true is definitely assigned inside the body.
              // Later iterations enter the condition with at least this state, and the analysis
              // is monotone.
              bodyEntry = trueState(loop.getConditionExprent(), entry);
              break;
            case DO_WHILE:
              // The condition runs after the body; it is checked against the body's exit below.
              conditionAfterBody = true;
              break;
            case FOR:
              // The init and the condition both run before the first body statement.
              bodyEntry = trueState(loop.getConditionExprent(), entry);
              exprent(loop.getIncExprent(), entry);
              break;
            case FOR_EACH:
              exprent(loop.getIncExprent(), entry);
              break;
            default:
              break;
          }
          Statement body = loop.getFirst();
          boolean afterBody = body == null ? bodyEntry : stat(body, bodyEntry);
          if (conditionAfterBody) {
            // A `continue` skips the rest of the body, so the linear walk may credit it with an
            // assignment the jumping path never makes; the body's entry state is the safe floor.
            exprent(loop.getConditionExprent(), hasContinue(body) ? bodyEntry : afterBody);
            // A do-while runs its body at least once, and with no jump out of the middle every
            // exit passes the body's end; the code after the loop sees that state.
            return hasBreakOrContinue(body) ? bodyEntry : afterBody;
          }
          // The loop may run zero times, and a break may leave it from any iteration.
          return entry;
        }
        case SWITCH: {
          SwitchStatement switchStatement = (SwitchStatement)stat;
          Statement head = switchStatement.getFirst();
          if (head != null) {
            assigned = stat(head, assigned);
          }
          for (Exprent exprent : switchStatement.getStatExprents()) {
            if (exprent != null) {
              assigned = exprent(exprent, assigned);
            }
          }
          boolean result = true;
          for (Statement arm : switchStatement.getCaseStatements()) {
            boolean armState = stat(arm, assigned);
            result = result && armState;
          }
          if (switchStatement.getDefaultEdge() == null) {
            result = result && assigned;
          }
          return result;
        }
        case SYNCHRONIZED: {
          SynchronizedStatement sync = (SynchronizedStatement)stat;
          Statement head = sync.getFirst();
          if (head != null) {
            assigned = stat(head, assigned);
          }
          for (Exprent exprent : sync.getStatExprents()) {
            if (exprent != null) {
              assigned = exprent(exprent, assigned);
            }
          }
          Statement body = sync.getBody();
          if (body != null) {
            stat(body, assigned);
          }
          return assigned;
        }
        case TRY_CATCH: {
          CatchStatement catchStatement = (CatchStatement)stat;
          for (Exprent exprent : catchStatement.getStatExprents()) {
            if (exprent != null) {
              assigned = exprent(exprent, assigned);
            }
          }
          Statement body = catchStatement.getFirst();
          boolean afterBody = body == null ? assigned : stat(body, assigned);
          // Control reaches the code after the statement either by leaving the body normally or
          // by leaving a handler normally; a handler that always returns or throws never gets
          // there, so it must not undo what the body established.
          boolean result = afterBody;
          for (int i = 1; i < catchStatement.getStats().size(); i++) {
            Statement handler = catchStatement.getStats().get(i);
            // A handler may run after any prefix of the try body.
            boolean handlerState = stat(handler, assigned);
            if (!neverCompletesNormally(handler)) {
              result = result && handlerState;
            }
          }
          return result;
        }
        case CATCH_ALL: {
          CatchAllStatement catchAll = (CatchAllStatement)stat;
          for (Exprent exprent : catchAll.getStatExprents()) {
            if (exprent != null) {
              assigned = exprent(exprent, assigned);
            }
          }
          Statement body = catchAll.getFirst();
          if (body != null) {
            stat(body, assigned);
          }
          Statement handler = catchAll.getHandler();
          if (handler != null) {
            stat(handler, assigned);
          }
          return assigned;
        }
        default: {
          for (Statement child : stat.getStats()) {
            assigned = stat(child, assigned);
          }
          return assigned;
        }
      }
    }

    private boolean exprent(Exprent exprent, boolean assigned) {
      if (exprent == null) {
        return assigned;
      }

      if (exprent instanceof AssignmentExprent assignment) {
        Exprent left = assignment.getLeft();
        // The target location is evaluated before the value: an array's base and index first.
        assigned = location(left, assigned);
        if (assignment.getCondType() != null && isTarget(left) && !assigned) {
          // A compound assignment reads the old value.
          violated = true;
        }
        assigned = exprent(assignment.getRight(), assigned);
        if (isTarget(left)) {
          assigned = true;
        }
        return assigned;
      }

      if (exprent instanceof VarExprent var) {
        if (!var.isStack() && !var.isDefinition() && isTarget(var) && !assigned) {
          violated = true;
        }
        return assigned;
      }

      if (exprent instanceof FunctionExprent function && function.getFuncType().isPPMM()) {
        for (Exprent operand : function.getLstOperands()) {
          assigned = exprent(operand, assigned);
        }
        if (!function.getLstOperands().isEmpty() && isTarget(function.getLstOperands().get(0))) {
          assigned = true;
        }
        return assigned;
      }

      if (exprent instanceof FunctionExprent function
        && (function.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND
        || function.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_OR
        || function.getFuncType() == FunctionExprent.FunctionType.TERNARY)) {
        List<Exprent> operands = function.getLstOperands();
        if (operands.isEmpty()) {
          return assigned;
        }
        // The first operand always runs; the others may be short-circuited away, so their
        // assignments cannot be credited to the state after the expression.
        boolean afterFirst = exprent(operands.get(0), assigned);
        for (int i = 1; i < operands.size(); i++) {
          exprent(operands.get(i), afterFirst);
        }
        return afterFirst;
      }

      for (Exprent child : exprent.getAllExprents(false)) {
        assigned = exprent(child, assigned);
      }
      return assigned;
    }

    /**
     * The state guaranteed when this expression evaluates to true: the operands a short-circuit
     * guard forced to run are evaluated here, so what they assign holds on the branch that takes
     * the condition. Uses are still checked against the state on entry.
     */
    private boolean trueState(Exprent expression, boolean assigned) {
      if (expression instanceof FunctionExprent function) {
        List<Exprent> operands = function.getLstOperands();
        if (function.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND) {
          boolean eval = assigned;
          boolean truth = assigned;
          for (Exprent operand : operands) {
            truth = trueState(operand, eval);
            eval = exprent(operand, eval);
          }
          return truth;
        }
        if (function.getFuncType() == FunctionExprent.FunctionType.BOOLEAN_OR) {
          if (operands.isEmpty()) {
            return assigned;
          }
          // If the first operand is true the rest never runs, so only its own assignments hold.
          boolean truth = trueState(operands.get(0), assigned);
          boolean eval = exprent(operands.get(0), assigned);
          for (int i = 1; i < operands.size(); i++) {
            exprent(operands.get(i), eval);
          }
          return truth;
        }
        if (function.getFuncType() == FunctionExprent.FunctionType.TERNARY) {
          // Only the condition is evaluated before the picked arm, whichever it is.
          return exprent(expression, assigned);
        }
      }
      return exprent(expression, assigned);
    }

    /** The parts of a store target, in evaluation order; a plain variable reads nothing. */
    private boolean location(Exprent exprent, boolean assigned) {
      if (exprent instanceof VarExprent) {
        return assigned;
      }
      return exprent(exprent, assigned);
    }

    private boolean isTarget(Exprent exprent) {
      return exprent instanceof VarExprent var && !var.isStack() && var.getVarVersionPair().equals(target);
    }

    /** True when an explicit {@code continue} leaves any statement of this subtree. */
    private static boolean hasContinue(Statement stat) {
      if (stat == null) {
        return false;
      }
      if (hasExplicit(stat, StatEdge.TYPE_CONTINUE)) {
        return true;
      }
      for (Statement child : stat.getStats()) {
        if (hasContinue(child)) {
          return true;
        }
      }
      return false;
    }

    /**
     * True when control never falls out of the bottom of this statement: every path ends in a
     * {@code return} or a {@code throw}. A break or continue leaves through an edge this walk
     * does not follow, so it counts as completing normally rather than as an exit.
     */
    private static boolean neverCompletesNormally(Statement stat) {
      if (stat == null || hasBreakOrContinue(stat)) {
        return false;
      }
      List<Exprent> exprents = stat.getExprents();
      if (exprents != null) {
        for (int i = exprents.size() - 1; i >= 0; i--) {
          Exprent exprent = exprents.get(i);
          if (exprent != null) {
            return exprent instanceof ExitExprent exit
              && (exit.getExitType() == ExitExprent.Type.RETURN || exit.getExitType() == ExitExprent.Type.THROW);
          }
        }
        return false;
      }
      switch (stat.type) {
        case SEQUENCE: {
          for (Statement child : stat.getStats()) {
            if (neverCompletesNormally(child)) {
              return true;
            }
          }
          return false;
        }
        case IF: {
          IfStatement ifStatement = (IfStatement)stat;
          return ifStatement.getIfstat() != null && ifStatement.getElsestat() != null
            && neverCompletesNormally(ifStatement.getIfstat())
            && neverCompletesNormally(ifStatement.getElsestat());
        }
        case SYNCHRONIZED: {
          Statement body = ((SynchronizedStatement)stat).getBody();
          return body != null && neverCompletesNormally(body);
        }
        default:
          return false;
      }
    }

    private static boolean hasBreakOrContinue(Statement stat) {
      if (hasExplicit(stat, StatEdge.TYPE_BREAK) || hasExplicit(stat, StatEdge.TYPE_CONTINUE)) {
        return true;
      }
      for (Statement child : stat.getStats()) {
        if (hasBreakOrContinue(child)) {
          return true;
        }
      }
      return false;
    }

    /**
     * True when the source wrote a break or continue here. A loop's implicit back edge is not a
     * jump the source made, and a jump to the dummy exit block is a return, not a fall-through
     * into the code after this statement.
     */
    private static boolean hasExplicit(Statement stat, int type) {
      for (StatEdge edge : stat.getSuccessorEdges(type)) {
        if (edge.explicit && !(edge.getDestination() instanceof DummyExitStatement)) {
          return true;
        }
      }
      return false;
    }
  }

  // *****************************************************************************
  // names
  // *****************************************************************************

  /**
   * Prints one declaration for a variable the target's table splits into several alive ranges:
   * the other ranges' own declarations become plain assignments, and a bare declaration that is
   * only the same variable's next row is dropped. The kept declaration is the one hoisted above.
   */
  private static void absorbSplitRanges(Statement stat, VarExprent kept) {
    absorbSplitRanges(stat.getVarDefinitions(), kept);
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      absorbSplitRanges(exprents, kept);
    }
    for (Statement child : stat.getStats()) {
      absorbSplitRanges(child, kept);
    }
  }

  private static void absorbSplitRanges(List<Exprent> exprents, VarExprent kept) {
    for (int i = exprents.size() - 1; i >= 0; i--) {
      Exprent exprent = exprents.get(i);
      if (exprent instanceof VarExprent var && var != kept && var.isDefinition() && sameRange(var, kept)) {
        // A bare declaration of the same variable's next range: the hoisted one announces it.
        exprents.remove(i);
        continue;
      }
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof VarExprent var && var != kept && var.isDefinition() && sameRange(var, kept)) {
          var.setDefinition(false);
        }
      }
    }
  }

  /** Whether two printed variables are one source variable's table ranges: same slot and name. */
  private static boolean sameRange(VarExprent a, VarExprent b) {
    return a.getLVT() != null && b.getLVT() != null && a.getLVT().getIndex() >= 0
      && a.getLVT().getIndex() == b.getLVT().getIndex()
      && a.getName().equals(b.getName());
  }

  /** Every printed local name in the method, to detect a hoist that would capture another one. */
  private static final class NameTable {
    private final Map<String, Set<VarVersionPair>> byName = new HashMap<>();
    private final Map<String, Set<Integer>> slotsByName = new HashMap<>();

    static NameTable build(Statement root) {
      NameTable table = new NameTable();
      table.collect(root);
      return table;
    }

    private void collect(Statement stat) {
      addAll(stat.getVarDefinitions());
      List<Exprent> exprents = stat.getExprents();
      if (exprents != null) {
        addAll(exprents);
      }
      addAll(stat.getStatExprents());
      for (Statement child : stat.getStats()) {
        collect(child);
      }
    }

    private void addAll(List<Exprent> exprents) {
      for (Exprent exprent : exprents) {
        if (exprent == null) {
          continue;
        }
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          if (inner instanceof VarExprent var && !var.isStack()) {
            byName.computeIfAbsent(var.getName(), name -> new HashSet<>()).add(var.getVarVersionPair());
            slotsByName.computeIfAbsent(var.getName(), name -> new HashSet<>())
              .add(var.getLVT() == null ? -1 : var.getLVT().getIndex());
          }
        }
      }
    }

    boolean uniqueName(VarExprent var) {
      Set<VarVersionPair> pairs = byName.get(var.getName());
      return pairs != null && pairs.size() == 1 && pairs.contains(var.getVarVersionPair());
    }

    /**
     * True when every printed variable of this name holds the same slot: the target's table
     * writes one row per alive range, so a discontinuous scope is one source variable, not two.
     */
    boolean sameSlotName(VarExprent var) {
      if (var.getLVT() == null || var.getLVT().getIndex() < 0) {
        return false;
      }
      Set<Integer> slots = slotsByName.get(var.getName());
      return slots != null && slots.size() == 1 && slots.contains(var.getLVT().getIndex());
    }
  }

  // *****************************************************************************
  // within-list pass
  // *****************************************************************************

  private static void reorderWithinList(Statement stat, VarProcessor varproc) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (int i = 1; i < exprents.size(); i++) {
        Exprent exprent = exprents.get(i);
        int slot = bareDeclarationSlot(exprent, varproc);
        boolean initialized = false;
        if (slot < 0) {
          // An initialized declaration whose slot precedes an earlier declaration's was written
          // before it in the source: print the declaration alone in slot order and keep the
          // store where it was. Only the declaration moves, so no evaluation order changes.
          VarExprent var = definedVar(exprent);
          if (var == null || !isRealDefinition(var)) {
            continue;
          }
          slot = slotOf(var, varproc);
          if (slot < 0) {
            continue;
          }
          initialized = true;
        }
        int j = i;
        while (j > 0) {
          Exprent previous = exprents.get(j - 1);
          int previousSlot = declarationSlot(previous, varproc);
          if (previousSlot < 0 || previousSlot <= slot) {
            break;
          }
          if (initialized) {
            j--;
            continue;
          }
          exprents.set(j, previous);
          exprents.set(j - 1, exprent);
          j--;
        }
        if (j < i && initialized) {
          VarExprent var = definedVar(exprent);
          VarExprent bare = (VarExprent) var.copy();
          var.setDefinition(false);
          exprents.add(j, bare);
        }
      }
    }
    if (!stat.getVarDefinitions().isEmpty()) {
      reconcileDefinitions(stat, exprents, varproc);
    }
    for (Statement child : stat.getStats()) {
      reorderWithinList(child, varproc);
    }
  }

  /**
   * A bare declaration hoisted to the sequence's definitions prints before every exprent, but the
   * source order is the target's slot order: one whose slot follows an initialized declaration's
   * prints after it. The declaration itself is unchanged, so nothing it declares changes value.
   */
  private static void reconcileDefinitionsInto(List<Exprent> definitions, List<Exprent> exprents,
                                               VarProcessor varproc) {
    for (int d = definitions.size() - 1; d >= 0; d--) {
      Exprent declaration = definitions.get(d);
      int slot = declarationSlot(declaration, varproc);
      if (slot < 0 || readsLocalBefore(declaration, exprents)) {
        continue;
      }
      int target = -1;
      for (int i = 0; i < exprents.size(); i++) {
        int earlier = declarationSlot(exprents.get(i), varproc);
        if (earlier >= 0 && earlier < slot) {
          target = i;
        }
      }
      if (target >= 0) {
        definitions.remove(d);
        exprents.add(target + 1, declaration);
      }
    }
  }

  /** The exprents of the sequence's first child statement, when that child is a plain block. */
  private static List<Exprent> firstChildExprents(Statement stat) {
    if (stat.getExprents() != null || stat.getStats().isEmpty()) {
      return null;
    }
    Statement first = stat.getStats().get(0);
    return first instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement
      ? first.getExprents() : null;
  }

  /** True when any exprent of the list reads the local this declaration defines. */
  private static boolean readsLocalBefore(Exprent declaration, List<Exprent> exprents) {
    VarExprent declared = definedVar(declaration);
    if (declared == null) {
      return true;
    }
    for (Exprent exprent : exprents) {
      for (Exprent part : exprent.getAllExprents(true, true)) {
        if (part instanceof VarExprent var && !var.isDefinition()
          && var.getIndex() == declared.getIndex()) {
          return true;
        }
      }
    }
    return false;
  }

  private static void reconcileDefinitions(Statement stat, List<Exprent> exprents, VarProcessor varproc) {
    // A sequence whose definitions print before its child statements can hide a declaration in
    // the first child block; the source order is still the target's slot order.
    List<Exprent> childExprents = firstChildExprents(stat);
    if (childExprents != null && childExprents != exprents) {
      reconcileDefinitionsInto(stat.getVarDefinitions(), childExprents, varproc);
    }
    if (exprents != null) {
      reconcileDefinitionsInto(stat.getVarDefinitions(), exprents, varproc);
    }
  }

  // *****************************************************************************
  // slots
  // *****************************************************************************

  private static final class Position {
    final Exprent exprent;
    final List<Exprent> list;
    final int slot;
    /** The statement holding the list, for the offset the declaration prints at. */
    final Statement owner;
    /** The end offset of the scope this variable's slot came from, or -1. */
    final int deadEnd;

    Position(Exprent exprent, List<Exprent> list, int slot, Statement owner, int deadEnd) {
      this.exprent = exprent;
      this.list = list;
      this.slot = slot;
      this.owner = owner;
      this.deadEnd = deadEnd;
    }
  }

  /** The slot of a declaration statement that only names a variable, or -1. */
  private static int bareDeclarationSlot(Exprent exprent, VarProcessor varproc) {
    if (exprent instanceof VarExprent var && isRealDefinition(var)) {
      return slotOf(var, varproc);
    }
    return -1;
  }

  /** The slot of a bare or initialized declaration statement, or -1 for any other exprent. */
  private static int declarationSlot(Exprent exprent, VarProcessor varproc) {
    if (exprent instanceof VarExprent var && isRealDefinition(var)) {
      return slotOf(var, varproc);
    }
    if (exprent instanceof AssignmentExprent assignment
      && assignment.getLeft() instanceof VarExprent var && isRealDefinition(var)) {
      return slotOf(var, varproc);
    }
    return -1;
  }

  private static boolean isRealDefinition(VarExprent var) {
    return var.isDefinition() && !var.isStack();
  }

  /** The variable a declaration exprent defines: a bare declaration or an initialized one. */
  private static VarExprent definedVar(Exprent exprent) {
    if (exprent instanceof VarExprent var) {
      return var;
    }
    if (exprent instanceof AssignmentExprent assignment
      && assignment.getLeft() instanceof VarExprent var) {
      return var;
    }
    return null;
  }

  /**
   * The end offset of the scope whose freed slot this variable took, or -1 when its slot was
   * freshly allocated. javac reserves a local's slot at its declaration, so a different local
   * owning the same slot earlier proves the declaration came after that scope closed. A row
   * carrying the same name is one source variable whose scope is discontinuous (javac writes a
   * row per range), not a second owner of the slot.
   */
  private static int slotReuseEnd(VarExprent var) {
    LocalVariable lvt = var.getLVT();
    if (lvt == null) {
      return -1;
    }
    MethodWrapper wrapper = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (wrapper == null || wrapper.methodStruct == null) {
      return -1;
    }
    StructLocalVariableTableAttribute table = wrapper.methodStruct.getAttribute(StructGeneralAttribute.ATTRIBUTE_LOCAL_VARIABLE_TABLE);
    if (table == null) {
      return -1;
    }
    int end = -1;
    for (LocalVariable other : table.getVariables().toList()) {
      if (other.getIndex() == lvt.getIndex()
        && !java.util.Objects.equals(other.getName(), lvt.getName())
        && other.getEnd() <= lvt.getStart()) {
        end = Math.max(end, other.getEnd());
      }
    }
    return end;
  }

  /** Whether a declaration printed at this position lies past the dead scope's end. */
  private static boolean afterDeadScope(Position candidate, int deadEnd) {
    if (deadEnd < 0) {
      return true;
    }
    // The target's end offset is exclusive: an instruction at exactly that offset is past the
    // scope. An initialized declaration prints at its own first instruction; a bare one has none,
    // so the statement holding it stands in.
    int offset = printedOffset(candidate.exprent);
    if (offset < 0 && candidate.owner != null) {
      offset = RoundTrip.firstOffset(candidate.owner);
    }
    return offset >= 0 && offset >= deadEnd;
  }

  private static int printedOffset(Exprent exprent) {
    java.util.BitSet offsets = new java.util.BitSet();
    exprent.getBytecodeRange(offsets);
    return offsets.nextSetBit(0);
  }

  private static int slotOf(VarExprent var, VarProcessor varproc) {
    LocalVariable lvt = var.getLVT();
    if (lvt != null) {
      return lvt.getVersion().var;
    }
    if (varproc != null) {
      Integer original = varproc.getVarOriginalIndex(var.getIndex());
      if (original != null) {
        return original;
      }
    }
    return -1;
  }

  private static void debug(String method, VarExprent var, String message) {
    if (System.getenv("NEUROFLOWER_DECLORDER") != null) {
      System.err.println("declorder " + method + " " + var.getName() + ": " + message);
    }
  }
}

// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SynchronizedStatement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

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
        for (Exprent exprent : candidates) {
          VarExprent var = definedVar(exprent);
          if (var == null || !isRealDefinition(var) || var.getLVT() == null) {
            continue;
          }
          // The target gave this local a slot below one that prints before the block: the source
          // declared it further up the sequence, bare, and assigned it here.
          if (var.getLVT().getIndex() < 0 || var.getLVT().getIndex() >= maxSlot) {
            continue;
          }
          if (!names.uniqueName(var) || mentionsField(seq, var.getName())) {
            debug(method, var, "rejected: nested declaration would capture a name");
            continue;
          }
          debug(method, var, "hoisted out of a nested block: slot " + var.getLVT().getIndex()
            + " below " + maxSlot);
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
    return null;
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
    addPositions(order, seq.getVarDefinitions(), varproc);
    for (Statement child : seq.getStats()) {
      if (child.type == Statement.StatementType.GENERAL || child.type == Statement.StatementType.DUMMY_EXIT) {
        continue;
      }
      addPositions(order, child.getVarDefinitions(), varproc);
      if (child.type == Statement.StatementType.BASIC_BLOCK) {
        List<Exprent> exprents = child.getExprents();
        if (exprents != null) {
          addPositions(order, exprents, varproc);
        }
      }
      else if (child instanceof IfStatement ifStatement) {
        Statement head = ifStatement.getFirst();
        if (head != null && head.type == Statement.StatementType.BASIC_BLOCK) {
          addPositions(order, head.getVarDefinitions(), varproc);
          List<Exprent> exprents = head.getExprents();
          if (exprents != null) {
            addPositions(order, exprents, varproc);
          }
        }
      }
    }
    return order;
  }

  private static void addPositions(List<Position> order, List<Exprent> exprents, VarProcessor varproc) {
    for (int i = 0; i < exprents.size(); i++) {
      Exprent exprent = exprents.get(i);
      if (exprent != null) {
        order.add(new Position(exprent, exprents, declarationSlot(exprent, varproc)));
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

      Position earliest = null;
      for (int j = 0; j < i; j++) {
        if (order.get(j).slot > slot) {
          earliest = order.get(j);
          break;
        }
      }
      if (earliest == null || earliest.list == position.list) {
        // Nothing earlier to precede, or the plain within-list pass owns this move.
        continue;
      }
      if (!names.uniqueName(var)) {
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

      debug(method, var, "hoisted from slot-" + slot + " past slot-" + earliest.slot);
      if (position.exprent == var) {
        hoisted.add(position);
      } else {
        // An initialized declaration: the table proves the variable was declared before an
        // earlier one, so hoist the declaration bare and leave the store as an assignment. Only
        // the declaration order moves; the value is still computed where it was printed.
        VarExprent bare = (VarExprent) var.copy();
        var.setDefinition(false);
        hoisted.add(new Position(bare, position.list, slot));
      }
    }

    if (hoisted.isEmpty()) {
      return;
    }

    for (Position position : hoisted) {
      removeIdentity(position.list, position.exprent);
    }
    hoisted.sort((a, b) -> Integer.compare(a.slot, b.slot));

    if (delegation != null) {
      // `this(...)`/`super(...)` must stay the constructor's first statement; the source
      // declared the hoisted locals right after it.
      List<Exprent> body = delegation.list;
      int at = indexOfIdentity(body, delegation.exprent) + 1;
      if (at <= 0) {
        at = body.size(); // unreachable: never place a declaration before the delegation
      }
      for (Position position : hoisted) {
        body.add(at++, position.exprent);
      }
      return;
    }

    for (Position position : hoisted) {
      List<Exprent> definitions = seq.getVarDefinitions();
      int at = definitions.size();
      for (int i = 0; i < definitions.size(); i++) {
        int slot = declarationSlot(definitions.get(i), varproc);
        if (slot > position.slot) {
          at = i;
          break;
        }
      }
      definitions.add(at, position.exprent);
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
          // Header expressions run before the first body statement only for a while loop; the
          // others run after it, but checking their uses against the entry state is conservative.
          switch (loop.getLooptype()) {
            case WHILE:
            case DO_WHILE:
              exprent(loop.getConditionExprent(), entry);
              break;
            case FOR:
              exprent(loop.getConditionExprent(), entry);
              exprent(loop.getIncExprent(), entry);
              break;
            case FOR_EACH:
              exprent(loop.getIncExprent(), entry);
              break;
            default:
              break;
          }
          Statement body = loop.getFirst();
          if (body != null) {
            stat(body, entry);
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
          if (body != null) {
            stat(body, assigned);
          }
          for (int i = 1; i < catchStatement.getStats().size(); i++) {
            stat(catchStatement.getStats().get(i), assigned);
          }
          // A handler may run after any prefix of the try body.
          return assigned;
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
  }

  // *****************************************************************************
  // names
  // *****************************************************************************

  /** Every printed local name in the method, to detect a hoist that would capture another one. */
  private static final class NameTable {
    private final Map<String, Set<VarVersionPair>> byName = new HashMap<>();

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
          }
        }
      }
    }

    boolean uniqueName(VarExprent var) {
      Set<VarVersionPair> pairs = byName.get(var.getName());
      return pairs != null && pairs.size() == 1 && pairs.contains(var.getVarVersionPair());
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

    Position(Exprent exprent, List<Exprent> list, int slot) {
      this.exprent = exprent;
      this.list = list;
      this.slot = slot;
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

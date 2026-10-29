// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by
// the Apache 2.0 license that can be found in the LICENSE file.

package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A bound method reference's captured receiver that javac parked in a hidden slot, which the
 * decompiler prints as a source local.
 *
 * <p>{@code recv::name} compiles as {@code <recv>; dup; requireNonNull; pop; store T; load T;
 * invokedynamic name} with the receiver captured into slot T. The invokedynamic's implementation
 * method is a static synthetic bridge whose first parameter is that receiver, and javac names the
 * bridge's first parameter {@code rec$} in the bridge's local table — a name only a method
 * reference's bridge carries. The creation site's slot T has no table row of its own and is read
 * exactly once, by the invokedynamic; no source local produces either the store or the missing row.
 * The source expression that produced the receiver therefore stands in for the temp: the capture
 * becomes that expression and the store disappears, so the printer's bridge reader sees
 * {@code recv::name} rather than a lambda over a declared local.
 *
 * <p>The stored value is either a non-stack local (the receiver {@code this}) or an invocation
 * ({@code baseFolder.getFileSystem()::getPath}): javac evaluates the invocation once at the
 * creation site and captures the result, and an invocation prints as a primary expression, so it
 * can stand as the reference's qualifier without parentheses. An invocation fold is taken only
 * when the bridge body is the forward shape the printer reads; otherwise the folded-away local
 * would leave the bridge's printed body referring to a variable that no longer exists.
 */
public final class ReferenceReceiverTemp {
  private ReferenceReceiverTemp() {
  }

  public static boolean fold(Statement root, StructMethod method) {
    // The fold exists to feed the bridge printer: with that printer off, the marker would have
    // no reader and the deleted store would leave the lambda's body dangling.
    if (method == null || !RoundTrip.enabled() || !RoundTrip.selector("reftemp")
        || !RoundTrip.selector("methodrefbridge")) {
      return false;
    }

    List<Statement> statements = new ArrayList<>();
    collectStatements(root, statements);

    // Every occurrence of a temporary's slot must be the store or the invokedynamic's capture:
    // removing the store has to leave no reference behind.
    Map<Integer, List<VarExprent>> occurrences = new HashMap<>();
    for (Statement stat : statements) {
      List<Exprent> exprents = stat.getExprents();
      if (exprents != null) {
        for (Exprent exprent : exprents) {
          if (exprent != null) {
            collectVars(exprent, occurrences);
          }
        }
      }
      for (Exprent exprent : stat.getStatExprents()) {
        if (exprent != null) {
          collectVars(exprent, occurrences);
        }
      }
    }

    // The stores the capture could come from, by slot. A slot stored twice is not a temp the
    // source wrote around this reference.
    Map<Integer, Store> stores = new HashMap<>();
    Set<Integer> ambiguous = new java.util.HashSet<>();
    for (Statement stat : statements) {
      List<Exprent> exprents = stat.getExprents();
      if (exprents == null) {
        continue;
      }
      for (int i = 0; i < exprents.size(); i++) {
        if (!(exprents.get(i) instanceof AssignmentExprent assignment)) {
          continue;
        }
        if (!(assignment.getLeft() instanceof VarExprent temp) || temp.isStack() || temp.getLVT() != null) {
          continue;
        }
        Exprent value = assignment.getRight();
        // Only a local (the receiver `this`) or an invocation is a primary the printer can put
        // before `::` unchanged. New, field, function, array, assignment and constant values
        // would need parentheses, so they stay as a declared temp.
        if (value instanceof VarExprent variable) {
          if (variable.isStack()) {
            continue;
          }
        } else if (!(value instanceof InvocationExprent)) {
          continue;
        }
        if (stores.putIfAbsent(temp.getIndex(),
            new Store(exprents, assignment, temp, value)) != null) {
          ambiguous.add(temp.getIndex());
        }
      }
    }
    if (stores.isEmpty()) {
      return false;
    }

    List<Fold> folds = new ArrayList<>();
    for (Statement stat : statements) {
      List<Exprent> exprents = stat.getExprents();
      if (exprents != null) {
        for (Exprent exprent : exprents) {
          if (exprent != null) {
            collectFolds(exprent, method, stores, ambiguous, occurrences, folds);
          }
        }
      }
      for (Exprent exprent : stat.getStatExprents()) {
        if (exprent != null) {
          collectFolds(exprent, method, stores, ambiguous, occurrences, folds);
        }
      }
    }
    if (folds.isEmpty()) {
      return false;
    }

    for (Fold fold : folds) {
      fold.site().getConstructor().getLstParameters().set(0, fold.store().value().copy());
    }
    // Remove the stores last, deepest list index first: one list may hold several defs, and every
    // fold was matched against the tree as it stood before any removal.
    for (Fold fold : folds) {
      List<Exprent> list = fold.store().list();
      for (int i = list.size() - 1; i >= 0; i--) {
        if (list.get(i) == fold.store().assignment()) {
          list.remove(i);
        }
      }
    }
    return true;
  }

  private static void collectFolds(Exprent exprent, StructMethod method,
                                   Map<Integer, Store> stores, Set<Integer> ambiguous,
                                   Map<Integer, List<VarExprent>> occurrences, List<Fold> folds) {
    if (exprent instanceof NewExprent site) {
      Fold fold = match(site, method, stores, ambiguous, occurrences);
      if (fold != null) {
        folds.add(fold);
      }
    }
    for (Exprent child : exprent.getAllExprents()) {
      if (child != null) {
        collectFolds(child, method, stores, ambiguous, occurrences, folds);
      }
    }
  }

  private static Fold match(NewExprent site, StructMethod method,
                            Map<Integer, Store> stores, Set<Integer> ambiguous,
                            Map<Integer, List<VarExprent>> occurrences) {
    if (!site.isLambda() || site.isMethodReference() || site.getConstructor() == null) {
      return null;
    }
    List<Exprent> parameters = site.getConstructor().getLstParameters();
    if (parameters.isEmpty() || !(parameters.get(0) instanceof VarExprent capture)) {
      return null;
    }
    int slot = capture.getIndex();
    Store store = stores.get(slot);
    if (store == null || ambiguous.contains(slot)) {
      return null;
    }
    Bridge bridge = boundBridge(site);
    if (bridge == null) {
      return null;
    }
    // The receiver temp must be untabled and appear exactly twice: its store and this capture.
    if (named(method, slot, store.temp()) || named(method, slot, capture)) {
      return null;
    }
    List<VarExprent> uses = occurrences.get(slot);
    if (uses == null || uses.size() != 2) {
      return null;
    }
    Set<VarExprent> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    seen.addAll(uses);
    if (!seen.contains(store.temp()) || !seen.contains(capture)) {
      return null;
    }
    if (!immediatelyBefore(method, store.assignment(), capture)) {
      return null;
    }
    // An invocation only prints as the reference's qualifier when the bridge body is the single
    // forward call the bridge printer reads; anything else would delete the temp and leave the
    // printed lambda body referring to a local that no longer exists.
    if (store.value() instanceof InvocationExprent invocation
        && !printableForward(bridge, invocation)) {
      return null;
    }
    return new Fold(site, store);
  }

  /**
   * The invokedynamic's implementation method is javac's bridge for a bound method reference: a
   * static synthetic method whose first parameter, the captured receiver, is named {@code rec$} in
   * its local variable table.
   */
  private static Bridge boundBridge(NewExprent site) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(site.getNewType().value);
    if (node == null || node.lambdaInformation == null || !node.lambdaInformation.is_content_method_static) {
      return null;
    }
    StructClass content = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);
    if (content == null) {
      return null;
    }
    StructMethod bridge = content.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (bridge == null || !bridge.hasModifier(CodeConstants.ACC_STATIC)
      || !bridge.hasModifier(CodeConstants.ACC_SYNTHETIC)) {
      return null;
    }
    StructLocalVariableTableAttribute table = bridge.getLocalVariableAttr();
    if (table == null) {
      return null;
    }
    for (LocalVariable row : table.getVariables().toList()) {
      if (row.getIndex() == 0 && row.getStart() == 0 && "rec$".equals(row.getName())) {
        return new Bridge(content, bridge, node.lambdaInformation.content_method_descriptor,
          node.lambdaInformation.method_descriptor);
      }
    }
    return null;
  }

  /**
   * Whether the bridge's body is the forward shape the bridge printer reads for a bound
   * reference whose qualifier is an invocation: the receiver and the forwarded parameters loaded
   * in order, an empty varargs array packed when the target's last parameter is an array, then
   * exactly one instance call and a plain return. The declared types must line up with the call,
   * and the invocation's own type must satisfy the printer's receiver check; a body with any
   * other instruction gives the printer no reference to write, so the store must stay.
   */
  private static boolean printableForward(Bridge bridge, InvocationExprent receiver) {
    MethodDescriptor content = MethodDescriptor.parseDescriptor(bridge.contentDescriptor());
    MethodDescriptor lambda = MethodDescriptor.parseDescriptor(bridge.lambdaDescriptor());
    int prefix = content.params.length - lambda.params.length;
    if (prefix != 1) {
      return false;
    }
    // Only a congruent bridge prints here: every functional parameter already has the referenced
    // method's own type, so the bridge's remaining parameters must be exactly the call's.
    for (int i = 0; i < lambda.params.length; i++) {
      if (!content.params[prefix + i].equals(lambda.params[i])) {
        return false;
      }
    }
    FullInstructionSequence seq;
    try {
      bridge.method().expandData(bridge.content());
      seq = bridge.method().getInstructionSequence();
    } catch (IOException e) {
      return false;
    }
    if (seq == null || seq.isEmpty()) {
      return false;
    }
    int index = 0;
    int slot = 0;
    for (VarType param : content.params) {
      if (index >= seq.length()) {
        return false;
      }
      Instruction load = seq.getInstr(index);
      if (!isLoad(load.opcode) || slotOf(load) != slot) {
        return false;
      }
      slot += param.stackSize;
      index++;
      while (index < seq.length() && seq.getInstr(index).opcode == CodeConstants.opc_checkcast) {
        index++;
      }
    }
    String packed = null;
    if (index + 1 < seq.length() && intConstant(seq.getInstr(index)) == 0
        && seq.getInstr(index + 1).opcode == CodeConstants.opc_anewarray) {
      packed = bridge.content().getPool().getPrimitiveConstant(seq.getInstr(index + 1).operand(0)).getString();
      index += 2;
    }
    if (index >= seq.length()) {
      return false;
    }
    Instruction call = seq.getInstr(index);
    if (call.opcode != CodeConstants.opc_invokevirtual
        && call.opcode != CodeConstants.opc_invokeinterface
        && call.opcode != CodeConstants.opc_invokespecial) {
      return false;
    }
    LinkConstant target = bridge.content().getPool().getLinkConstant(call.operand(0));
    if (target == null || target.classname == null || target.elementname == null
        || target.descriptor == null) {
      return false;
    }
    MethodDescriptor called = MethodDescriptor.parseDescriptor(target.descriptor);
    int passed = content.params.length - 1;
    if (called.params.length != passed + (packed == null ? 0 : 1)) {
      return false;
    }
    for (int i = 0; i < passed; i++) {
      if (!called.params[i].equals(content.params[i + 1])) {
        return false;
      }
    }
    if (packed != null) {
      VarType last = called.params[passed];
      if (last == null || last.arrayDim != 1 || !packed.equals(last.value)) {
        return false;
      }
    }
    // The printer types the qualifier and requires it to be an instance of the call's owner.
    MethodDescriptor invocation = receiver.getDescriptor();
    VarType receiverType = invocation == null ? null : invocation.ret;
    if (receiverType == null || receiverType.type != CodeType.OBJECT
        || receiverType.arrayDim != 0 || receiverType.value == null
        || !DecompilerContext.getStructContext().instanceOf(receiverType.value, target.classname)) {
      return false;
    }
    index++;
    while (index < seq.length() && (seq.getInstr(index).opcode == CodeConstants.opc_checkcast
        || seq.getInstr(index).opcode == CodeConstants.opc_pop)) {
      index++;
    }
    return index + 1 == seq.length() && isReturn(seq.getInstr(index).opcode);
  }

  /** The value of a small integer constant instruction, or Integer.MIN_VALUE. */
  private static int intConstant(Instruction instr) {
    int opcode = instr.opcode;
    if (opcode >= CodeConstants.opc_iconst_m1 && opcode <= CodeConstants.opc_iconst_5) {
      return opcode - CodeConstants.opc_iconst_0;
    }
    if (opcode == CodeConstants.opc_bipush || opcode == CodeConstants.opc_sipush) {
      return instr.operand(0);
    }
    return Integer.MIN_VALUE;
  }

  /**
   * The store's instruction is the one right before the load the invokedynamic captures: the
   * target stores the receiver into the temp mid-expression, which no separate source statement
   * would do.
   */
  private static boolean immediatelyBefore(StructMethod method, AssignmentExprent definition, VarExprent capture) {
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    if (definition.bytecode == null || definition.bytecode.isEmpty()
      || capture.bytecode == null || capture.bytecode.isEmpty()) {
      return false;
    }
    Integer loadIndex = seq.offsetToIndex().get(capture.bytecode.nextSetBit(0));
    if (loadIndex == null || loadIndex == 0) {
      return false;
    }
    Instruction load = seq.getInstr(loadIndex);
    Instruction store = seq.getInstr(loadIndex - 1);
    return isLoad(load.opcode) && slotOf(load) == capture.getIndex()
      && isStore(store.opcode) && slotOf(store) == capture.getIndex()
      && definition.bytecode.get(store.startOffset);
  }

  private static boolean isStore(int opcode) {
    return opcode >= CodeConstants.opc_istore && opcode <= CodeConstants.opc_astore
      || opcode >= CodeConstants.opc_istore_0 && opcode <= CodeConstants.opc_astore_3;
  }

  private static boolean isLoad(int opcode) {
    return opcode >= CodeConstants.opc_iload && opcode <= CodeConstants.opc_aload
      || opcode >= CodeConstants.opc_iload_0 && opcode <= CodeConstants.opc_aload_3;
  }

  private static boolean isReturn(int opcode) {
    return opcode == CodeConstants.opc_return || opcode == CodeConstants.opc_areturn
      || opcode == CodeConstants.opc_ireturn || opcode == CodeConstants.opc_lreturn
      || opcode == CodeConstants.opc_freturn || opcode == CodeConstants.opc_dreturn;
  }

  /** The slot an {@code iload}..{@code astore} instruction names, short form included. */
  private static int slotOf(Instruction instr) {
    if (instr.opcode >= CodeConstants.opc_iload && instr.opcode <= CodeConstants.opc_aload
      || instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore) {
      return instr.operand(0);
    }
    if (instr.opcode >= CodeConstants.opc_iload_0 && instr.opcode <= CodeConstants.opc_aload_3) {
      return (instr.opcode - CodeConstants.opc_iload_0) % 4;
    }
    return (instr.opcode - CodeConstants.opc_istore_0) % 4;
  }

  /** Whether a table row for {@code slot} covers the instruction at {@code offset}. */
  private static boolean named(StructMethod method, int slot, VarExprent var) {
    if (var.getLVT() != null) {
      return true;
    }
    StructLocalVariableTableAttribute table = method.getLocalVariableAttr();
    if (table == null || var.bytecode == null || var.bytecode.isEmpty()) {
      return false;
    }
    int offset = var.bytecode.nextSetBit(0);
    for (LocalVariable row : table.getVariables().toList()) {
      if (row.getIndex() == slot && row.getStart() <= offset && row.getEnd() > offset) {
        return true;
      }
    }
    return false;
  }

  private static void collectVars(Exprent exprent, Map<Integer, List<VarExprent>> out) {
    if (exprent instanceof VarExprent var) {
      out.computeIfAbsent(var.getIndex(), key -> new ArrayList<>()).add(var);
    }
    for (Exprent child : exprent.getAllExprents()) {
      if (child != null) {
        collectVars(child, out);
      }
    }
  }

  private static void collectStatements(Statement stat, List<Statement> out) {
    out.add(stat);
    for (Statement child : stat.getStats()) {
      collectStatements(child, out);
    }
  }

  private record Store(List<Exprent> list, AssignmentExprent assignment,
                       VarExprent temp, Exprent value) {
  }

  private record Fold(NewExprent site, Store store) {
  }

  /** The bound reference's synthetic bridge and the two descriptors it was created with. */
  private record Bridge(StructClass content, StructMethod method,
                        String contentDescriptor, String lambdaDescriptor) {
  }
}

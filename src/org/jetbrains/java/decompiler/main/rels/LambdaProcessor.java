// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main.rels;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.main.ClassesProcessor;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructContext;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructBootstrapMethodsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;

import java.io.IOException;
import java.util.*;

public class LambdaProcessor {
  @SuppressWarnings("SpellCheckingInspection") private static final String JAVAC_LAMBDA_CLASS = "java/lang/invoke/LambdaMetafactory";
  @SuppressWarnings("SpellCheckingInspection") private static final String JAVAC_LAMBDA_METHOD = "metafactory";
  @SuppressWarnings("SpellCheckingInspection") private static final String JAVAC_LAMBDA_ALT_METHOD = "altMetafactory";

  /** javac names a lowered lambda's method after its owner: {@code lambda$<owner>$<n>}. */
  private static final String LAMBDA_METHOD_PREFIX = "lambda$";
  /**
   * The functional interface an orphan is printed with. The class file records no trace of the
   * interface the source named — a lambda's target type is only in its call site, and an orphan
   * has none — so any interface with one parameter and a void method reproduces the synthetic
   * method javac made; {@code Consumer} is the canonical one.
   */
  private static final String ORPHAN_SAM_CLASS = "java/util/function/Consumer";
  private static final String ORPHAN_SAM_METHOD = "accept";

  public void processClass(ClassNode node) throws IOException {
    for (ClassNode child : node.nested) {
      processClass(child);
    }

    ClassesProcessor clProcessor = DecompilerContext.getClassProcessor();
    StructClass cl = node.classStruct;

    if (!cl.getVersion().hasLambdas()) { // lambda beginning with Java 8
      return;
    }

    // Before the bootstrap checks: javac lowers every lambda before Lower prunes a dead branch, so
    // a class can hold a lambda method with no bootstrap method at all, and the scan below would
    // return early on it.
    registerOrphanLambdas(node, cl);

    StructBootstrapMethodsAttribute bootstrap = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_BOOTSTRAP_METHODS);
    if (bootstrap == null || bootstrap.getMethodsNumber() == 0) {
      return; // no bootstrap constants in pool
    }

    BitSet lambdaMethods = new BitSet();

    // find lambda bootstrap constants
    for (int i = 0; i < bootstrap.getMethodsNumber(); ++i) {
      LinkConstant method_ref = bootstrap.getMethodReference(i); // method handle

      // FIXME: extend for Eclipse etc. at some point
      if (JAVAC_LAMBDA_CLASS.equals(method_ref.classname) &&
          (JAVAC_LAMBDA_METHOD.equals(method_ref.elementname) || JAVAC_LAMBDA_ALT_METHOD.equals(method_ref.elementname))) {
        lambdaMethods.set(i);
      }
    }

    if (lambdaMethods.isEmpty()) {
      return; // no lambda bootstrap constant found
    }

    Map<String, String> mapMethodsLambda = new HashMap<>();

    // iterate over code and find invocations of bootstrap methods. Replace them with anonymous classes.
    for (StructMethod mt : cl.getMethods()) {
      mt.expandData(cl);

      FullInstructionSequence seq = mt.getInstructionSequence();
      if (seq != null) {
        for (var instr : seq) {
          if (instr.opcode == CodeConstants.opc_invokedynamic) {
            LinkConstant invoke_dynamic = cl.getPool().getLinkConstant(instr.operand(0));

            if (lambdaMethods.get(invoke_dynamic.index1)) { // lambda invocation found

              List<PooledConstant> bootstrap_arguments = bootstrap.getMethodArguments(invoke_dynamic.index1);
              MethodDescriptor md = MethodDescriptor.parseDescriptor(invoke_dynamic.descriptor);

              String lambda_class_name = md.ret.value;
              String lambda_method_name = invoke_dynamic.elementname;
              String lambda_method_descriptor = ((PrimitiveConstant)bootstrap_arguments.get(2)).getString(); // method type

              LinkConstant content_method_handle = (LinkConstant)bootstrap_arguments.get(1);

              ClassNode node_lambda = new ClassNode(content_method_handle.classname, content_method_handle.elementname,
                                                    content_method_handle.descriptor, content_method_handle.index1,
                                                    lambda_class_name, lambda_method_name, lambda_method_descriptor, cl);
              node_lambda.simpleName = cl.qualifiedName + "##Lambda_" + invoke_dynamic.index1 + "_" + invoke_dynamic.index2;
              node_lambda.enclosingMethod = InterpreterUtil.makeUniqueKey(mt.getName(), mt.getDescriptor());

              node.nested.add(node_lambda);
              node_lambda.parent = node;

              clProcessor.getMapRootClasses().put(node_lambda.simpleName, node_lambda);
              if (!node_lambda.lambdaInformation.is_method_reference) {
                mapMethodsLambda.put(node_lambda.lambdaInformation.content_method_key, node_lambda.simpleName);
              }
            }
          }
        }
      }

      mt.releaseResources();
    }

    Collections.sort(node.nested);

    // build class hierarchy on lambda
    for (ClassNode nd : node.nested) {
      if (nd.type == ClassNode.Type.LAMBDA) {
        String parent_class_name = mapMethodsLambda.get(nd.enclosingMethod);
        if (parent_class_name != null) {
          ClassNode parent_class = clProcessor.getMapRootClasses().get(parent_class_name);

          if (nd == parent_class) {
            throw new IllegalStateException("Lambda " + nd.classStruct.qualifiedName + " is recursive?!");
          }
          parent_class.nested.add(nd);
          nd.parent = parent_class;
          // TODO: is this needed?
//          Collections.sort(parent_class.nested);
        }
      }
    }

    // FIXME: mixed hierarchy?
  }

  /**
   * Registers the lambda content methods nothing in the class refers to.
   *
   * <p>javac lowers every lambda before Lower prunes a branch whose condition is a constant false,
   * so the synthetic method of a lambda inside that branch is emitted with no call site binding
   * it. Only the method's own attributes say what it is, and the printer can only reproduce it by
   * printing a dead block that holds the lambda again; this registers the method so the writer can
   * do that. Everything the printer needs must be proved by the class file, so a method is
   * registered only when all of it holds:
   * <ul>
   *   <li>the name is {@code lambda$<owner>$<n>} for one declared method of the class, and the
   *       owner is an ordinary method — a dead block at the head of a constructor would precede
   *       its {@code super()} call;</li>
   *   <li>the pool binds the method nowhere — no method handle, no direct reference;</li>
   *   <li>it is static, so its parameters are captures followed by the functional parameters, and
   *       its return is void, which is what the canonical functional interface prints;</li>
   *   <li>it has exactly one functional parameter: every earlier parameter is a parameter of the
   *       owner, by the name and type the method's own local table records — that is the scope the
   *       dead block is printed in, so a capture read from a later local is refused rather than
   *       printed out of scope;</li>
   *   <li>the functional parameter is a plain, non-generic class, so no erased type has to be
   *       printed for it.</li>
   * </ul>
   * Two orphans for one owner are refused: the class file does not say where their dead blocks
   * sat relative to each other, and their lambda indices only follow that order.
   */
  private static void registerOrphanLambdas(ClassNode node, StructClass cl) {
    if (!RoundTrip.selector("orphanlambda") || node.type == ClassNode.Type.LAMBDA) {
      // A lambda node carries its parent's class; the class's own node registers for it.
      return;
    }

    Map<String, List<StructMethod>> candidates = new LinkedHashMap<>();
    for (StructMethod lambda : cl.getMethods()) {
      if (!lambda.hasModifier(CodeConstants.ACC_SYNTHETIC) || !lambda.hasModifier(CodeConstants.ACC_STATIC)
          || !lambda.containsCode() || !lambda.getName().startsWith(LAMBDA_METHOD_PREFIX)) {
        continue;
      }
      StructMethod owner = ownerOf(cl, lambda.getName());
      if (owner == null || !acceptsAsOrphan(lambda, owner) || isReferenced(cl, lambda)) {
        continue;
      }
      candidates.computeIfAbsent(InterpreterUtil.makeUniqueKey(owner.getName(), owner.getDescriptor()),
        key -> new ArrayList<>()).add(lambda);
    }

    for (Map.Entry<String, List<StructMethod>> entry : candidates.entrySet()) {
      if (entry.getValue().size() != 1) {
        continue;
      }
      StructMethod lambda = entry.getValue().get(0);
      StructMethod owner = cl.getMethod(entry.getKey());
      if (owner == null) {
        continue;
      }
      MethodDescriptor md = MethodDescriptor.parseDescriptor(lambda.getDescriptor());
      String functional = "(" + md.params[md.params.length - 1] + ")V";

      ClassNode orphan = new ClassNode(cl.qualifiedName, lambda.getName(), lambda.getDescriptor(),
        CodeConstants.CONSTANT_MethodHandle_REF_invokeStatic,
        ORPHAN_SAM_CLASS, ORPHAN_SAM_METHOD, functional, cl);
      orphan.simpleName = cl.qualifiedName + "##Orphan_" + lambda.getName();
      orphan.enclosingMethod = entry.getKey();
      orphan.parent = node;
      node.orphanLambdas.put(entry.getKey(), orphan);
    }
  }

  /** The declared method a lambda method is named after, or null when none matches. */
  private static StructMethod ownerOf(StructClass cl, String lambdaName) {
    StructMethod owner = null;
    for (StructMethod candidate : cl.getMethods()) {
      if (candidate.isSynthetic() || !lambdaName.startsWith(LAMBDA_METHOD_PREFIX + candidate.getName() + "$")) {
        continue;
      }
      String index = lambdaName.substring(LAMBDA_METHOD_PREFIX.length() + candidate.getName().length() + 1);
      if (index.isEmpty() || !index.chars().allMatch(Character::isDigit)) {
        continue;
      }
      if (owner == null || candidate.getName().length() > owner.getName().length()) {
        owner = candidate;
      }
    }
    return owner;
  }

  /**
   * Whether the class's pool binds this method: a method handle (a call site, a method reference)
   * or a direct reference. A lowered lambda's method is bound by the call site that created it, so
   * an unreferenced one had its creation site removed from the code.
   */
  private static boolean isReferenced(StructClass cl, StructMethod lambda) {
    for (PooledConstant constant : cl.getPool().getPool()) {
      if (constant instanceof LinkConstant link
          && cl.qualifiedName.equals(link.classname)
          && lambda.getName().equals(link.elementname)
          && lambda.getDescriptor().equals(link.descriptor)) {
        return true;
      }
    }
    return false;
  }

  /** Whether the method's attributes prove the shape the writer prints an orphan lambda with. */
  private static boolean acceptsAsOrphan(StructMethod lambda, StructMethod owner) {
    if (owner.isSynthetic() || CodeConstants.INIT_NAME.equals(owner.getName())
        || CodeConstants.CLINIT_NAME.equals(owner.getName())) {
      return false;
    }

    MethodDescriptor md = MethodDescriptor.parseDescriptor(lambda.getDescriptor());
    if (md.params.length < 1 || !VarType.VARTYPE_VOID.equals(md.ret)) {
      return false;
    }

    StructLocalVariableTableAttribute lvt = lambda.getLocalVariableAttr();
    if (lvt == null) {
      return false;
    }
    int slot = 0;
    String[] names = new String[md.params.length];
    for (int i = 0; i < md.params.length; i++) {
      names[i] = lvt.getName(slot, 0);
      if (names[i] == null) {
        return false;
      }
      slot += md.params[i].stackSize;
    }

    for (int i = 0; i < md.params.length - 1; i++) {
      if (!ownerParameter(owner, names[i], md.params[i], true)) {
        return false;
      }
    }

    String functionalName = names[names.length - 1];
    if (ownerParameter(owner, functionalName, null, false)) {
      return false; // the name alone proves nothing: it could be a capture as well
    }
    return isPrintableFunctionalType(md.params[md.params.length - 1]);
  }

  /** Whether the owner declares a parameter with this name, and, when given, this type. */
  private static boolean ownerParameter(StructMethod owner, String name, VarType type, boolean matchType) {
    StructLocalVariableTableAttribute lvt = owner.getLocalVariableAttr();
    if (lvt == null) {
      return false;
    }
    MethodDescriptor md = MethodDescriptor.parseDescriptor(owner.getDescriptor());
    int slot = owner.hasModifier(CodeConstants.ACC_STATIC) ? 0 : 1;
    for (VarType param : md.params) {
      if (name.equals(lvt.getName(slot, 0)) && (!matchType || param.equals(type))) {
        return true;
      }
      slot += param.stackSize;
    }
    return false;
  }

  /**
   * Whether the functional parameter's type can be printed as it stands: a class (not a type
   * variable, not an array, not a primitive, whose correction would need boxing) whose own
   * declaration records no type parameters. A generic class would have to be printed raw, and a
   * raw type is an erased stand-in the source never wrote.
   */
  private static boolean isPrintableFunctionalType(VarType type) {
    if (type.type != CodeType.OBJECT || type.arrayDim != 0 || type.value == null) {
      return false;
    }
    StructContext context = DecompilerContext.getStructContext();
    StructClass named = context == null ? null : context.getClass(type.value);
    return named == null || named.getSignature() == null || named.getSignature().fparameters.isEmpty();
  }
}

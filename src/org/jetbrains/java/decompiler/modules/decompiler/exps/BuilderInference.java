// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Solves the type argument of a {@code RecordCodecBuilder.create}/{@code mapCodec} call from the
 * declared generic signatures the class files record. The builder chain
 * {@code create(i -> i.group(a, b).apply(i, Factory::of))} determines the argument uniquely:
 * every group component is an {@code App<Mu<O>, T>} (a {@code RecordCodecBuilder<_, T>}), the
 * functional argument's method reference fixes the result {@code R}, and the lambda must return
 * {@code App<Mu<O>, O>}, so {@code O = R}. javac's own inference resolves the nested method
 * reference before {@code O} is known and fails, which is why the original source pinned the
 * argument; the constraints themselves are nevertheless all present in the class files.
 */
public final class BuilderInference {
  private static final String BUILDER = "com/mojang/serialization/codecs/RecordCodecBuilder";
  private static final String APP = "com/mojang/datafixers/kinds/App";
  private static final String PRODUCTS = "com/mojang/datafixers/Products$P";
  private static final String FUNCTION = "java/util/function/Function";
  private static final int MAX_DEPTH = 3;

  private static final ThreadLocal<Boolean> SOLVING = ThreadLocal.withInitial(() -> Boolean.FALSE);

  private BuilderInference() {
  }

  /**
   * Returns the solved value of the call's type variable, keyed as {@code T<name>;}, or null when
   * the call is not the builder shape or the solution is not fully determined, printable and in
   * scope. The caller seeds its generic map with the result.
   */
  public static @Nullable Map<VarType, VarType> solve(InvocationExprent call, List<String> fparams) {
    if (SOLVING.get()) {
      return null;
    }
    SOLVING.set(Boolean.TRUE);
    try {
      return solveInner(call, fparams);
    }
    catch (RuntimeException e) {
      return null;
    }
    finally {
      SOLVING.set(Boolean.FALSE);
    }
  }

  private static @Nullable Map<VarType, VarType> solveInner(InvocationExprent call, List<String> fparams) {
    if (fparams.size() != 1 || call.getFunctype() == InvocationExprent.Type.INIT || !BUILDER.equals(call.getClassname())) {
      return null;
    }
    if (!call.isRecordedCallSite()) {
      return null;
    }
    StructMethod method = call.getDesc();
    if (method == null || method.getSignature() == null) {
      return null;
    }
    List<VarType> declaredParams = method.getSignature().parameterTypes;
    if (declaredParams.size() != 1 || !(declaredParams.get(0) instanceof GenericType function)
      || !FUNCTION.equals(function.value) || function.getArguments().size() != 2) {
      return null;
    }

    // Function<Instance<O>, ? extends App<Mu<O>, O>>
    VarType samArg = strip(function.getArguments().get(0));
    VarType samRet = strip(function.getArguments().get(1));
    if (!(samRet instanceof GenericType app) || !APP.equals(app.value) || app.getArguments().size() != 2) {
      return null;
    }
    VarType expected = app.getArguments().get(1);
    if (expected == null || expected.type != CodeType.GENVAR || !expected.value.equals(fparams.get(0))) {
      return null;
    }

    if (call.getLstParameters().size() != 1 || !(call.getLstParameters().get(0) instanceof NewExprent lambda)
      || !lambda.isLambda() || lambda.isMethodReference()) {
      return null;
    }
    ClassNode lambdaNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(lambda.getNewType().value);
    if (lambdaNode == null || lambdaNode.lambdaInformation == null) {
      return null;
    }

    InvocationExprent apply = lambdaBodyReturn(lambdaNode);
    if (apply == null || !"apply".equals(apply.getName()) || !apply.getClassname().startsWith(PRODUCTS)
      || apply.getLstParameters().size() != 2) {
      return null;
    }
    int arity = apply.getClassname().length() > PRODUCTS.length()
      ? apply.getClassname().charAt(PRODUCTS.length()) - '0' : -1;
    if (arity < 2 || arity > 6) {
      return null;
    }
    if (!(apply.getInstance() instanceof InvocationExprent group) || !"group".equals(group.getName())
      || group.getLstParameters().size() != arity) {
      return null;
    }
    if (!(apply.getLstParameters().get(1) instanceof NewExprent reference) || !reference.isMethodReference()) {
      return null;
    }
    // The instance passed to apply is the lambda's own parameter, the receiver of group.
    if (!(group.getInstance() instanceof VarExprent receiver) || !(apply.getLstParameters().get(0) instanceof VarExprent passed)
      || receiver.getIndex() != passed.getIndex()) {
      return null;
    }

    // Type variables of the enclosing method/class are nameable at the call site; nothing else is.
    Map<VarType, List<VarType>> named = call.getNamedGenerics();

    List<VarType> componentTypes = new ArrayList<>();
    for (Exprent component : group.getLstParameters()) {
      VarType type = typeOf(component, 0);
      if (!(type instanceof GenericType record) || !BUILDER.equals(record.value) || record.getArguments().size() != 2) {
        return null;
      }
      VarType argument = record.getArguments().get(1);
      if (!isNameable(argument, named)) {
        return null;
      }
      componentTypes.add(argument);
    }

    Unifier unifier = new Unifier();
    VarType result = referenceResult(reference, componentTypes, unifier);
    if (result == null || !unifier.unify(expected, result)) {
      return null;
    }

    VarType solved = unifier.resolve(expected);
    if (!isNameable(solved, named)) {
      return null;
    }
    for (VarType value : unifier.values()) {
      if (!isNameable(value, named)) {
        return null;
      }
    }

    // The substitution must keep the erased functional shape the class file recorded for the lambda.
    MethodDescriptor recorded = MethodDescriptor.parseDescriptor(lambdaNode.lambdaInformation.method_descriptor);
    if (recorded.params.length != 1 || samArg == null || samRet == null) {
      return null;
    }
    if (!unifier.substitute(samArg).equals(recorded.params[0]) || !unifier.substitute(samRet).equals(recorded.ret)) {
      return null;
    }

    Map<VarType, VarType> mapping = new HashMap<>();
    mapping.put(expected, solved);
    return mapping;
  }

  /** The expression a single-return lambda body returns. */
  private static @Nullable InvocationExprent lambdaBodyReturn(ClassNode lambdaNode) {
    ClassWrapper wrapper = lambdaNode.getWrapper();
    if (wrapper == null) {
      return null;
    }
    MethodWrapper method = wrapper.getMethodWrapper(lambdaNode.lambdaInformation.content_method_name,
      lambdaNode.lambdaInformation.content_method_descriptor);
    if (method == null || method.root == null) {
      return null;
    }
    Statement first = method.root.getFirst();
    if (!(first instanceof BasicBlockStatement block) || block.getExprents() == null || block.getExprents().size() != 1) {
      return null;
    }
    Exprent exprent = block.getExprents().get(0);
    if (!(exprent instanceof ExitExprent exit) || exit.getExitType() != ExitExprent.Type.RETURN) {
      return null;
    }
    return exit.getValue() instanceof InvocationExprent invocation ? invocation : null;
  }

  /**
   * The result of applying the functional argument's method reference to {@code arguments}: the
   * referenced method's declared parameter types are unified with the argument types and its
   * declared return type is substituted.
   */
  private static @Nullable VarType referenceResult(NewExprent reference, List<VarType> arguments, Unifier unifier) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(reference.getNewType().value);
    if (node == null || node.lambdaInformation == null) {
      return null;
    }
    String className = node.lambdaInformation.content_class_name;
    StructClass content = DecompilerContext.getStructContext().getClass(className);
    if (content == null) {
      return null;
    }
    StructMethod method = content.getMethodRecursive(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (method == null || method.getSignature() == null || !method.hasModifier(CodeConstants.ACC_STATIC)) {
      return null;
    }
    GenericMethodDescriptor signature = method.getSignature();
    if (signature.parameterTypes.size() != arguments.size()) {
      return null;
    }
    for (int i = 0; i < arguments.size(); i++) {
      if (!unifier.unify(signature.parameterTypes.get(i), arguments.get(i))) {
        return null;
      }
    }
    return unifier.substitute(signature.returnType);
  }

  /**
   * The type an expression contributes to the chain: the printer's own inference when it is
   * parameterized, else the declared return type of the call with the receiver's type arguments
   * substituted (synthetic lambda methods and fresh method variables defeat the former).
   */
  private static @Nullable VarType typeOf(Exprent exprent, int depth) {
    if (depth > MAX_DEPTH) {
      return null;
    }
    if (exprent instanceof VarExprent) {
      return exprent.getInferredExprType(null);
    }
    if (!(exprent instanceof InvocationExprent call)) {
      return null;
    }
    VarType inferred = call.getInferredExprType(null);
    if (inferred != null && inferred.isGeneric() && inferred.type == CodeType.OBJECT) {
      return inferred;
    }
    StructMethod method = call.getDesc();
    if (method == null || method.getSignature() == null || call.getInstance() == null) {
      return inferred;
    }
    VarType receiver = typeOf(call.getInstance(), depth + 1);
    if (receiver == null || !receiver.isGeneric()) {
      return inferred;
    }
    String declaring = method.getClassQualifiedName().replace('.', '/');
    VarType projected = GenericType.getGenericSuperType(receiver,
      new VarType(CodeType.OBJECT, 0, declaring));
    if (!(projected instanceof GenericType generic) || !declaring.equals(generic.value)) {
      return inferred;
    }
    StructClass owner = DecompilerContext.getStructContext().getClass(declaring);
    if (owner == null || owner.getSignature() == null) {
      return inferred;
    }
    List<String> names = owner.getSignature().fparameters;
    List<VarType> actual = generic.getArguments();
    if (names.size() != actual.size()) {
      return inferred;
    }
    Map<VarType, VarType> map = new HashMap<>();
    for (int i = 0; i < names.size(); i++) {
      VarType argument = actual.get(i);
      if (argument == null) {
        return inferred;
      }
      map.put(GenericType.parse("T" + names.get(i) + ";"), argument);
    }
    return method.getSignature().returnType.remap(map);
  }

  private static @Nullable VarType strip(VarType type) {
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return GenericType.withWildcard(generic, GenericType.WILDCARD_NO);
    }
    return type;
  }

  /**
   * A type the source can spell at the call site: no wildcard, no bare generic class (a raw type
   * the record never has), and every type variable declared by the enclosing class or method.
   */
  private static boolean isNameable(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null || type == GenericType.DUMMY_VAR) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return named.containsKey(type);
    }
    if (!(type instanceof GenericType generic)) {
      return true;
    }
    if (generic.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    List<VarType> arguments = generic.getArguments();
    for (VarType argument : arguments) {
      if (argument != null && !isNameable(argument, named)) {
        return false;
      }
    }
    if (arguments.isEmpty()) {
      StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
      return cls == null || cls.getSignature() == null || cls.getSignature().fparameters.isEmpty();
    }
    return true;
  }

  /** Structural unification over the declared signatures; unlike mapGenVarsTo it can fail. */
  private static final class Unifier {
    private final Map<VarType, VarType> values = new HashMap<>();

    java.util.Collection<VarType> values() {
      return values.values();
    }

    VarType resolve(VarType type) {
      int guard = 0;
      while (type != null && type.type == CodeType.GENVAR && values.containsKey(type) && guard++ < 16) {
        type = values.get(type);
      }
      return type;
    }

    boolean unify(VarType pattern, VarType actual) {
      VarType left = resolve(pattern);
      VarType right = resolve(actual);
      if (left == null || right == null) {
        return false;
      }
      if (left.type == CodeType.GENVAR) {
        return bind(left, right);
      }
      if (right.type == CodeType.GENVAR) {
        return bind(right, left);
      }
      if (!left.equals(right)) {
        return false;
      }
      if (left instanceof GenericType genericLeft && right instanceof GenericType genericRight) {
        List<VarType> leftArgs = genericLeft.getArguments();
        List<VarType> rightArgs = genericRight.getArguments();
        if (leftArgs.size() != rightArgs.size()) {
          return false;
        }
        for (int i = 0; i < leftArgs.size(); i++) {
          VarType a = leftArgs.get(i);
          VarType b = rightArgs.get(i);
          if (a == null || b == null) {
            if (a != b) {
              return false;
            }
          }
          else if (!unify(a, b)) {
            return false;
          }
        }
      }
      return true;
    }

    boolean bind(VarType variable, VarType type) {
      VarType existing = values.get(variable);
      if (existing != null) {
        return unify(existing, type);
      }
      if (variable.equals(type)) {
        return true;
      }
      values.put(variable, type);
      return true;
    }

    VarType substitute(VarType type) {
      if (type == null) {
        return null;
      }
      if (type.type == CodeType.GENVAR) {
        VarType value = resolve(type);
        return value == type ? type : substitute(value);
      }
      if (!(type instanceof GenericType generic)) {
        return type;
      }
      List<VarType> arguments = generic.getArguments();
      List<VarType> substituted = new ArrayList<>(arguments.size());
      boolean changed = false;
      for (VarType argument : arguments) {
        VarType value = argument == null ? null : substitute(argument);
        if (value != argument) {
          changed = true;
        }
        substituted.add(value);
      }
      if (!changed) {
        return type;
      }
      return new GenericType(type.type, type.arrayDim, type.value, generic.getParent(),
        Collections.unmodifiableList(substituted), generic.getWildcard());
    }
  }
}

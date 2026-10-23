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
   * Solves the receiver's class type variable of an instance call that takes only a method
   * reference, and writes the solution into the expected-type map the receiver is inferred with.
   * {@code StreamCodec.apply(ByteBufCodecs::optional)} is the shape: javac gives the receiver
   * expression no target, so codec's own variable defaults to its bound, while the reference's
   * recorded Signature (optional's, {@code StreamCodec<? super B,V> -> StreamCodec<B,Optional<V>>})
   * and the call's functional interface bind the receiver's value type to the type the call's
   * other type arguments already fix. Before unifying, the implementation's type variables are
   * alpha-renamed so names shared with the caller or the interface cannot collide.
   *
   * @param known the call's type arguments already solved from its target, keyed as
   *              {@code T<name>;}
   * @param target the expected-type map of the call, into which the receiver's variable is written
   * @return whether any receiver class variable was fixed
   */
  public static boolean solveReceiverFromReference(InvocationExprent call, List<String> fparams,
                                                   Map<VarType, VarType> known, Map<VarType, VarType> target) {
    if (SOLVING.get()) {
      return false;
    }
    SOLVING.set(Boolean.TRUE);
    try {
      return solveReceiverFromReferenceInner(call, fparams, known, target);
    }
    catch (RuntimeException e) {
      return false;
    }
    finally {
      SOLVING.set(Boolean.FALSE);
    }
  }

  private static boolean solveReceiverFromReferenceInner(InvocationExprent call, List<String> fparams,
                                                         Map<VarType, VarType> known, Map<VarType, VarType> target) {
    if (call.getFunctype() == InvocationExprent.Type.INIT
      || call.getInvocationType() == InvocationExprent.InvocationType.STATIC
      || call.getInvocationType() == InvocationExprent.InvocationType.DYNAMIC
      || call.getInvocationType() == InvocationExprent.InvocationType.CONSTANT_DYNAMIC
      || fparams.isEmpty() || call.getInstance() == null || !call.isRecordedCallSite()
      || call.getLstParameters().size() != 1
      || !(call.getLstParameters().get(0) instanceof NewExprent reference)
      || !reference.isMethodReference()) {
      return false;
    }
    StructMethod callee = call.getDesc();
    if (callee == null || callee.getSignature() == null || callee.getSignature().parameterTypes.size() != 1
      || !(callee.getSignature().parameterTypes.get(0) instanceof GenericType samType)) {
      return false;
    }
    StructClass calleeClass = DecompilerContext.getStructContext().getClass(call.getClassname());
    if (calleeClass == null || calleeClass.getSignature() == null) {
      return false;
    }
    ClassNode referenceNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(reference.getNewType().value);
    if (referenceNode == null || referenceNode.lambdaInformation == null
      || !referenceNode.lambdaInformation.is_method_reference) {
      return false;
    }
    StructClass samClass = DecompilerContext.getStructContext().getClass(samType.value);
    if (samClass == null || samClass.getSignature() == null) {
      return false;
    }
    List<String> interfaceParams = samClass.getSignature().fparameters;
    List<VarType> interfaceArgs = samType.getArguments();
    if (interfaceParams.isEmpty() || interfaceParams.size() != interfaceArgs.size()) {
      return false;
    }
    int samArity = MethodDescriptor.parseDescriptor(referenceNode.lambdaInformation.method_descriptor).params.length;
    StructMethod samMethod = null;
    for (StructMethod candidate : samClass.getMethods()) {
      if (!referenceNode.lambdaInformation.method_name.equals(candidate.getName())
        || candidate.hasModifier(CodeConstants.ACC_STATIC)
        || !candidate.hasModifier(CodeConstants.ACC_ABSTRACT)
        || MethodDescriptor.parseDescriptor(candidate.getDescriptor()).params.length != samArity) {
        continue;
      }
      if (samMethod != null) {
        return false;
      }
      samMethod = candidate;
    }
    if (samMethod == null || samMethod.getSignature() == null || !samMethod.getSignature().typeParameters.isEmpty()) {
      return false;
    }
    StructClass content = DecompilerContext.getStructContext().getClass(referenceNode.lambdaInformation.content_class_name);
    if (content == null || (content.getSignature() != null && !content.getSignature().fparameters.isEmpty())) {
      return false;
    }
    StructMethod implementation = content.getMethodRecursive(referenceNode.lambdaInformation.content_method_name,
      referenceNode.lambdaInformation.content_method_descriptor);
    if (implementation == null || implementation.getSignature() == null
      || !implementation.hasModifier(CodeConstants.ACC_STATIC)
      || implementation.getSignature().typeParameters.isEmpty()) {
      return false;
    }

    Map<VarType, VarType> interfaceMap = new HashMap<>();
    for (int i = 0; i < interfaceParams.size(); i++) {
      VarType argument = interfaceArgs.get(i);
      if (argument == null) {
        return false;
      }
      interfaceMap.put(GenericType.parse("T" + interfaceParams.get(i) + ";"), argument);
    }
    // Tag the call side too: a class variable of the callee (Optional's T) and a variable the
    // caller's target mentions can share a name while being different variables.
    Map<VarType, VarType> sideRename = sideRename(calleeClass, fparams);
    GenericMethodDescriptor samSignature = samMethod.getSignature();
    List<VarType> samParams = new ArrayList<>(samSignature.parameterTypes.size());
    for (VarType parameter : samSignature.parameterTypes) {
      VarType instantiated = parameter.remap(interfaceMap);
      if (instantiated == null) {
        return false;
      }
      samParams.add(instantiated.remap(sideRename));
    }
    VarType samReturn = samSignature.returnType.remap(interfaceMap);
    if (samReturn == null) {
      return false;
    }
    samReturn = samReturn.remap(sideRename);
    GenericMethodDescriptor implSignature = implementation.getSignature();
    if (samParams.size() != implSignature.parameterTypes.size()) {
      return false;
    }

    // Tag the implementation's type variables so a name it shares with the caller's class or
    // method (optional's B against StreamCodec's B) cannot be mistaken for the same variable.
    Map<VarType, VarType> rename = renameTypeVariables(implSignature.typeParameters);
    List<VarType> implParams = new ArrayList<>(implSignature.parameterTypes.size());
    for (VarType parameter : implSignature.parameterTypes) {
      implParams.add(parameter.remap(rename));
    }
    VarType implReturn = implSignature.returnType.remap(rename);

    Unifier unifier = new Unifier();
    for (int i = 0; i < samParams.size(); i++) {
      if (!unifier.unify(samParams.get(i), implParams.get(i))) {
        return false;
      }
    }
    if (!unifier.unify(samReturn, implReturn)) {
      return false;
    }

    // The call's own target already solved some of the interface's type arguments (the method's
    // O); those values solve the implementation's variables, and through them the receiver's.
    boolean informed = false;
    for (int i = 0; i < interfaceParams.size(); i++) {
      VarType argument = interfaceArgs.get(i);
      if (argument == null || argument.type != CodeType.GENVAR || !fparams.contains(argument.value)) {
        continue;
      }
      VarType value = known.get(argument);
      if (value == null || GenericType.DUMMY_VAR.equals(value)) {
        continue;
      }
      VarType solved = unifier.substitute(argument.remap(sideRename));
      if (solved == null || !unifier.unify(solved, value)) {
        return false;
      }
      informed = true;
    }
    if (!informed) {
      return false;
    }

    // The substituted interface signature must erase to the method the MethodHandle records.
    MethodDescriptor recorded = MethodDescriptor.parseDescriptor(referenceNode.lambdaInformation.content_method_descriptor);
    if (recorded.params.length != samParams.size()) {
      return false;
    }
    for (int i = 0; i < samParams.size(); i++) {
      VarType erased = eraseWithWildcards(samParams.get(i), unifier);
      if (erased == null || !erased.equals(recorded.params[i])) {
        return false;
      }
    }
    VarType erasedReturn = eraseWithWildcards(samReturn, unifier);
    if (erasedReturn == null || !erasedReturn.equals(recorded.ret)) {
      return false;
    }

    Map<VarType, List<VarType>> named = call.getNamedGenerics();
    List<String> classParams = calleeClass.getSignature().fparameters;
    boolean seeded = false;
    for (int i = 0; i < interfaceParams.size(); i++) {
      VarType argument = interfaceArgs.get(i);
      if (argument == null || argument.type != CodeType.GENVAR || !classParams.contains(argument.value)) {
        continue;
      }
      VarType solved = unifier.substitute(argument.remap(sideRename));
      if (solved == null || GenericType.DUMMY_VAR.equals(solved) || containsTaggedVariable(solved)
        || !isNameable(solved, named) || !isConcrete(solved)) {
        // A value that still mentions any type variable is the printer's own chain inference,
        // not something the recorded signatures fix; only a closed type is written down.
        continue;
      }
      VarType prior = target.get(argument);
      if (prior != null && !GenericType.DUMMY_VAR.equals(prior)) {
        continue;
      }
      target.put(argument, solved);
      seeded = true;
    }
    return seeded;
  }

  /**
   * The erasure of a substituted signature type for a comparison with the recorded method
   * descriptor. A variable the signature left unsolved erases to Object: its own bound cannot
   * change the erasure of a position inside a parameterized type, and a bare variable position
   * is rejected by the caller's descriptor comparison instead.
   */
  private static @Nullable VarType eraseWithWildcards(VarType type, Unifier unifier) {
    VarType resolved = unifier.resolve(type);
    if (resolved == null) {
      return null;
    }
    if (resolved.type == CodeType.GENVAR) {
      return new VarType(CodeType.OBJECT, resolved.arrayDim, "java/lang/Object");
    }
    if (resolved.type == CodeType.OBJECT) {
      return new VarType(CodeType.OBJECT, resolved.arrayDim, resolved.value);
    }
    return resolved;
  }

  /** Whether a type still mentions a variable renamed for either side of the unification. */
  private static boolean containsTaggedVariable(VarType type) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return type.value.startsWith(RENAME_PREFIX) || type.value.startsWith(SIDE_PREFIX);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (containsTaggedVariable(argument)) {
          return true;
        }
      }
    }
    return false;
  }

  /** A type with no type variable, wildcard or unbound argument anywhere inside it. */
  private static boolean isConcrete(VarType type) {
    if (type == null || type == GenericType.DUMMY_VAR || type.type == CodeType.GENVAR) {
      return false;
    }
    if (!(type instanceof GenericType generic)) {
      return true;
    }
    if (generic.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument != null && !isConcrete(argument)) {
        return false;
      }
    }
    return true;
  }

  private static final String RENAME_PREFIX = "vf$";
  private static final String SIDE_PREFIX = "vs$";

  /** The call side's variables: the callee's class type parameters and the method's own. */
  private static Map<VarType, VarType> sideRename(StructClass calleeClass, List<String> fparams) {
    List<String> names = new ArrayList<>(calleeClass.getSignature().fparameters);
    for (String name : fparams) {
      if (!names.contains(name)) {
        names.add(name);
      }
    }
    Map<VarType, VarType> rename = new HashMap<>();
    for (String name : names) {
      rename.put(GenericType.parse("T" + name + ";"), GenericType.parse("T" + SIDE_PREFIX + name + ";"));
    }
    return rename;
  }

  /**
   * Alpha-renaming for one side of a unification: same-named type variables of two different
   * declarations are different variables, so each is renamed to a name no declaration can hold.
   */
  private static Map<VarType, VarType> renameTypeVariables(List<String> names) {
    Map<VarType, VarType> rename = new HashMap<>();
    for (String name : names) {
      rename.put(GenericType.parse("T" + name + ";"), GenericType.parse("T" + RENAME_PREFIX + name + ";"));
    }
    return rename;
  }

  /**
   * Solves a static call's type arguments from the method reference it alone passes. javac does
   * not use a method reference for applicability, so a call that gets no target type (a receiver
   * expression) infers the functional interface's variables to their bounds and rejects the
   * reference; the source had to pin them. Both the implementation method (the recorded
   * MethodHandle) and the functional interface's own Signature are in the class files, and their
   * declared shapes fix the variables: the interface method's instantiated parameters and result
   * are unified with the implementation's. A variable the implementation declares itself is not
   * nameable at the call site; it is written as the unbounded wildcard, the one type that stands
   * for every instantiation. Returns the values keyed as {@code T<name>;}, or null when the call
   * is not this shape, the reference is not the only argument, or any value is not nameable.
   */
  public static @Nullable Map<VarType, VarType> solveMethodReference(InvocationExprent call, List<String> fparams) {
    if (SOLVING.get()) {
      return null;
    }
    SOLVING.set(Boolean.TRUE);
    try {
      return solveMethodReferenceInner(call, fparams);
    }
    catch (RuntimeException e) {
      return null;
    }
    finally {
      SOLVING.set(Boolean.FALSE);
    }
  }

  private static @Nullable Map<VarType, VarType> solveMethodReferenceInner(InvocationExprent call, List<String> fparams) {
    if (call.getFunctype() == InvocationExprent.Type.INIT || call.getInvocationType() != InvocationExprent.InvocationType.STATIC
      || fparams.isEmpty() || !call.isReceiverPosition() || !call.isRecordedCallSite()) {
      return null;
    }
    StructMethod callee = call.getDesc();
    if (callee == null || callee.getSignature() == null) {
      return null;
    }
    List<VarType> declaredParams = callee.getSignature().parameterTypes;
    if (declaredParams.size() != 1 || !(declaredParams.get(0) instanceof GenericType samType)
      || call.getLstParameters().size() != 1
      || !(call.getLstParameters().get(0) instanceof NewExprent reference)
      || !reference.isMethodReference()) {
      return null;
    }
    ClassNode referenceNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(reference.getNewType().value);
    if (referenceNode == null || referenceNode.lambdaInformation == null
      || !referenceNode.lambdaInformation.is_method_reference) {
      return null;
    }
    // The functional interface's own declared method, and the implementation the MethodHandle
    // records. Both are looked up by the exact recorded descriptor, so an overload cannot be
    // mistaken for either.
    StructClass samClass = DecompilerContext.getStructContext().getClass(samType.value);
    if (samClass == null || samClass.getSignature() == null) {
      return null;
    }
    List<String> interfaceParams = samClass.getSignature().fparameters;
    List<VarType> interfaceArgs = samType.getArguments();
    if (interfaceParams.isEmpty() || interfaceParams.size() != interfaceArgs.size()) {
      return null;
    }
    // The recorded method descriptor is the instantiated functional method type, not the
    // interface's own erased one; the method is the interface's single abstract member of that
    // name and arity.
    int samArity = MethodDescriptor.parseDescriptor(referenceNode.lambdaInformation.method_descriptor).params.length;
    StructMethod samMethod = null;
    for (StructMethod candidate : samClass.getMethods()) {
      if (!referenceNode.lambdaInformation.method_name.equals(candidate.getName())
        || candidate.hasModifier(CodeConstants.ACC_STATIC)
        || !candidate.hasModifier(CodeConstants.ACC_ABSTRACT)
        || MethodDescriptor.parseDescriptor(candidate.getDescriptor()).params.length != samArity) {
        continue;
      }
      if (samMethod != null) {
        return null;
      }
      samMethod = candidate;
    }
    if (samMethod == null || samMethod.getSignature() == null
      || !samMethod.getSignature().typeParameters.isEmpty()) {
      return null;
    }
    StructClass content = DecompilerContext.getStructContext().getClass(referenceNode.lambdaInformation.content_class_name);
    if (content == null || (content.getSignature() != null && !content.getSignature().fparameters.isEmpty())) {
      // The implementation's own class type variables would leak into the witness; only a
      // non-generic declaring class leaves the solution nameable.
      return null;
    }
    StructMethod implementation = content.getMethodRecursive(referenceNode.lambdaInformation.content_method_name,
      referenceNode.lambdaInformation.content_method_descriptor);
    if (implementation == null || implementation.getSignature() == null
      || !implementation.hasModifier(CodeConstants.ACC_STATIC)
      || implementation.getSignature().typeParameters.isEmpty()) {
      // A reference to a non-generic method records its own instantiated type, so javac infers
      // the interface's variables from it; only the implementation's own type variables are
      // unnameable at the call site and force the source witness.
      return null;
    }

    Map<VarType, VarType> interfaceMap = new HashMap<>();
    for (int i = 0; i < interfaceParams.size(); i++) {
      VarType argument = interfaceArgs.get(i);
      if (argument == null) {
        return null;
      }
      interfaceMap.put(GenericType.parse("T" + interfaceParams.get(i) + ";"), argument);
    }
    GenericMethodDescriptor samSignature = samMethod.getSignature();
    GenericMethodDescriptor implSignature = implementation.getSignature();
    List<VarType> samParams = new ArrayList<>(samSignature.parameterTypes.size());
    for (VarType parameter : samSignature.parameterTypes) {
      VarType instantiated = parameter.remap(interfaceMap);
      if (instantiated == null) {
        return null;
      }
      samParams.add(instantiated);
    }
    VarType samReturn = samSignature.returnType.remap(interfaceMap);
    if (samReturn == null || samParams.size() != implSignature.parameterTypes.size()) {
      return null;
    }

    // A type variable the implementation declares itself is not nameable at the call site; its
    // name may collide with a variable of the caller, which would make the solution ambiguous.
    Map<VarType, List<VarType>> named = call.getNamedGenerics();
    for (String name : implSignature.typeParameters) {
      if (named.containsKey(GenericType.parse("T" + name + ";"))) {
        return null;
      }
    }
    // Tag the implementation's variables so names it shares with the interface side cannot be
    // mistaken for the same variable during unification.
    Map<VarType, VarType> rename = renameTypeVariables(implSignature.typeParameters);
    List<VarType> implParams = new ArrayList<>(implSignature.parameterTypes.size());
    for (VarType parameter : implSignature.parameterTypes) {
      implParams.add(parameter.remap(rename));
    }

    Unifier unifier = new Unifier();
    for (int i = 0; i < samParams.size(); i++) {
      if (!unifier.unify(samParams.get(i), implParams.get(i))) {
        return null;
      }
    }
    if (!unifier.unify(samReturn, implSignature.returnType.remap(rename))) {
      return null;
    }

    // The substituted interface signature must erase to the method the MethodHandle records:
    // this is the recorded functional shape, checked after every variable is solved.
    MethodDescriptor recorded = MethodDescriptor.parseDescriptor(referenceNode.lambdaInformation.content_method_descriptor);
    if (recorded.params.length != samParams.size()) {
      return null;
    }
    for (int i = 0; i < samParams.size(); i++) {
      VarType erased = eraseSolved(samParams.get(i), unifier);
      if (erased == null || !erased.equals(recorded.params[i])) {
        return null;
      }
    }
    VarType erasedReturn = eraseSolved(samReturn, unifier);
    if (erasedReturn == null || !erasedReturn.equals(recorded.ret)) {
      return null;
    }

    Map<VarType, VarType> solved = new HashMap<>();
    boolean[] wildcarded = new boolean[1];
    for (String name : fparams) {
      VarType variable = GenericType.parse("T" + name + ";");
      VarType value = wildcardUnnameable(unifier.substitute(variable), named, wildcarded);
      if (value == null || !isNameable(value, named)) {
        return null;
      }
      solved.put(variable, value);
    }
    if (!wildcarded[0]) {
      // No implementation variable survived into the witness: javac can infer these values, and
      // a source need not have pinned them.
      return null;
    }
    return solved;
  }

  /**
   * The erasure of a substituted signature type: a type variable that remains unsolved has no
   * bound the call could have written, and any type argument is dropped as the descriptor does.
   */
  private static @Nullable VarType eraseSolved(VarType type, Unifier unifier) {
    VarType resolved = unifier.resolve(type);
    if (resolved == null) {
      return null;
    }
    if (resolved.type == CodeType.GENVAR) {
      return null;
    }
    if (resolved.type == CodeType.OBJECT) {
      return new VarType(CodeType.OBJECT, resolved.arrayDim, resolved.value);
    }
    return resolved;
  }

  /**
   * Replaces every variable not nameable at the call site with the unbounded wildcard. A null
   * result means the whole type is such a variable, which a source cannot write as a witness.
   */
  private static @Nullable VarType wildcardUnnameable(VarType type, Map<VarType, List<VarType>> named, boolean[] wildcarded) {
    if (type == null) {
      return null;
    }
    if (type.type == CodeType.GENVAR) {
      if (isNameable(type, named)) {
        return type;
      }
      wildcarded[0] = true;
      return null;
    }
    if (!(type instanceof GenericType generic)) {
      return type;
    }
    List<VarType> arguments = generic.getArguments();
    if (arguments.isEmpty()) {
      return type;
    }
    List<VarType> substituted = new ArrayList<>(arguments.size());
    boolean changed = false;
    for (VarType argument : arguments) {
      if (argument == null) {
        substituted.add(null);
        continue;
      }
      VarType value = wildcardUnnameable(argument, named, wildcarded);
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
      // Variance markers are not structure: a wildcard's bound constrains the position, and
      // keeping the marker would bind an implementation variable to a type mentioning itself
      // (`? super B` against `B`), which no substitution can unfold.
      VarType left = strip(resolve(pattern));
      VarType right = strip(resolve(actual));
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

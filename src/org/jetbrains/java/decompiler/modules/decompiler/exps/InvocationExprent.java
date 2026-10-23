// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.ClasspathHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericFieldDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMain;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.struct.match.MatchNode;
import org.jetbrains.java.decompiler.util.*;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.collections.NullableConcurrentHashMap;

import java.io.IOException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class InvocationExprent extends Exprent {
  public enum InvocationType {
    SPECIAL, VIRTUAL, STATIC, INTERFACE, DYNAMIC, CONSTANT_DYNAMIC
  }

  public enum Type {
    GENERAL, INIT, CLINIT
  }

  private static final BitSet EMPTY_BIT_SET = new BitSet(0);

  private static final VarType JAVA_NIO_BUFFER = new VarType(CodeType.OBJECT, 0, "java/nio/Buffer");

  private static final String BUILDER_OWNER = "com/mojang/serialization/codecs/RecordCodecBuilder";

  private String name;
  private String classname;
  private boolean isStatic;
  private boolean canIgnoreBoxing = true;
  private Type functype = Type.GENERAL;
  private Exprent instance;
  private StructMethod desc = null;
  private MethodDescriptor descriptor;
  private String stringDescriptor;
  private String invokeDynamicClassSuffix;
  private InvocationType invocationType = InvocationType.VIRTUAL;
  private List<Exprent> lstParameters = new ArrayList<>();
  private LinkConstant bootstrapMethod;
  private List<PooledConstant> bootstrapArguments;
  private final List<VarType> genericArgs = new ArrayList<>();
  /** A witness this call prints that an unqualified name cannot carry: print the class too. */
  private boolean witnessQualifier = false;
  private VarType remappedInstType = null;
  /** The line the call's own token sits on, when the printer of a constructor knows it. */
  private int callerOpeningLine = -1;
  public boolean forceGenericQualfication = false;
  private final NullableConcurrentHashMap<VarType, VarType> genericsMap = new NullableConcurrentHashMap<>();
  private boolean isInvocationInstance = false;
  /** The invocation whose receiver is currently being typed; set only for the duration. */
  private static final ThreadLocal<InvocationExprent> OUTER_INVOCATION = new ThreadLocal<>();
  /**
   * The map invocation whose type argument an enclosing {@code Optional.orElse}/{@code orElseGet}
   * argument pins, and the recorded wildcard type that pins it. Set only while the receiver
   * subtree of such a call is being inferred or printed.
   */
  private static final ThreadLocal<InvocationExprent> OPTIONAL_MAP_DEMAND = new ThreadLocal<>();
  private static final ThreadLocal<VarType> OPTIONAL_MAP_DEMAND_TYPE = new ThreadLocal<>();
  private boolean isQualifier = false;
  private final BoxState boxing = new BoxState();
  private boolean isSyntheticNullCheck = false;
  private boolean wasLazyCondy = false;

  public InvocationExprent() {
    super(Exprent.Type.INVOCATION);
  }

  public InvocationExprent(int opcode,
                           LinkConstant cn,
                           LinkConstant bootstrapMethod,
                           List<PooledConstant> bootstrapArguments,
                           ListStack<? extends Exprent> stack,
                           BitSet bytecodeOffsets) {
    this();

    name = cn.elementname;
    classname = cn.classname;
    this.bootstrapMethod = bootstrapMethod;
    this.bootstrapArguments = bootstrapArguments;
    switch (opcode) {
      case CodeConstants.opc_invokestatic:
        invocationType = InvocationType.STATIC;
        break;
      case CodeConstants.opc_invokespecial:
        invocationType = InvocationType.SPECIAL;
        break;
      case CodeConstants.opc_invokevirtual:
        invocationType = InvocationType.VIRTUAL;
        break;
      case CodeConstants.opc_invokeinterface:
        invocationType = InvocationType.INTERFACE;
        break;
      case CodeConstants.opc_invokedynamic:
        invocationType = InvocationType.DYNAMIC;

        classname = bootstrapMethod.classname; // dummy class name
        invokeDynamicClassSuffix = "##Lambda_" + cn.index1 + "_" + cn.index2;
        break;
      case CodeConstants.opc_ldc:
      case CodeConstants.opc_ldc_w:
      case CodeConstants.opc_ldc2_w:
        invocationType = InvocationType.CONSTANT_DYNAMIC;
        classname = bootstrapMethod.classname; // dummy class name
        invokeDynamicClassSuffix = "##Condy_" + cn.index1 + "_" + cn.index2;
        break;
    }

    if (CodeConstants.INIT_NAME.equals(name)) {
      functype = Type.INIT;
    }
    else if (CodeConstants.CLINIT_NAME.equals(name)) {
      functype = Type.CLINIT;
    }

    stringDescriptor = cn.descriptor;
    if (invocationType == InvocationType.CONSTANT_DYNAMIC) {
      stringDescriptor = "()" + stringDescriptor;
    }
    descriptor = MethodDescriptor.parseDescriptor(stringDescriptor);

    for (VarType ignored : descriptor.params) {
      lstParameters.add(0, stack.pop());
    }

    if (opcode == CodeConstants.opc_invokedynamic || invocationType == InvocationType.CONSTANT_DYNAMIC) {
      int dynamicInvocationType = bootstrapMethod.index1;
      if (bootstrapArguments != null) {
        if (bootstrapArguments.size() > 1) { // FIXME: INVOKEDYNAMIC is used not only for lambdas
          PooledConstant link = bootstrapArguments.get(1);
          if (link instanceof LinkConstant) {
            dynamicInvocationType = ((LinkConstant)link).index1;
          }
        }
      }
      if (dynamicInvocationType == CodeConstants.CONSTANT_MethodHandle_REF_invokeStatic) {
        isStatic = true;
      }
      else {
        // FIXME: remove the first parameter completely from the list. It's the object type for a virtual lambda method.
        if (!lstParameters.isEmpty()) {
          instance = lstParameters.get(0);
        }
      }
    }
    else if (opcode == CodeConstants.opc_invokestatic) {
      isStatic = true;
    }
    else {
      instance = stack.pop();
    }

    addBytecodeOffsets(bytecodeOffsets);
  }

  protected InvocationExprent(InvocationExprent expr) {
    this();

    name = expr.getName();
    classname = expr.getClassname();
    isStatic = expr.isStatic();
    canIgnoreBoxing = expr.canIgnoreBoxing;
    functype = expr.getFunctype();
    instance = expr.getInstance();
    if (instance != null) {
      instance = instance.copy();
    }
    invocationType = expr.getInvocationType();
    invokeDynamicClassSuffix = expr.getInvokeDynamicClassSuffix();
    stringDescriptor = expr.getStringDescriptor();
    descriptor = expr.getDescriptor();
    lstParameters = new ArrayList<>(expr.getLstParameters());
    ExprProcessor.copyEntries(lstParameters);

    addBytecodeOffsets(expr.bytecode);
    bootstrapMethod = expr.getBootstrapMethod();
    bootstrapArguments = expr.getBootstrapArguments();
    isSyntheticNullCheck = expr.isSyntheticNullCheck();
    wasLazyCondy = expr.wasLazyCondy;

    if (invocationType == InvocationType.DYNAMIC && !isStatic && instance != null && !lstParameters.isEmpty()) {
      // method reference, instance and first param are expected to be the same var object
      instance = lstParameters.get(0);
    }
  }

  @Override
  public VarType getExprType() {
    return descriptor.ret;
  }

  /**
   * The return type as the method declares it, wildcards and type variables intact. Inference
   * substitutes the upper bound into this type, so it is the only witness that the declared type
   * was a wildcard instantiation the source had to cast away.
   */
  public VarType getDeclaredGenericReturnType() {
    if (desc == null) {
      StructClass cl = DecompilerContext.getStructContext().getClass(classname);
      desc = cl != null ? cl.getMethodRecursive(name, stringDescriptor) : null;
    }
    if (desc != null && desc.getSignature() != null && desc.getSignature().returnType != null) {
      return desc.getSignature().returnType;
    }
    return descriptor.ret;
  }


  @Override
  public VarType getInferredExprType(VarType upperBound) {
    if (desc == null) {
      StructClass cl = DecompilerContext.getStructContext().getClass(classname);
      desc = cl != null ? cl.getMethodRecursive(name, stringDescriptor) : null;
    }

    // Clear existing state
    genericArgs.clear();
    genericsMap.clear();
    this.remappedInstType = null;
    this.witnessQualifier = false;

    StructClass mthCls = DecompilerContext.getStructContext().getClass(classname);

    // In the case of `(Long)call() & 100L)`, the boxing call must exist.
    if (isUnboxingCall() && upperBound != null) {
      if (instance instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent)instance;
        if (func.getFuncType() == FunctionType.CAST) {
          VarType inferred = func.getLstOperands().get(0).getInferredExprType(upperBound);

          // In the case of `long l = (Long)call()` where `call()` is a generic, we can remove the cast.
          // Don't keep the cast in that case.
          VarType unboxed = VarType.UNBOXING_TYPES.get(inferred);
          if (unboxed == null || !unboxed.equals(upperBound)) {
            if (inferred.typeFamily == TypeFamily.OBJECT || inferred.isGeneric()) {
              boxing.keepCast = true;
            }
          }
        }
      }
    }

    if (desc != null && mthCls != null) {
      boolean isNew = functype == Type.INIT;
      boolean isGenNew = isNew && mthCls.getSignature() != null;
      if (desc.getSignature() != null || isGenNew) {
        Map<VarType, List<VarType>> named = getNamedGenerics();
        Map<VarType, List<VarType>> bounds = getGenericBounds(mthCls);

        List<String> fparams = isGenNew ? mthCls.getSignature().fparameters : desc.getSignature().typeParameters;
        VarType ret = isGenNew ? mthCls.getSignature().genericType : desc.getSignature().returnType;

        StructClass cls;
        Map<VarType, VarType> tempMap = new HashMap<>();
        Map<VarType, VarType> upperBoundsMap = new HashMap<>();
        Map<VarType, VarType> hierarchyMap = new HashMap<>();

        // The builder chain's type argument is not recorded anywhere; the declared signatures of
        // the builder calls do determine it, and javac's own resolution of the nested method
        // reference cannot reach it without the witness the source wrote.
        Map<VarType, VarType> builderInference = null;
        if (!isNew && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_BUILDER_INFERENCE)
          && BUILDER_OWNER.equals(classname) && ("create".equals(name) || "mapCodec".equals(name))) {
          builderInference = BuilderInference.solve(this, fparams);
          if (builderInference != null) {
            builderInference.forEach(genericsMap::putIfAbsent);
          }
        }

        if (!classname.equals(desc.getClassQualifiedName())) {
          Map<String, Map<VarType, VarType>> hierarchy = mthCls.getAllGenerics();
          if (hierarchy.containsKey(desc.getClassQualifiedName())) {
            hierarchyMap = hierarchy.get(desc.getClassQualifiedName());
            hierarchyMap.forEach((from, to) -> {
              if (to.type == CodeType.GENVAR) {
                if (bounds.containsKey(to) && !bounds.containsKey(from)) {
                  bounds.put(from, bounds.get(to));
                }
              }
              else if (!bounds.containsKey(from)) {
                genericsMap.put(from, to);
              }
            });
          }
        }

        // if possible, collect mappings from the ub
        // these mappings will be used to help 'fill in the blanks' when creating the ub types for the instance/params
        if (upperBound != null && !upperBound.equals(VarType.VARTYPE_OBJECT) && (upperBound.type != CodeType.GENVAR || named.containsKey(upperBound))) {
          VarType ub = upperBound; // keep original
          VarType r = ret;
          if (ub.type != CodeType.GENVAR && r.type != CodeType.GENVAR && !ub.value.equals(r.value)) {
            if (DecompilerContext.getStructContext().instanceOf(ub.value, r.value)) {
              ub = GenericType.getGenericSuperType(ub, r);
            }
            else {
              r = GenericType.getGenericSuperType(r, ub);
            }
          }

          // Don't capture as a real upper bound unless the upperbound is an object or a likewise generic.
          // FunctionExprent needs to inform its children about the type that it has, so it'll cause conflict here.
          if (r.type == CodeType.GENVAR && (upperBound.typeFamily == TypeFamily.OBJECT || upperBound.isGeneric())) {
            upperBoundsMap.put(r.resizeArrayDim(0), upperBound.resizeArrayDim(Math.max(upperBound.arrayDim - r.arrayDim, 0)));
          }
          else {
            gatherGenerics(ub, r, tempMap);
            tempMap.forEach((from, to) -> {
              if (!genericsMap.containsKey(from)) {
                if (to != null && (to.type != CodeType.GENVAR || named.containsKey(to))) {
                  boolean ok = true;

                  // Don't apply generic mappings if we're mapping to a distinct, but unknown generic type
                  // It's a bit hard to visualize. Consider this:
                  // public <S> Collection<S> test(Collection<? extends T> list) {
                  //   return (Collection<S>) Collections.unmodifiableCollection(list);
                  // }
                  // the result of "Collections.unmodifiableCollection" *should* be a collection of type T, not of type S.
                  // S is not part of the hierarchy, so we cannot capture it as the upper bound.
                  //
                  // A type variable the invoked method declares itself and takes as a whole parameter
                  // (of(T value)) is a fresh variable: the same name in the caller's scope is a
                  // different variable, so the collision below is spurious and the target's variable
                  // is what the call was instantiated with. javac then rejects that argument, and the
                  // source cast it. When the variable only sits nested inside a parameter type
                  // (Collection<? extends T>), the source suppressed the target typing with a cast on
                  // the call instead, so the mapping must stay rejected here.
                  boolean directParameter = fparams.contains(from.value) && desc.getSignature() != null
                    && desc.getSignature().parameterTypes.stream()
                      .anyMatch(p -> p instanceof GenericType g && g.type == CodeType.GENVAR
                        && g.getWildcard() == GenericType.WILDCARD_NO && g.value.equals(from.value));
                  if (!directParameter
                    && to.type == CodeType.GENVAR && named.containsKey(from) && bounds.containsKey(from) && bounds.get(from).contains(VarType.VARTYPE_OBJECT) && !bounds.containsKey(to)) {
                    if (!named.get(to).contains(from)) {
                      ok = false;
                    }
                  }

                  if (ok && isMappingInBounds(from, to, named, bounds, new HashSet<>())) {
                    upperBoundsMap.put(from, to);
                  }
                }
              }
            });
            tempMap.clear();
          }
        }

        // add all other known gen types to the UB map as a dummy value
        // this is important for the creation of instance/param UBs
        // leaving a type 'T' because we have no mapping for it is bad; it is taken as we expect the result to be 'T'
        // really though, we have no idea what 'T' is supposed to be and this is an attempt to make that clear
        fparams.stream().map(p -> "T" + p + ";").map(GenericType::parse).filter(t -> !upperBoundsMap.containsKey(t)).forEach(t -> upperBoundsMap.put(t, GenericType.DUMMY_VAR));
        if (mthCls.getSignature() != null) {
          mthCls.getSignature().fparameters.stream().map(p -> "T" + p + ";").map(GenericType::parse).filter(t -> !upperBoundsMap.containsKey(t)).forEach(t -> upperBoundsMap.put(t, GenericType.DUMMY_VAR));
        }

        VarType instType = null;

        // types gathered from the instance have the highest priority
        if (instance != null && !isNew) {
          instance.setInvocationInstance();

          VarType instUB = mthCls.getSignature() != null ? mthCls.getSignature().genericType.remap(upperBoundsMap) : upperBound;
          InvocationExprent priorOuter = OUTER_INVOCATION.get();
          InvocationExprent priorMapDemand = OPTIONAL_MAP_DEMAND.get();
          VarType priorMapDemandType = OPTIONAL_MAP_DEMAND_TYPE.get();
          VarType optionalDemand = optionalWildcardArgument();
          InvocationExprent optionalMap = optionalDemand == null ? null : optionalElementMap();
          OUTER_INVOCATION.set(this);
          if (optionalMap != null) {
            OPTIONAL_MAP_DEMAND.set(optionalMap);
            OPTIONAL_MAP_DEMAND_TYPE.set(optionalDemand);
          }
          try {
            // don't want the casted type
            if (instance instanceof FunctionExprent && ((FunctionExprent)instance).getFuncType() == FunctionType.CAST) {
              instType = ((FunctionExprent)instance).getLstOperands().get(0).getInferredExprType(instUB);
            }
            else {
              instType = instance.getInferredExprType(instUB);
            }
          }
          finally {
            OUTER_INVOCATION.set(priorOuter);
            OPTIONAL_MAP_DEMAND.set(priorMapDemand);
            OPTIONAL_MAP_DEMAND_TYPE.set(priorMapDemandType);
          }

          if (instType.type == CodeType.GENVAR && named.containsKey(instType)) {
            instType = named.get(instType).get(0);
          }

          if (instType.isGeneric() && instType.type != CodeType.GENVAR) {
            GenericType ginstance = (GenericType)instType;

            cls = DecompilerContext.getStructContext().getClass(instType.value);
            if (cls != null && cls.getSignature() != null) {
              cls.getSignature().genericType.mapGenVarsTo(ginstance, tempMap);
              tempMap.forEach((from, to) -> {
                if (!fparams.contains(from.value)) {
                  processGenericMapping(from, to, named, bounds);
                }
              });
              tempMap.clear();
            }
          }
        }

        // fix for this() & super()
        if (upperBound == null && isGenNew) {
          ClassNode currentCls = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);

          if (currentCls != null) {
            if (mthCls.equals(currentCls.classStruct)) {
              mthCls.getSignature().genericType.getAllGenericVars().forEach(var -> genericsMap.put(var, var));
            }
            else {
              Map<String, Map<VarType, VarType>> hierarchy = currentCls.classStruct.getAllGenerics();
              if (hierarchy.containsKey(mthCls.qualifiedName)) {
                hierarchy.get(mthCls.qualifiedName).forEach(genericsMap::put);
              }
            }
          }
        }

        // Type variables whose value comes from the target type alone; javac cannot recover
        // them from the arguments, so a context that withholds the target needs the witness.
        Map<VarType, VarType> targetSeeded = new HashMap<>();
        if (!isInvocationInstance) {
          upperBoundsMap.forEach((k, v) -> {
            if (fparams.contains(k.value) && !GenericType.DUMMY_VAR.equals(v) && !genericsMap.containsKey(k)) {
              genericsMap.put(k, v);
              targetSeeded.put(k, v);
            }
          });
        }

        Set<VarType> paramGenerics = new HashSet<>();
        if (!lstParameters.isEmpty() && desc.getSignature() != null) {
          List<VarVersionPair> mask = null;
          int start = 0;
          ClassNode newNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
          if (newNode != null) {
            if (isNew) {
              mask = ExprUtil.getSyntheticParametersMask(newNode, stringDescriptor, lstParameters.size());
              start = newNode.classStruct.hasModifier(CodeConstants.ACC_ENUM) ? 2 : 0;
            } else if (!newNode.enclosingClasses.isEmpty()) {
              start = (newNode.access & CodeConstants.ACC_STATIC) == 0 ? 1 : 0;
            }
          }
          
          Set<VarType> commonGenerics = new HashSet<>();
          ClassNode currentNode = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
          MethodWrapper methodWrapper = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
          if (methodWrapper != null) {
            StructMethod currentMethod = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER).methodStruct;
            if (newNode != null && currentNode != null && !desc.hasModifier(CodeConstants.ACC_STATIC) && !currentMethod.hasModifier(CodeConstants.ACC_STATIC)) {
              List<ClassNode> parents = new ArrayList<>();
              ClassNode search = currentNode;
              while (search != null) {
                parents.add(search);
                search = (search.access & CodeConstants.ACC_STATIC) == 0 ? search.parent : null;
              }
              
              search = newNode;
              while (search != null) {
                if (parents.contains(search) && search.classStruct.getSignature() != null) {
                  commonGenerics.addAll(search.classStruct.getSignature().fparameters
                      .stream()
                      .map(generic -> GenericType.parse("T" + generic + ";"))
                      .collect(Collectors.toList()));
                }
                search = (search.access & CodeConstants.ACC_STATIC) == 0 ? search.parent : null;
              }
            }
          }

          int j = 0;
          for (int i = start; i < lstParameters.size(); ++i) {
            if ((mask == null || mask.get(i) == null)) {
              // FIXME: why can this happen?
              //   See: jdk ReduceOps
              if (desc.getSignature().parameterTypes.size() <= j) {
                continue;
              }

              VarType paramType = desc.getSignature().parameterTypes.get(j++);
              if (paramType.isGeneric()) {

                Exprent parameter = lstParameters.get(i);
                Set<VarType> excluded = new HashSet<>();
                if (parameter.type == Exprent.Type.NEW) {
                  NewExprent newExprent = (NewExprent) parameter;
                  if (newExprent.isLambda()) {
                    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newExprent.getNewType().value);
                    int potentialMethodCount = Integer.MAX_VALUE;
                    if (node.lambdaInformation.is_method_reference) {
                      StructClass content = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);

                      if (content != null) {
                        StructClass currentCls = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
                        potentialMethodCount = (int) content.getMethods().stream()
                          .filter((method) -> canAccess(currentCls, method))
                          .map(StructMethod::getName)
                          .filter(node.lambdaInformation.content_method_name::equals)
                          .count();
                      }
                    }
                    if (potentialMethodCount > 1) {
                      StructClass base = DecompilerContext.getStructContext().getClass(newExprent.getExprType().value);
                      if (base != null) {
                        StructMethod found = null;
                        for (StructMethod method : base.getMethods()) {
                          if (!method.hasModifier(CodeConstants.ACC_STATIC) && method.getInstructionSequence() == null) {
                            found = method;
                            break;
                          }
                        }
                        if (found != null) {
                          Map<VarType, VarType> genvars = new HashMap<>();
                          if (base.getSignature() != null && found.getSignature() != null) {
                            base.getSignature().genericType.mapGenVarsTo((GenericType) paramType, genvars);
                            excluded.addAll(found.getSignature().parameterTypes.stream()
                              .filter(VarType::isGeneric)
                              .map(GenericType.class::cast)
                              .map(GenericType::getAllGenericVars)
                              .flatMap(List::stream)
                              .map(genvars::get)
                              .filter(Objects::nonNull)
                              .filter(VarType::isGeneric)
                              .map(GenericType.class::cast)
                              .map(GenericType::getAllGenericVars)
                              .flatMap(List::stream)
                              .collect(Collectors.toList()));
                          }
                        }
                      }
                    }
                  }
                }

                Map<VarType, VarType> combined = new HashMap<>(genericsMap);
                upperBoundsMap.forEach((k, v) -> {
                  if (!combined.containsKey(k))
                    combined.put(k, v);
                });
                VarType paramUB = paramType.remap(hierarchyMap).remap(combined);

                VarType argtype;
                if (parameter instanceof FunctionExprent && ((FunctionExprent)parameter).getFuncType() == FunctionType.CAST) {
                  argtype = ((FunctionExprent)parameter).getLstOperands().get(0).getInferredExprType(paramUB);
                }
                else {
                  argtype = parameter.getInferredExprType(paramUB);
                }

                // If the instance type is a wildcard and the param type can give us more information about the instance
                // type, then capture that type and cast in toJava.
                // For example:
                // Type<T extends Number> contains a method "void accept(T t)". You have a Type<?> inst.
                // You want to call inst.accept(returnLong()). This would fail, and will need a cast instead.
                // By changing to ((Type<Long>)inst).accept(returnLong()), it will work.
                if (paramUB == null && argtype != null && instType instanceof GenericType) {
                  if (combined.containsKey(paramType) && combined.get(paramType) == null && !VarType.VARTYPE_NULL.equals(argtype)) {
                    // Remap the type from the wildcard (null) to the actual type here.
                    combined.put(paramType, argtype);

                    // We need the base type, and not the raw instance's type.
                    // Taking from the prior example, Type<T> instead of Type<?>.
                    // This will let us remap with our new argtype in a simple fashion.
                    GenericType baseType = ((GenericType) instType).findBaseType();
                    if (baseType != null) {
                      this.remappedInstType = baseType.remap(hierarchyMap).remap(combined);
                    }
                  }
                }

                StructClass paramCls = DecompilerContext.getStructContext().getClass(paramType.value);
                cls = argtype.type != CodeType.GENVAR ? DecompilerContext.getStructContext().getClass(argtype.value) : null;

                if (cls != null && paramCls != null) {
                  if (paramType.isGeneric() && !paramType.value.equals(argtype.value)) {
                    argtype = GenericType.getGenericSuperType(argtype, paramType);
                  }

                  if (paramType.isGeneric() && argtype.isGeneric()) {
                    GenericType genParamType = (GenericType)paramType;
                    GenericType genArgType = (GenericType)argtype;

                    genParamType.mapGenVarsTo(genArgType, tempMap);
                    GenericType.cleanLoweredGenericTypes(tempMap, genParamType, genArgType, commonGenerics);
                    tempMap.forEach((from, to) -> {
                      if (!excluded.contains(from)) {
                        paramGenerics.add(from);
                      }
                      // If we didn't process the generic mapping here, try to see if this and the old type are both raw types
                      // If so, we should forcibly stuff the mapping in there to ensure it isn't missed.
                      // Say, for example in this case, B extends A, and where invoc is "<T> T invoc(SomeType<T> t, ...);
                      // So, then, if you have:
                      // return (B)invoc(#SomeType<A>#, ...);
                      // The known type of invoc *must* be A, and not B.
                      // Without doing this, we may lose some extra information.
                      // TODO: generalize this! Seems there's cases where generalizing can cause breakages currently
                      if (!processGenericMapping(from, to, named, bounds)) {
                        VarType current = genericsMap.get(from);
                        if (to != null && current != null && !current.isGeneric() && !to.isGeneric()) {
                          putGenericMapping(from, to, named, bounds);
                        }
                      }
                    });
                    tempMap.clear();
                  }
                }
                else if (paramType.type == CodeType.GENVAR && !paramType.equals(argtype) && argtype.arrayDim >= paramType.arrayDim) {
                  if (paramType.arrayDim > 0) {
                    argtype = argtype.resizeArrayDim(argtype.arrayDim - paramType.arrayDim);
                    paramType = paramType.resizeArrayDim(0);
                  }
                  if (!excluded.contains(paramType)) {
                    paramGenerics.add(paramType);
                  }
                  processGenericMapping(paramType, argtype, named, bounds);
                }
              }
            }
          }
        }

        upperBoundsMap.forEach((k, v) -> {
          if (fparams.contains(k.value) && !GenericType.DUMMY_VAR.equals(v)) {
            VarType current = genericsMap.get(k);
            // Don't replace raw types. See comment above about losing extra information. [TestGenericCasts]
            if (current != null && v != null && !current.isGeneric() && !v.isGeneric() && !DecompilerContext.getStructContext().instanceOf(current.value, v.value)) {
              return;
            }
            processGenericMapping(k, v, named, bounds);
          }
        });

        if (!genericsMap.isEmpty()) {
          VarType newRet = ret.remap(hierarchyMap);

          boolean skipArgs = true;
          if (!fparams.isEmpty() && newRet.isGeneric()) {
            for (VarType genVar : ((GenericType)newRet).getAllGenericVars()) {
              if (fparams.contains(genVar.value)) {
                skipArgs = false;
                break;
              }
            }
          }

          newRet = newRet.remap(genericsMap);
          if (newRet == null && bounds.get(ret) != null && bounds.get(ret).size() > 0) {
            newRet = bounds.get(ret).get(0).remap(genericsMap);
          }

          if (!skipArgs && (!isNew || isGenNew)) {
            boolean missing = paramGenerics.isEmpty();

            if (!missing) {
              for (String param : fparams) {
                if (!paramGenerics.contains(GenericType.parse("T" + param + ";"))) {
                  missing = true;
                  break;
                }
              }
            }

            boolean suppress = (!missing || !isInvocationInstance) && newRet != null &&
            (upperBound == null || !newRet.isGeneric() || DecompilerContext.getStructContext().instanceOf(newRet.value, upperBound.value));

            if (this.forceGenericQualfication) {
              suppress = false;
            }

            boolean receiverDemand = suppress && !isNew
              && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
              && receiverTargetDemand(fparams, upperBoundsMap, bounds);

            // A type variable no recorded parameter mentions can only default to its declared
            // bound where javac has no target, and the recorded expected type rejects that
            // instantiation, so the source pinned it. Only the witness whose erasure reproduces
            // the pool's descriptor is used.
            boolean returnOnlyDemand = suppress && !isNew
              && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
              && returnOnlyTypeVariableDemand(fparams, ret, bounds, upperBound, isNew);

            if (!suppress || DecompilerContext.getOption(IFernflowerPreferences.EXPLICIT_GENERIC_ARGUMENTS)
              || receiverDemand || returnOnlyDemand) {
              getGenericArgs(fparams, genericsMap, genericArgs);
              // The printer's own return type does not even fit the class of the expected type,
              // so no substitution of its type arguments can make the call assignable: the value
              // it inferred for them came from the target, not from the arguments, and javac will
              // solve the same constraint itself. Printing it would pin a guess (List.<T>of()
              // where the target is a HolderSet.Named<T>).
              boolean misfit = !suppress && !isNew && newRet != null && newRet.isGeneric() && upperBound != null
                && !DecompilerContext.getStructContext().instanceOf(newRet.value, upperBound.value);
              if (misfit && !DecompilerContext.getOption(IFernflowerPreferences.EXPLICIT_GENERIC_ARGUMENTS)) {
                genericArgs.clear();
              }
              // A variable a declared parameter carries bare is fixed by that argument's recorded
              // type, which every class file writes in full. A witness the printer could only
              // render as a bare generic class for it is its own inference losing type arguments,
              // and printing it would pin javac to a raw type the record never has; the call is
              // left unparameterised and javac infers the variable from the argument again.
              boolean rawWitness = !misfit && !receiverDemand && !returnOnlyDemand && !isNew && dropsRawParameterWitness(fparams);
              if (rawWitness) {
                genericArgs.clear();
              }
              if (!rawWitness && genericArgs.isEmpty() && !isNew
                && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)) {
                // The printer's inference has no value for some type variable; an argument's
                // recorded metafactory type may still prove what the source passed.
                tryDemandWitness(fparams, bounds);
              }
            }
            else if (DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
              && receiverRecordedValueDemand(fparams, ret, bounds)) {
              // The printer has no value for some type variable of a call in receiver position.
              // The outer call's functional argument records the value it must return, and the
              // receiver's type argument is invariant in it: the recorded type pins the variable.
            }
            else if (DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_GENVAR_ARGS)
              && inPoly() && hasGenvarArgs(fparams, genericsMap)) {
              // A call inferred to an enclosing method's or class's type variable can need the
              // witness in source: javac does not propagate the target type into every poly
              // expression (a conditional arm, a diamond argument), and then cannot infer it.
              getGenericArgs(fparams, genericsMap, genericArgs);
            }
            else if (DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_ARG_WITNESS)
              && inArgument() && hasWildcardArgs(fparams, genericsMap)) {
              // A call whose inferred arguments carry wildcards can be beyond javac's inference
              // from an argument position; the original wrote the witnesses it inferred itself.
              getGenericArgs(fparams, genericsMap, genericArgs);
            }
            else if (DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
              && constructorDelegationDemand(fparams, ret, targetSeeded, isNew)) {
              // this(...)/super(...) overload resolution cannot hand the target type to the
              // argument, so a type variable the arguments leave to the target must be pinned
              // in source; the constructor's recorded parameter type is what demanded it.
              getGenericArgs(fparams, genericsMap, genericArgs);
            }
            else if (!isNew && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
              && tryDemandWitness(fparams, bounds)) {
              // A functional argument's recorded instantiated type is wider than the method it
              // names, so the source constrained the call's type arguments explicitly. The witness
              // is printed only when its erasure reproduces the call the target actually recorded.
            }
            else if (isGenNew) {
              genericArgs.add(GenericType.DUMMY_VAR);
            }
          }

          // The map whose element type feeds an enclosing Optional.orElse/orElseGet argument of
          // recorded wildcard type: every read of such a variable captures the wildcard afresh,
          // so javac cannot infer this call's variable from the lambda to the argument's type.
          // The source pinned it to the recorded declaration, which is the only nameable witness.
          if (OPTIONAL_MAP_DEMAND.get() == this
            && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
            && optionalMapWitness(OPTIONAL_MAP_DEMAND_TYPE.get(), fparams, bounds)) {
            genericArgs.clear();
            genericArgs.add(OPTIONAL_MAP_DEMAND_TYPE.get());
          }

          // The solved builder argument is printed even where the printer's own inference left
          // nothing: every type variable it names is in scope and every constraint holds.
          if (builderInference != null && !builderInference.isEmpty()) {
            List<VarType> solved = new ArrayList<>(fparams.size());
            for (String param : fparams) {
              VarType value = builderInference.get(GenericType.parse("T" + param + ";"));
              if (value == null) {
                solved.clear();
                break;
              }
              solved.add(value);
            }
            if (!solved.isEmpty()) {
              genericArgs.clear();
              genericArgs.addAll(solved);
            }
          }

          if (newRet != ret && newRet != null && !(newRet.isGeneric() && ((GenericType)newRet).hasUnknownGenericType(named.keySet()))) {
            return newRet;
          }
        }

        if (ret.isGeneric() && ((GenericType)ret).getAllGenericVars().isEmpty()) {
          return ret;
        }
      }
    }

    return getExprType();
  }


  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    if (instance != null) {
      result.addExprLowerBound(instance, VarType.findFamilyBottom(instance.getExprType().typeFamily));
      result.addExprUpperBound(instance, instance.getExprType());
    }

    for (int i = 0; i < lstParameters.size(); i++) {
      Exprent parameter = lstParameters.get(i);

      VarType leftType = descriptor.params[i];

      result.addExprLowerBound(parameter, VarType.findFamilyBottom(leftType.typeFamily));
      result.addExprUpperBound(parameter, leftType);
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    if (instance != null) {
      lst.add(instance);
    }
    lst.addAll(lstParameters);
    return lst;
  }


  @Override
  public Exprent copy() {
    return new InvocationExprent(this);
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    if (wasLazyCondy) {
      buf.append("/* $VF: constant dynamic replaced with non-lazy method call */ ");
    }

    String super_qualifier = null;
    boolean isInstanceThis = false;

    if (instance instanceof InvocationExprent) {
      ((InvocationExprent) instance).markUsingBoxingResult();
    }

    boolean pushedCallChainGroup = false;

    if (isStatic || invocationType == InvocationType.DYNAMIC || invocationType == InvocationType.CONSTANT_DYNAMIC) {
      if (isBoxingCall() && canIgnoreBoxing && !boxing.forceBoxing) {
        // process general "boxing" calls, e.g. 'Object[] data = { true }' or 'Byte b = 123'
        // here 'byte' and 'short' values do not need an explicit narrowing type cast
        ExprProcessor.getCastedExprent(lstParameters.get(0), descriptor.params[0], buf, indent, ExprProcessor.NullCastType.DONT_CAST, false, true, false);
        buf.addBytecodeMapping(bytecode);
        return buf;
      }

      if (invocationType == InvocationType.CONSTANT_DYNAMIC) {
        buf.append('(').appendCastTypeName(descriptor.ret).append(')');
      }

      ClassNode node = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
      if (node == null || !classname.equals(node.classStruct.qualifiedName)
        || (witnessQualifier && !genericArgs.isEmpty())) {
        // An unqualified call has no place for a witness: `.m()` is not valid Java.
        buf.appendAllClasses(DecompilerContext.getImportCollector().getShortNameInClassContext(ExprProcessor.buildJavaClassName(classname)), classname);
      }
    }
    else {

      if (instance instanceof VarExprent) {
        VarExprent instVar = (VarExprent)instance;
        VarVersionPair varPair = new VarVersionPair(instVar);

        VarProcessor varProc = instVar.getProcessor();
        if (varProc == null) {
          MethodWrapper currentMethod = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
          if (currentMethod != null) {
            varProc = currentMethod.varproc;
          }
        }

        String this_classname = null;
        if (varProc != null) {
          this_classname = varProc.getThisVars().get(varPair);
        }

        if (this_classname != null) {
          isInstanceThis = true;

          if (invocationType == InvocationType.SPECIAL) {
            if (!classname.equals(this_classname)) { // TODO: direct comparison to the super class?
              StructClass cl = DecompilerContext.getStructContext().getClass(classname);
              boolean isInterface = cl != null && cl.hasModifier(CodeConstants.ACC_INTERFACE);
              super_qualifier = !isInterface ? this_classname : classname;
            }
          }
        }
      }

      // Signature polymorphic methods returning Object require a cast to the return type in the descriptor
      if (CodeConstants.isReturnPolymorphic(classname, name) && !descriptor.ret.equals(VarType.VARTYPE_VOID)) {
        buf.append('(').appendCastTypeName(descriptor.ret).append(')');
      }

      if (functype == Type.GENERAL) {
        if (super_qualifier != null) {
          TextUtil.writeQualifiedSuper(buf, super_qualifier);
        }
        else if (instance != null) {
          StructClass cl = DecompilerContext.getStructContext().getClass(classname);

          VarType leftType = new VarType(CodeType.OBJECT, 0, classname);
          if (!genericsMap.isEmpty() && cl != null && cl.getSignature() != null) {
            VarType _new = cl.getSignature().genericType.remap(genericsMap);
            if (_new != cl.getSignature().genericType) {
              leftType = _new;
            }
          }

          instance.setInvocationInstance();
          InvocationExprent priorOuter = OUTER_INVOCATION.get();
          InvocationExprent priorMapDemand = OPTIONAL_MAP_DEMAND.get();
          VarType priorMapDemandType = OPTIONAL_MAP_DEMAND_TYPE.get();
          VarType optionalDemand = optionalWildcardArgument();
          InvocationExprent optionalMap = optionalDemand == null ? null : optionalElementMap();
          OUTER_INVOCATION.set(this);
          if (optionalMap != null) {
            OPTIONAL_MAP_DEMAND.set(optionalMap);
            OPTIONAL_MAP_DEMAND_TYPE.set(optionalDemand);
          }
          VarType rightType;
          try {
            rightType = instance.getInferredExprType(leftType);
          }
          finally {
            OUTER_INVOCATION.set(priorOuter);
            OPTIONAL_MAP_DEMAND.set(priorMapDemand);
            OPTIONAL_MAP_DEMAND_TYPE.set(priorMapDemandType);
          }

          if (isUnboxingCall() && !boxing.forceUnboxing) {
            // we don't print the unboxing call - no need to bother with the instance wrapping / casting
            buf.addBytecodeMapping(bytecode);
            if (instance instanceof FunctionExprent) {
              FunctionExprent func = (FunctionExprent)instance;
              if (func.getFuncType() == FunctionType.CAST && func.getLstOperands().get(1) instanceof ConstExprent && !boxing.keepCast) {
                ConstExprent constexpr = (ConstExprent)func.getLstOperands().get(1);
                boolean skipCast = false;

                Exprent firstParam = func.getLstOperands().get(0);
                if (firstParam instanceof VarExprent || firstParam instanceof FieldExprent) {
                  VarType inferred = firstParam.getInferredExprType(leftType);
                  skipCast = (inferred.type != CodeType.OBJECT && inferred.type != CodeType.GENVAR) ||
                    DecompilerContext.getStructContext().instanceOf(inferred.value, this.classname);
                } else if (this.classname.equals(constexpr.getConstType().value)) {
                  skipCast = true;
                }

                if (skipCast) {
                  buf.append(firstParam.toJava(indent));
                  return buf;
                }
              }
            }

            buf.append(instance.toJava(indent));
            return buf;
          }

          instance.setIsQualifier();

          if (!isQualifier) {
            buf.pushNewlineGroup(indent, 1);
            pushedCallChainGroup = true;
          }
          TextBuffer res;
          VarType printedDemand = optionalWildcardArgument();
          InvocationExprent printedMap = printedDemand == null ? null : optionalElementMap();
          InvocationExprent priorPrintedMap = OPTIONAL_MAP_DEMAND.get();
          VarType priorPrintedType = OPTIONAL_MAP_DEMAND_TYPE.get();
          if (printedMap != null) {
            OPTIONAL_MAP_DEMAND.set(printedMap);
            OPTIONAL_MAP_DEMAND_TYPE.set(printedDemand);
          }
          try {
            // The receiver subtree is inferred again while it prints, so the demand must be
            // visible for the whole print, not just for the type computation above.
            res = instance.toJava(indent);
          }
          finally {
            OPTIONAL_MAP_DEMAND.set(priorPrintedMap);
            OPTIONAL_MAP_DEMAND_TYPE.set(priorPrintedType);
          }

          ClassNode instNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
          // Don't cast to anonymous classes, since they by definition can't have a name
          // TODO: better fix may be to change equals to isSuperSet? all anonymous classes are superset of Object
          if (wildcardCapturedParameter(cl, rightType) >= 0) {
            // The value cannot be passed to the captured parameter, so the source erased the
            // receiver's type; the erased cast adds no instruction and keeps the pool's descriptor.
            appendInstCast(buf, new VarType(CodeType.OBJECT, 0, classname), res);
          } else if (rightType.equals(VarType.VARTYPE_OBJECT) && !leftType.equals(rightType) && (instNode != null && instNode.type != ClassNode.Type.ANONYMOUS)) {
            appendInstCast(buf, leftType, res);
          } else if (remappedInstType != null) {
            // If we have a remap inst type, do a cast
            appendInstCast(buf, remappedInstType, res);
          } else if (instance.getPrecedence() > getPrecedence() && !canSkipParenEnclose(instance)) {
            buf.append("(").append(res).append(")");
          }
          //Java 9+ adds some overrides to java/nio/Buffer's subclasses that alter the return types.
          //This isn't properly handled by the compiler. So explicit casts are needed to retain J8 compatibility.
          else if (JAVA_NIO_BUFFER.equals(descriptor.ret) && !JAVA_NIO_BUFFER.equals(rightType)
              && DecompilerContext.getStructContext().instanceOf(rightType.value, JAVA_NIO_BUFFER.value)) {
              buf.append("((").appendCastTypeName(JAVA_NIO_BUFFER).append(")").append(res).append(")");
          }
          else {
            buf.append(res);
          }
          if (instance.allowNewlineAfterQualifier()) {
            buf.appendPossibleNewline();
          }
        }
      }
    }

    switch (functype) {
      case GENERAL:
        if (buf.contentEquals(VarExprent.VAR_NAMELESS_ENCLOSURE)) {
          buf.setLength(0);
        }

        if (buf.length() > 0) {
          // A chain link whose invoke the original put on a later line than the receiver's last
          // instruction starts a line of its own. Inside an argument list javac attributes the
          // invoke to the first argument's line, so the entry proves nothing about the dot there.
          if (instance != null && !insideOwnArgumentList() && RoundTrip.newlineBetween(instance, this)) {
            buf.appendLineSeparator().appendIndent(indent);
          }
          buf.append(".");
          // Adds generic arguments to the invocation, so .m() becomes .<T>m()
          this.appendParameters(buf, witnessContradictsRecordedMethodReference() ? Collections.emptyList() : genericArgs);
        }

        buf.addBytecodeMapping(bytecode);

        String validName = ClassWriter.toValidJavaIdentifier(name);

        if (invocationType == InvocationType.DYNAMIC || invocationType == InvocationType.CONSTANT_DYNAMIC) {
          if (bootstrapMethod == null) {
            buf.append("<").appendMethod(validName, false, classname, name, descriptor);
            if (!validName.equals(name)) {
              buf.append("/* $VF was: ").append(name).append(" */");
            }

            if (invocationType == InvocationType.DYNAMIC) {
              buf.append(">invokedynamic");
            } else {
              buf.append(">ldc");
            }
          } else {
            buf.append(bootstrapMethod.elementname);
            buf.append("<\"");
            buf.appendMethod(validName, false, classname, name, descriptor);

            if (!validName.equals(name)) {
              buf.append("/* $VF was: ").append(name).append(" */");
            }

            buf.append('"');
            for (PooledConstant arg : bootstrapArguments) {
              buf.append(',');
              appendBootstrapArgument(buf, arg);
            }
            buf.append('>');
          }
        } else {
          buf.appendMethod(validName, false, classname, name, descriptor);
          if (!validName.equals(name)) {
            buf.append("/* $VF was: ").append(name).append(" */");
          }
        }

        buf.append("(");
        break;

      case CLINIT:
        throw new RuntimeException("Explicit invocation of " + CodeConstants.CLINIT_NAME);

      case INIT:
        buf.addBytecodeMapping(bytecode);
        if (super_qualifier != null) {
          buf.append("super(");
        }
        else if (isInstanceThis) {
          buf.append("this(");
        }
        else if (instance != null) {
          String s = ".";
          if (DecompilerContext.getOption(IFernflowerPreferences.DECOMPILER_COMMENTS)) {
            s += "/* $VF: Unable to resugar constructor */";
          }
          s += "<init>(";

          buf.append(instance.toJava(indent)).append(s);
        }
        else {
          throw new RuntimeException("Unrecognized invocation of " + CodeConstants.INIT_NAME);
        }
    }

    boolean delegation = functype == Type.INIT && (super_qualifier != null || isInstanceThis);
    if (delegation) {
      enterConstructorDelegation();
    }
    try {
      buf.append(appendParamList(indent)).append(')');
    } finally {
      if (delegation) {
        exitConstructorDelegation();
      }
    }
    if (pushedCallChainGroup) {
      buf.popNewlineGroup();
    }
    return buf;
  }

  private void appendInstCast(TextBuffer buf, VarType leftType, TextBuffer res) {
    buf.append("((").appendCastTypeName(leftType).append(")");

    if (instance.getPrecedence() >= FunctionType.CAST.precedence) {
      res.encloseWithParens();
    }
    buf.append(res).append(")");
  }

  /**
   * The position of an argument whose declared parameter is a type variable of the receiver's
   * class, instantiated to a wildcard with no lower bound. javac captures such a wildcard before
   * checking the call, and no expression type is a subtype of the capture, so the call the
   * printer would write cannot compile; the class file's signatures (the class's type parameters,
   * the receiver's recorded instantiation and the method's own signature) prove the source had to
   * erase the receiver's type, and a raw cast is exactly that erasure. The argument's own
   * recorded type must not be the wildcard itself: a value read out of the same instantiation has
   * the capture's type and is accepted. Only a receiver whose type is a recorded declaration (a
   * variable or a field) is evidence: the printer's own inference of a call can lower arguments to
   * wildcards it invented, and a receiver the printer already casts to a recorded type is settled.
   */
  private int wildcardCapturedParameter(StructClass cl, VarType receiverType) {
    if (cl == null || cl.getSignature() == null || desc == null || desc.getSignature() == null
      || remappedInstType != null
      || !(instance instanceof VarExprent || instance instanceof FieldExprent)) {
      return -1;
    }
    GenericClassDescriptor classSignature = cl.getSignature();
    if (classSignature.fparameters.isEmpty() || !(receiverType instanceof GenericType receiver)
      || receiver.type != CodeType.OBJECT) {
      return -1;
    }
    List<VarType> arguments = receiver.getArguments();
    if (arguments.size() != classSignature.fparameters.size()) {
      return -1;
    }
    List<VarType> parameterTypes = desc.getSignature().parameterTypes;
    int count = Math.min(parameterTypes.size(), lstParameters.size());
    for (int i = 0; i < count; i++) {
      VarType parameter = parameterTypes.get(i);
      if (parameter == null) {
        continue;
      }
      int index = -1;
      boolean nested = false;
      if (parameter.type == CodeType.GENVAR && parameter.arrayDim == 0) {
        index = classSignature.fparameters.indexOf(parameter.value);
      }
      else if (parameter instanceof GenericType parameterized
        && parameterized.getWildcard() == GenericType.WILDCARD_NO
        && parameterized.getArguments().size() == 1) {
        // A parameter built from the class variable (EntityType<C>) is invariant in it: a value
        // recorded as EntityType<T> for any other argument is not convertible to EntityType<CAP>
        // either, and the same erasure argument applies. A wildcard-wrapped variable
        // (Comparator<? super E>) is a contravariant position that accepts such values, so only
        // a plain, unwrapped argument proves the call cannot compile.
        VarType nestedArgument = parameterized.getArguments().get(0);
        if (nestedArgument != null && nestedArgument.type == CodeType.GENVAR && nestedArgument.arrayDim == 0
          && (!(nestedArgument instanceof GenericType wrapped)
          || wrapped.getWildcard() == GenericType.WILDCARD_NO)) {
          index = classSignature.fparameters.indexOf(nestedArgument.value);
          nested = index >= 0;
        }
      }
      if (index < 0) {
        continue;
      }
      VarType argument = arguments.get(index);
      boolean upperBounded = argument == null
        || (argument instanceof GenericType generic && generic.getWildcard() == GenericType.WILDCARD_EXTENDS);
      if (!upperBounded) {
        continue;
      }
      Exprent value = lstParameters.get(i);
      if (value instanceof ConstExprent constant && constant.getConstType() == VarType.VARTYPE_NULL) {
        continue;
      }
      VarType valueType = value.getExprType();
      if (valueType instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      if (nested) {
        // The value must be the same generic class with an argument of its own: a type from the
        // same wildcard instantiation reads as the capture and is accepted. Only a declaration
        // records that argument (LocalVariableTypeTable or the field's Signature).
        if (!(value instanceof VarExprent || value instanceof FieldExprent)) {
          continue;
        }
        VarType recordedType = value.getInferredExprType(valueType);
        if (!(recordedType instanceof GenericType recorded)
          || !recorded.value.equals(((GenericType) parameter).value)
          || recorded.getArguments().size() != 1) {
          continue;
        }
        VarType recordedArgument = recorded.getArguments().get(0);
        if (recordedArgument == null
          || (recordedArgument instanceof GenericType recordedGeneric
          && recordedGeneric.getWildcard() != GenericType.WILDCARD_NO)) {
          continue;
        }
      }
      return i;
    }
    return -1;
  }

  private boolean canSkipParenEnclose(Exprent instance) {
    if (!(instance instanceof NewExprent)) {
      return false;
    }

    NewExprent newExpr = (NewExprent) instance;

    if (!newExpr.isAnonymous() && !newExpr.isLambda() && !newExpr.isMethodReference()) {
      return this.functype == Type.GENERAL;
    }

    return false;
  }

  private static void appendBootstrapArgument(TextBuffer buf, PooledConstant arg) {
    if (arg instanceof PrimitiveConstant) {
      PrimitiveConstant prim = ((PrimitiveConstant) arg);
      Object value = prim.value;
      String stringValue = String.valueOf(value);
      if (prim.type == CodeConstants.CONSTANT_Class) {
        buf.appendCastTypeName(new VarType(stringValue));
      } else if (prim.type == CodeConstants.CONSTANT_String) {
        buf.append('"').append(ConstExprent.convertStringToJava(stringValue, false)).append('"');
      } else {
        buf.append(stringValue);
      }
    } else if (arg instanceof LinkConstant link) {
      if (link.classname != null) {
        buf.appendCastTypeName(new VarType(link.classname))
          .append("::")
          .append(link.elementname);
      } else if (link.descriptor != null) {
        buf.append("/* VF: Constant Dynamic */ (").appendCastTypeName(new VarType(link.descriptor))
          .append(") ")
          .append(link.elementname);
      }
    }
  }

  private static final ThreadLocal<int[]> ARGUMENT = ThreadLocal.withInitial(() -> new int[1]);

  // The direct arguments of a this(...)/super(...) delegation whose class declares another
  // constructor of the same arity: only those expressions are judged, and only while one is
  // being inferred or printed.
  private static final ThreadLocal<ListStack<List<Exprent>>> CTOR_DELEGATION =
    ThreadLocal.withInitial(ListStack::new);

  private boolean inConstructorDelegation() {
    ListStack<List<Exprent>> stack = CTOR_DELEGATION.get();
    if (stack.isEmpty()) {
      return false;
    }
    List<Exprent> direct = stack.peek();
    for (Exprent argument : direct) {
      Exprent value = argument;
      // The source's cast may still be in the tree even when the printer elides it.
      while (value instanceof FunctionExprent cast && cast.getFuncType() == FunctionType.CAST
        && !cast.getLstOperands().isEmpty()) {
        value = cast.getLstOperands().get(0);
      }
      if (value == this) {
        return true;
      }
    }
    return false;
  }

  private void enterConstructorDelegation() {
    CTOR_DELEGATION.get().push(constructorLooksOverloaded() ? lstParameters : List.of());
  }

  private static void exitConstructorDelegation() {
    CTOR_DELEGATION.get().pop();
  }

  /**
   * Whether this class declares more than one constructor with the call's parameter count. That
   * is the precondition for the delegation's overload resolution to withhold the target type.
   */
  private boolean constructorLooksOverloaded() {
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl == null || descriptor == null) {
      return false;
    }
    int arity = descriptor.params.length;
    int count = 0;
    for (StructMethod method : cl.getMethods()) {
      if (CodeConstants.INIT_NAME.equals(method.getName())
        && MethodDescriptor.parseDescriptor(method.getDescriptor()).params.length == arity) {
        if (++count >= 2) {
          return true;
        }
      }
    }
    return false;
  }

  private static final ThreadLocal<int[]> CALL_LINE = ThreadLocal.withInitial(() -> new int[]{-1});

  /** The target line of the innermost call whose arguments are being printed, or -1. */
  public static int enclosingCallLine() {
    return CALL_LINE.get()[0];
  }
  private static final ThreadLocal<StructMethod[]> ARGUMENT_AT =
    ThreadLocal.withInitial(() -> new StructMethod[64]);

  public static boolean inArgument() {
    return ARGUMENT.get()[0] > 0;
  }

  /**
   * Whether the printer is inside the argument list of the method it is printing. A lambda body
   * switches the current method, so a call written there is not subject to the enclosing call's
   * argument-line attribution.
   */
  public static boolean insideOwnArgumentList() {
    int depth = ARGUMENT.get()[0];
    return depth > 0 && ARGUMENT_AT.get()[depth - 1] == RoundTrip.currentMethod();
  }

  /** Tells the argument printer the line the call's own token sits on, from its `new`. */
  public void setCallerOpeningLine(int line) {
    callerOpeningLine = line;
  }

  public TextBuffer appendParamList(int indent) {
    int savedCallLine = CALL_LINE.get()[0];
    CALL_LINE.get()[0] = RoundTrip.sourceLineEnd(this);
    int depth = ++ARGUMENT.get()[0];
    if (depth <= ARGUMENT_AT.get().length) {
      ARGUMENT_AT.get()[depth - 1] = RoundTrip.currentMethod();
    }
    try {
      return appendParamList0(indent);
    } finally {
      ARGUMENT.get()[0]--;
      CALL_LINE.get()[0] = savedCallLine;
    }
  }

  private TextBuffer appendParamList0(int indent) {
    List<VarVersionPair> mask = null;
    boolean isEnum = false;
    if (functype == Type.INIT) {
      ClassNode newNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
      if (newNode != null) {
        mask = ExprUtil.getSyntheticParametersMask(newNode, stringDescriptor, lstParameters.size());
        isEnum = newNode.classStruct.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);
      }
    }
    ClassNode currCls = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    List<StructMethod> matches = getMatchedDescriptors(false);
    boolean ambiguousVararg = isVarargsAmbiguous(getMatchedDescriptors(true));
    BitSet setAmbiguousParameters = new BitSet(lstParameters.size());
    setAmbiguousParameters.or(getAmbiguousParameters(matches));
    BitSet lambdaAmbiguous = getLambdaAmbiguousParameters();
    setAmbiguousParameters.or(lambdaAmbiguous);

    // omit 'new Type[] {}' for the last parameter of a vararg method call
    if (lstParameters.size() == descriptor.params.length && isVarArgCall() && !lstParameters.isEmpty()) {
      Exprent lastParam = lstParameters.get(lstParameters.size() - 1);
      if (lastParam instanceof NewExprent lastNew && lastParam.getExprType().arrayDim >= 1) {
        if (!ambiguousVararg || lastNew.getLstArrayElements().size() != 1) {
          lastNew.setVarArgParam(true);
        }
      }
    }

    int start = isEnum ? 2 : 0;
    List<Exprent> parameters = new ArrayList<>(lstParameters);
    VarType[] types = Arrays.copyOf(descriptor.params, descriptor.params.length);
    for (int i = start; i < parameters.size(); i++) {
      Exprent par = parameters.get(i);
      if (par instanceof InvocationExprent) {
          InvocationExprent inv = (InvocationExprent)par;
        // "unbox" invocation parameters, e.g. 'byteSet.add((byte)123)' or 'new ShortContainer((short)813)'
        //However, we must make sure we don't accidentally make the call ambiguous.
        //An example being List<Integer>, remove(Integer.valueOf(1)) and remove(1) are different functions
        if (inv.isBoxingCall()) {
          Exprent value = inv.lstParameters.get(0);
          types[i] = value.getExprType(); //Infer?
          //Unboxing in this case is lossy, so we need to explicitly set the type
          if (types[i].typeFamily == TypeFamily.INTEGER) {
            types[i] =
              "java/lang/Short".equals(inv.classname) ? VarType.VARTYPE_SHORT :
              "java/lang/Byte".equals(inv.classname) ? VarType.VARTYPE_BYTE :
              "java/lang/Integer".equals(inv.classname) ? VarType.VARTYPE_INT :
               VarType.VARTYPE_CHAR;
          }

          int count = 0;
          StructClass stClass = DecompilerContext.getStructContext().getClass(classname);
          if (stClass != null) {
            List<StructMethod> customMatchedDescriptors = getMatchedDescriptors(false, (mt, md) -> {
              if (md.params.length == descriptor.params.length) {
                for (int x = 0; x < md.params.length; x++) {
                  if (md.params[x].typeFamily != descriptor.params[x].typeFamily &&
                    md.params[x].typeFamily != types[x].typeFamily
                  ) {
                    return false;
                  }

                  if (md.params[x].arrayDim != descriptor.params[x].arrayDim &&
                    md.params[x].arrayDim != types[x].arrayDim
                  ) {
                    return false;
                  }
                }
                return true;
              }

              return false;
            });
            count = customMatchedDescriptors.size();
          }

          if (count != matches.size()) { //We become more ambiguous? Lets keep the explicit boxing
            types[i] = descriptor.params[i];
            inv.boxing.forceBoxing = true;
          } else {
            value.addBytecodeOffsets(inv.bytecode); //Keep the bytecode for matching/debug
            parameters.set(i, value);
          }
        }
        // We also need to care about when things are intentionally unboxed to call a different overloaded method,
        //and skipping unboxing causes us to call ourselves.
        //  EXA:
        //  int compare(Integer a, Integer b) { return this.compare(a.intValue(), b.intValue()); }
        //  int compare(int a, int b) { return a - b; }
        //  Allowing the first function to unbox would cause infinite recursion
        // Right now it just do a quick check, but a proper check would be to do compiler like inference of argument
        // types, and check unboxing as needed. Currently it causes some false forces
        else if (inv.isUnboxingCall() && !inv.shouldForceUnboxing()) {
          StructClass stClass = DecompilerContext.getStructContext().getClass(classname);

          if (stClass != null) {
            for (StructMethod mt : stClass.getMethods()) {
              if (name.equals(mt.getName()) && (currCls == null || canAccess(currCls.classStruct, mt)) && !stringDescriptor.equals(mt.getDescriptor())) {
                MethodDescriptor md = MethodDescriptor.parseDescriptor(mt.getDescriptor());
                if (md.params.length == descriptor.params.length) {
                  if (md.params[i].type == CodeType.OBJECT) {
                    if (DecompilerContext.getStructContext().instanceOf(inv.getInstance().getExprType().value, md.params[i].value)) {
                      inv.forceUnboxing(true);
                      break;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    if (desc == null) {
      // FIXME: this is a hack, must remove
      this.getInferredExprType(null);

      if (genericsMap.isEmpty() && instance != null && functype != Type.INIT) {
        VarType instType = instance.getInferredExprType(null);
        if (instType.isGeneric() && instType.type != CodeType.GENVAR) {
          GenericType ginstance = (GenericType)instType;

          StructClass cls = DecompilerContext.getStructContext().getClass(instType.value);
          if (cls != null && cls.getSignature() != null) {
            cls.getSignature().genericType.mapGenVarsTo(ginstance, genericsMap);
          }
        }
      }
    }
    Map<Integer, Set<VarType>> unboundArguments = new HashMap<>();
    if (desc != null && desc.getSignature() != null) {
      Map<VarType, VarType> hierarchyMap = new HashMap<>();
      if (!classname.equals(desc.getClassQualifiedName())) {
        StructClass mthCls = DecompilerContext.getStructContext().getClass(classname);
        if (mthCls != null) {
          Map<String, Map<VarType, VarType>> hierarchy = mthCls.getAllGenerics();
          if (hierarchy.containsKey(desc.getClassQualifiedName())) {
            hierarchyMap = hierarchy.get(desc.getClassQualifiedName());
          }
        }
      }

      Set<VarType> namedGens = getNamedGenerics().keySet();
      int y = 0;
      for (int x = start; x < types.length; x++) {
        if (mask == null || mask.get(x) == null) {
          if (desc.getSignature().parameterTypes.size() <= y) {
            continue;
          }

          VarType rawType = desc.getSignature().parameterTypes.get(y++);
          VarType type = rawType.remap(hierarchyMap).remap(genericsMap);
          // A name that is in scope at the call site may be the caller's own variable of the same
          // name (the callee's signature and the caller often share letters); the source may have
          // meant that one, so only a name with no in-scope declaration proves the cast wrong.
          Map<VarType, List<VarType>> named = getNamedGenerics();
          // A type parameter of the called method that inference left unbound has no name at the
          // call site, but its recorded bound can be a type variable the caller does own: a
          // callee {@code V extends T} where T is the caller's variable can only be bound there
          // if the argument is a T, so the source cast to it. The cast erases to the bound's
          // erasure, which is exactly the parameter's erased type, so it changes no bytecode and
          // is only printed when the argument's own recorded type has that same erasure.
          List<String> typeParameters = desc.getSignature().typeParameters;
          if (type != null && type.type == CodeType.GENVAR && typeParameters.contains(type.value)
            && !genericsMap.containsKey(type)) {
            int index = typeParameters.indexOf(type.value);
            List<VarType> declaredBounds = index < desc.getSignature().typeParameterBounds.size()
              ? desc.getSignature().typeParameterBounds.get(index) : null;
            if (declaredBounds != null && declaredBounds.size() == 1) {
              VarType bound = declaredBounds.get(0).remap(hierarchyMap).remap(genericsMap);
              VarType argumentType = lstParameters.get(x).getExprType();
              if (bound != null && bound.type == CodeType.GENVAR && !bound.value.equals(type.value)
                && isInScopeTypeVariable(bound, named) && argumentType != null
                && argumentType.resizeArrayDim(0).equals(descriptor.params[x].resizeArrayDim(0))) {
                type = bound;
              }
            }
          }
          // A type parameter of the called method that inference left unbound is not a type any
          // source can name at the call site: its name belongs to the callee's signature, not to
          // this scope, and a caller variable that happens to share the name is a different
          // variable. Record it for the argument's cast decision; javac infers it again.
          Set<VarType> unbound = unboundTypeParameters(rawType, desc.getSignature().typeParameters, genericsMap);
          VarType erasedParameter = x < descriptor.params.length ? descriptor.params[x] : null;
          unbound.removeIf(variable -> isInScopeTypeVariable(variable, named)
            && (!isBareTypeVariable(rawType) || callerVariableFitsParameter(variable, named, erasedParameter)));
          if (!unbound.isEmpty()) {
            unboundArguments.put(x, unbound);
          }
          if (type != null && !(type.isGeneric() && ((GenericType)type).hasUnknownGenericType(namedGens))) {
            types[x] = type;
          }
        }
      }
    }

    // A cast to a wildcard type cannot be the target of a lambda, and a lambda cast to one does not
    // satisfy the parameter it was meant to disambiguate. Leave those overloads as they were.
    for (int i = lambdaAmbiguous.nextSetBit(0); i >= 0; i = lambdaAmbiguous.nextSetBit(i + 1)) {
      if (i >= types.length || types[i] == null || !types[i].isGeneric()
          || ExprProcessor.getTypeName(types[i]).contains("?")) {
        setAmbiguousParameters.clear(i);
      }
    }

    TextBuffer buf = new TextBuffer();

    boolean firstParameter = true;
    int previousLine = -1;
    int callLine = RoundTrip.sourceLineEnd(this);
    int firstLine = start < lstParameters.size() ? RoundTrip.sourceLine(lstParameters.get(start)) : -1;
    // The line the call's own token sits on: the first argument's, when javac started a line
    // there; otherwise the invoke's inherited line is the only line the call is known to have.
    boolean firstStartsLine = start < lstParameters.size() && RoundTrip.lineStartsHere(lstParameters.get(start));
    int openingLine = callerOpeningLine >= 0 ? callerOpeningLine : firstStartsLine ? firstLine : callLine;
    if (!lstParameters.isEmpty()) {
      buf.pushNewlineGroup(indent, 1);
      // A later argument line is always a break the source had. An earlier one is normally the
      // enclosing statement's marker inherited by the argument's pushes, but not when the argument
      // itself has an entry there: then its own expression started that line.
      if (callLine >= 0 && firstLine >= 0 && firstLine != callLine
          && (firstLine > callLine || RoundTrip.lineStartsHere(lstParameters.get(start)))) {
        buf.appendLineSeparator();
      } else {
        buf.appendPossibleNewline();
      }
      buf.pushNewlineGroup(indent, 0);
    }

    for (int i = start; i < lstParameters.size(); i++) {
      if (mask == null || mask.get(i) == null) {
        TextBuffer buff = new TextBuffer();
        boolean ambiguous = setAmbiguousParameters.get(i);

        if (i == parameters.size() - 1 && lstParameters.get(i).getExprType() == VarType.VARTYPE_NULL && NewExprent.probablySyntheticParameter(descriptor.params[i].value)) {
          break;  // skip last parameter of synthetic constructor call
        }

        // 'byte' and 'short' literals need an explicit narrowing type cast when used as a parameter
        Set<VarType> unbound = unboundArguments.get(i);
        if (unbound != null) {
          UNBOUND_ARGUMENT.get().push(new UnboundArgument(RoundTrip.currentMethod(), unbound));
        }
        VarType argumentType = types[i];
        if (unbound != null && !unbound.isEmpty() && argumentType != null
          && lstParameters.get(i) instanceof NewExprent lambda && lambda.isLambda() && !lambda.isMethodReference()) {
          // The called method's signature declared these variables and the printer's inference
          // gave them no value. The source cannot name them at the call site, so a name shared
          // with a caller variable is a different variable; leaving it in the lambda's target
          // type makes the printer read it as the caller's and pin the body's returns to it.
          // The body's own recorded value type is then the only target, and javac infers the
          // call's variable from it exactly as the original source did.
          Map<VarType, List<VarType>> inScope = getNamedGenerics();
          Map<VarType, VarType> shadowed = null;
          for (VarType variable : unbound) {
            if (inScope.containsKey(variable)) {
              if (shadowed == null) {
                shadowed = new HashMap<>();
              }
              shadowed.put(variable, GenericType.DUMMY_VAR);
            }
          }
          if (shadowed != null) {
            argumentType = argumentType.remap(shadowed);
          }
        }
        try {
          ExprProcessor.getCastedExprent(lstParameters.get(i), argumentType, buff, indent, ambiguous ? ExprProcessor.NullCastType.CAST : ExprProcessor.NullCastType.DONT_CAST_AT_ALL, ambiguous, true, true);
        } finally {
          if (unbound != null) {
            UNBOUND_ARGUMENT.get().pop();
          }
        }

        int line = RoundTrip.sourceLine(lstParameters.get(i));
        // Only a later line is a break the original had; an equal or earlier one is inheritance
        // from the enclosing statement's marker. javac attributes the invoke to the first
        // argument's line, so a later argument at the call's own line was written on that line:
        // the first argument merely inherited the declaration's line above it.
        boolean callLineGate = DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_ARG_CALL_LINE);
        boolean forced = !firstParameter && line >= 0 && previousLine >= 0 && line > previousLine
          && (!callLineGate || openingLine < 0 || line > openingLine);

        // the last "new Object[0]" in the vararg call is not printed
        if (buff.length() > 0) {
          if (!firstParameter) {
            buf.append(",");
            if (forced) {
              buf.appendLineSeparator();
            } else {
              buf.appendPossibleNewline(" ");
            }
          }
          buf.append(buff);
        }
        if (line >= 0) {
          previousLine = line;
        }

        firstParameter = false;
      }
    }

    if (!lstParameters.isEmpty()) {
      buf.popNewlineGroup();
      if (previousLine >= 0 && callLine >= 0 && previousLine != callLine
          && (!RoundTrip.selector("arg-entry")
              || RoundTrip.lineStartsHere(lstParameters.get(lstParameters.size() - 1)))) {
        buf.appendLineSeparator();
      } else {
        buf.appendPossibleNewline("", true);
      }
      buf.popNewlineGroup();
    }

    return buf;
  }

  /** An argument's recorded parameter type names variables no source can spell at this call. */
  private record UnboundArgument(StructMethod method, Set<VarType> variables) {}

  private static final ThreadLocal<Deque<UnboundArgument>> UNBOUND_ARGUMENT =
    ThreadLocal.withInitial(ArrayDeque::new);

  /**
   * Whether the type names a type parameter of the method whose argument is being printed while
   * the inference at this call site left it unbound. Such a variable exists only inside the
   * callee's declaration; a caller variable that happens to share its name is a different
   * variable, so a cast written with it names the wrong type. The lambda body is a different
   * method, printed under its own signatures, and does not inherit the argument's scope.
   */
  public static boolean namesUnboundArgumentVariable(VarType type) {
    UnboundArgument top = UNBOUND_ARGUMENT.get().peek();
    return top != null && top.method == RoundTrip.currentMethod()
      && mentionsVariable(type, top.variables);
  }

  private static boolean mentionsVariable(VarType type, Set<VarType> variables) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR && variables.contains(type)) {
      return true;
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (mentionsVariable(argument, variables)) {
          return true;
        }
      }
    }
    return false;
  }

  /** The callee-declared type parameters a recorded parameter type still names after inference. */
  private static Set<VarType> unboundTypeParameters(VarType type, List<String> typeParameters,
                                                    Map<VarType, VarType> genericsMap) {
    Set<VarType> result = new HashSet<>();
    collectUnboundTypeParameters(type, typeParameters, genericsMap, result);
    return result;
  }

  /** Whether the declared parameter type is nothing but the type variable itself. */
  private static boolean isBareTypeVariable(VarType type) {
    return type != null && type.type == CodeType.GENVAR && type.arrayDim == 0
      && (!(type instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO);
  }

  /**
   * A parameter that is exactly the callee's own unbound type variable can only be printed as a
   * caller variable of the same name, so the cast this printer emits names that variable. The
   * call then has to compile: the argument is converted to the caller's variable, whose erasure
   * must be a subtype of the parameter's erased type. When it is not - a callee {@code <T
   * extends Avatar> get(T)} called from a {@code <T extends Entity>} method, where the shared
   * letter is the caller's - no source could have written the cast, and the argument is passed
   * through for javac to infer the callee's variable from it.
   */
  private static boolean callerVariableFitsParameter(VarType variable, Map<VarType, List<VarType>> named,
                                                     VarType parameter) {
    List<VarType> callerBounds = named.get(variable);
    VarType callerBound = callerBounds == null || callerBounds.isEmpty() ? null : callerBounds.get(0);
    if (callerBound == null || callerBound.type != CodeType.OBJECT || parameter == null
      || parameter.type != CodeType.OBJECT || parameter.arrayDim != 0) {
      return true; // no class bound to compare, or an erased shape this check does not cover
    }
    return DecompilerContext.getStructContext().instanceOf(callerBound.value, parameter.value);
  }

  private static void collectUnboundTypeParameters(VarType type, List<String> typeParameters,
                                                   Map<VarType, VarType> genericsMap, Set<VarType> result) {
    if (type == null) {
      return;
    }
    if (type.type == CodeType.GENVAR && typeParameters.contains(type.value)
      && !genericsMap.containsKey(type)) {
      result.add(type.resizeArrayDim(0));
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        collectUnboundTypeParameters(argument, typeParameters, genericsMap, result);
      }
    }
  }

  private boolean isVarArgCall() {
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl != null) {
      StructMethod mt = cl.getMethod(InterpreterUtil.makeUniqueKey(name, stringDescriptor));
      if (mt == null) {
        mt = cl.getMethodRecursive(name, stringDescriptor);
      }
      if (mt != null) {
        return mt.hasModifier(CodeConstants.ACC_VARARGS);
      }
    }
    else {
      // try to check the class on the classpath
      Method mtd = ClasspathHelper.findMethod(classname, name, descriptor);
      return mtd != null && mtd.isVarArgs();
    }
    return false;
  }

  public boolean isBoxingCall() {
    if (isStatic && "valueOf".equals(name) && lstParameters.size() == 1) {
      CodeType paramType = lstParameters.get(0).getExprType().type;

      // special handling for ambiguous types
      if (lstParameters.get(0) instanceof ConstExprent) {
        // 'Integer.valueOf(1)' has '1' type detected as TYPE_BYTECHAR
        // 'Integer.valueOf(40_000)' has '40_000' type detected as TYPE_CHAR
        // so we check the type family instead
        if (lstParameters.get(0).getExprType().typeFamily == TypeFamily.INTEGER) {
          if (classname.equals("java/lang/Integer")) {
            return true;
          }
        }

        if (paramType == CodeType.BYTECHAR || paramType == CodeType.SHORTCHAR) {
          if (classname.equals("java/lang/Character") || classname.equals("java/lang/Short")) {
            return true;
          }
        }
      }

      return classname.equals(getClassNameForPrimitiveType(paramType));
    }

    return false;
  }

  public void markUsingBoxingResult() {
    canIgnoreBoxing = false;
  }

  @Override
  public void setIsQualifier() {
    isQualifier = true;
  }

  // TODO: move to CodeConstants ???
  private static String getClassNameForPrimitiveType(CodeType type) {
    switch (type) {
      case BOOLEAN:
        return "java/lang/Boolean";
      case BYTE:
      case BYTECHAR:
        return "java/lang/Byte";
      case CHAR:
        return "java/lang/Character";
      case SHORT:
      case SHORTCHAR:
        return "java/lang/Short";
      case INT:
        return "java/lang/Integer";
      case LONG:
        return "java/lang/Long";
      case FLOAT:
        return "java/lang/Float";
      case DOUBLE:
        return "java/lang/Double";
    }
    return null;
  }

  private static final Map<String, String> UNBOXING_METHODS;

  static {
    UNBOXING_METHODS = new HashMap<>();
    UNBOXING_METHODS.put("booleanValue", "java/lang/Boolean");
    UNBOXING_METHODS.put("byteValue", "java/lang/Byte");
    UNBOXING_METHODS.put("shortValue", "java/lang/Short");
    UNBOXING_METHODS.put("intValue", "java/lang/Integer");
    UNBOXING_METHODS.put("longValue", "java/lang/Long");
    UNBOXING_METHODS.put("floatValue", "java/lang/Float");
    UNBOXING_METHODS.put("doubleValue", "java/lang/Double");
    UNBOXING_METHODS.put("charValue", "java/lang/Character");
  }

  public boolean isUnboxingCall() {
    return !isStatic && lstParameters.isEmpty() && classname.equals(UNBOXING_METHODS.get(name));
  }

  public void forceBoxing(boolean value) {
    boxing.forceBoxing = value;
  }

  public boolean shouldForceBoxing() {
    return boxing.forceBoxing;
  }

  public void forceUnboxing(boolean value) {
    boxing.forceUnboxing = value;
  }

  public boolean shouldForceUnboxing() {
    return boxing.forceUnboxing;
  }

  private List<StructMethod> getMatchedDescriptors(boolean varargs) {
    return getMatchedDescriptors(varargs, null);
  }

  private List<StructMethod> getMatchedDescriptors(boolean varargs, @Nullable BiFunction<StructMethod, MethodDescriptor, Boolean> customParamMatcher) {
    List<StructMethod> matches = new ArrayList<>();
    ClassNode currCls = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl == null) return matches;
    StructMethod currentMethod = cl.getMethod(InterpreterUtil.makeUniqueKey(name, stringDescriptor));

    Set<String> visited = new HashSet<>();
    Queue<StructClass> que = new ArrayDeque<>();
    que.add(cl);

    while (!que.isEmpty()) {
      StructClass cls = que.poll();
      if (cls == null)
          continue;

      for (StructMethod mt : cls.getMethods()) {
        if (name.equals(mt.getName())) {
          MethodDescriptor md = MethodDescriptor.parseDescriptor(mt.getDescriptor());
          boolean matchedParams;
          if (customParamMatcher == null) {
            if (varargs) {
              matchedParams = matchesVarargs(md.params, descriptor.params, mt, currentMethod);
            } else {
              matchedParams = matches(md.params, descriptor.params);
            }
          } else {
            matchedParams = customParamMatcher.apply(mt, md);
          }
          if (matchedParams && (currCls == null || canAccess(currCls.classStruct, mt))) {
            matches.add(mt);
          }
        }
      }

      if (cls == cl && !matches.isEmpty()) {
        return matches;
      }

      visited.add(cls.qualifiedName);
      if (cls.superClass != null && !visited.contains(cls.superClass.value)) {
        StructClass tmp = DecompilerContext.getStructContext().getClass((String)cls.superClass.value);
        if (tmp != null) {
          que.add(tmp);
        }
      }

      for (String intf : cls.getInterfaceNames()) {
        if (!visited.contains(intf)) {
          StructClass tmp = DecompilerContext.getStructContext().getClass(intf);
          if (tmp != null) {
            que.add(tmp);
          }
        }
      }

    }

    return matches;
  }

  private boolean matches(VarType[] left, VarType[] right) {
    if (left.length == right.length) {
      for (int i = 0; i < left.length; i++) {
        TypeFamily leftFamily = left[i].typeFamily;
        TypeFamily rightFamily = right[i].typeFamily;
        if (leftFamily != rightFamily && !(leftFamily.isNumeric() && rightFamily.isNumeric())) {
          return false;
        }

        if (i >= lstParameters.size() || lstParameters.get(i).getExprType().type != CodeType.NULL) {
          if (left[i].arrayDim != right[i].arrayDim) {
            return false;
          }
        }
      }
      return true;
    }
    return false;
  }

  private boolean matchesVarargs(VarType[] left, VarType[] right, StructMethod leftMethod, StructMethod rightMethod) {
    if (left.length == right.length) {
      for (int i = 0; i < left.length; i++) {
        TypeFamily leftFamily = left[i].typeFamily;
        TypeFamily rightFamily = right[i].typeFamily;
        if (leftFamily != rightFamily && !(leftFamily.isNumeric() && rightFamily.isNumeric())) {
          return false;
        }

        VarType leftType = left[i];
        if (leftMethod.hasModifier(CodeConstants.ACC_VARARGS) && i == left.length - 1) {
          leftType = leftType.decreaseArrayDim();
        }
        VarType rightType = right[i];
        if (rightMethod != null && rightMethod.hasModifier(CodeConstants.ACC_VARARGS) && i == right.length - 1) {
          rightType = rightType.decreaseArrayDim();
        }

        if (i >= lstParameters.size() || lstParameters.get(i).getExprType().type != CodeType.NULL) {
          if (leftType.arrayDim != rightType.arrayDim) {
            return false;
          }

          // If we have two types which are both Object, it's hard to tell what is compatible.
          // We need to get the common type between the two. If there isn't one, it means the type isn't compatible.
          if (leftType.type == CodeType.OBJECT && rightType.type == CodeType.OBJECT) {
            VarType commonType = VarType.meet(leftType, rightType);
            if (commonType == null || commonType == VarType.VARTYPE_NULL) {
              return false;
            }
          }
        }
      }
      return true;
    }
    return false;
  }

  private boolean canAccess(StructClass currCls, StructMethod mt) {
    if (mt.hasModifier(CodeConstants.ACC_PUBLIC)) {
      return true;
    }
    else if (mt.hasModifier(CodeConstants.ACC_PRIVATE)) {
      return mt.getClassQualifiedName().equals(currCls.qualifiedName);
    }
    else if (mt.hasModifier(CodeConstants.ACC_PROTECTED)) {
      boolean samePackage = isInSamePackage(currCls.qualifiedName, mt.getClassQualifiedName());
      return samePackage || DecompilerContext.getStructContext().instanceOf(currCls.qualifiedName, mt.getClassQualifiedName());
    }
    else {
      return isInSamePackage(currCls.qualifiedName, mt.getClassQualifiedName());
    }
  }

  private boolean isInSamePackage(String class1, String class2) {
    int pos1 = class1.lastIndexOf('/');
    int pos2 = class2.lastIndexOf('/');
    if (pos1 != pos2) {
      return false;
    }

    if (pos1 == -1) {
      return true;
    }

    String pkg1 = class1.substring(0, pos1);
    String pkg2 = class2.substring(0, pos2);
    return pkg1.equals(pkg2);
  }

  private boolean isVarargsAmbiguous(List<StructMethod> matches) {
    Set<StructMethod> varargs = matches.stream().filter(mt -> mt.hasModifier(CodeConstants.ACC_VARARGS))
      .collect(Collectors.toSet());

    // Check for:
    // method(type t)
    // method(type... t) // overload

    for (StructMethod match : matches) {
      for (StructMethod vararg : varargs) {
        if (match == vararg) {
          continue;
        }

        MethodDescriptor md1 = match.methodDescriptor();
        MethodDescriptor md2 = vararg.methodDescriptor();
        if (md1.params.length != md2.params.length) {
          // Should be impossible, but always be sure
          continue;
        }

        if (md1.params[md1.params.length - 1].equals(md2.params[md2.params.length - 1].decreaseArrayDim())) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * javac judges whether an overload applies to a lambda or method reference by arity and functional
   * interface, not by the descriptor the target already resolved. Two such overloads are ambiguous
   * in source even though the target's descriptor names one of them; the original source had to cast
   * its argument, and printing that cast restores it.
   */
  private BitSet getLambdaAmbiguousParameters() {
    BitSet result = new BitSet(lstParameters.size());
    if (!RoundTrip.selector("overloadcast")) {
      return result;
    }
    boolean hasLambda = false;
    for (Exprent param : lstParameters) {
      if (param instanceof NewExprent && ((NewExprent) param).isLambda()) {
        hasLambda = true;
        break;
      }
    }
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (!hasLambda || cl == null) {
      return result;
    }
    List<StructMethod> candidates = collectSameNameSameArity(cl);
    if (candidates.size() < 2) {
      return result;
    }
    for (int i = 0; i < lstParameters.size(); i++) {
      if (!(lstParameters.get(i) instanceof NewExprent lambda) || !lambda.isLambda()) {
        continue;
      }
      String key = lambda.getLambdaMethodKey();
      int paren = key.indexOf('(');
      if (paren < 0) {
        continue;
      }
      int arity = MethodDescriptor.parseDescriptor(key.substring(paren)).params.length;
      int applicable = 0;
      for (StructMethod mt : candidates) {
        MethodDescriptor md = mt.methodDescriptor();
        if (md.params.length != lstParameters.size()) {
          continue;
        }
        // The erased descriptor hides a type-variable parameter behind Object; read the signature.
        org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor signature = mt.getSignature();
        VarType genericParam = signature != null && i < signature.parameterTypes.size()
          ? signature.parameterTypes.get(i) : md.params[i];
        if (genericParam.type == CodeType.GENVAR) {
          // A parameter typed by a type variable can itself be a functional interface, so javac has
          // no way to choose between this overload and a functional-interface one; the source cast.
          applicable++;
          continue;
        }
        StructClass paramType = DecompilerContext.getStructContext().getClass(md.params[i].value);
        if (paramType == null) {
          continue;
        }
        StructMethod abstractMethod = ExprProcessor.functionalMethod(paramType);
        if (abstractMethod != null && abstractMethod.methodDescriptor().params.length == arity) {
          applicable++;
        }
      }
      if (applicable > 1) {
        result.set(i);
      }
    }
    return result;
  }

  /** Same-name, same-arity methods from the receiver's class, or its first ancestor declaring any. */
  private List<StructMethod> collectSameNameSameArity(StructClass cl) {
    List<StructMethod> found = new ArrayList<>();
    Set<String> visited = new HashSet<>();
    Queue<StructClass> queue = new ArrayDeque<>();
    queue.add(cl);
    while (!queue.isEmpty()) {
      StructClass cls = queue.poll();
      if (cls == null) {
        continue;
      }
      for (StructMethod mt : cls.getMethods()) {
        // Bridges and synthetics are not overloads in source; the raw bridge beside a covariant
        // override would otherwise read as a second, ambiguous overload.
        if (mt.hasModifier(CodeConstants.ACC_SYNTHETIC) || mt.hasModifier(CodeConstants.ACC_BRIDGE)) {
          continue;
        }
        if (name.equals(mt.getName()) && mt.methodDescriptor().params.length == lstParameters.size()) {
          found.add(mt);
        }
      }
      if (cls == cl && !found.isEmpty()) {
        return found;
      }
      visited.add(cls.qualifiedName);
      if (cls.superClass != null && !visited.contains(cls.superClass.value)) {
        StructClass parent = DecompilerContext.getStructContext().getClass((String) cls.superClass.value);
        if (parent != null) {
          queue.add(parent);
        }
      }
      for (String intf : cls.getInterfaceNames()) {
        if (!visited.contains(intf)) {
          StructClass parent = DecompilerContext.getStructContext().getClass(intf);
          if (parent != null) {
            queue.add(parent);
          }
        }
      }
    }
    return found;
  }

  private BitSet getAmbiguousParameters(List<StructMethod> matches) {
    StructClass cl = DecompilerContext.getStructContext().getClass(classname);
    if (cl == null || matches.size() == 1) {
      return EMPTY_BIT_SET;
    }

    BitSet missed = new BitSet(lstParameters.size());

    // treat signature polymorphic methods as always ambiguous
    // even if we have the classes available and think they are accepting Object...
    if (CodeConstants.areParametersPolymorphic(classname, name)) {
      missed.set(0, lstParameters.size());
      return missed;
    }

    StructMethod currentMethod = cl.getMethod(InterpreterUtil.makeUniqueKey(name, stringDescriptor));

    Set<StructMethod> possible = new HashSet<>();
    Set<StructMethod> exacts = new HashSet<>();

    BitSet ambiguous = new BitSet(descriptor.params.length);
    for (StructMethod mt : matches) {
      MethodDescriptor md = mt.methodDescriptor();

      boolean exact = true;
      for (int i = 0; i < md.params.length; i++) {
        Exprent exp = lstParameters.get(i);

        // Peek through non-casting types
        if (exp instanceof FunctionExprent f && !f.doesCast()) {
          exp = f.getLstOperands().get(0);
        }

        VarType type = exp.getExprType();

        exact &= md.params[i].equals(type) || type.type == CodeType.NULL;

        if (md.params[i].higherCrossFamilyThan(type, true)) {
          possible.add(mt);
        }
      }

      if (exact) {
        // What method would we call if we were unambiguous?
        exacts.add(mt);
      }
    }

    if (possible.size() == 1) {
      return EMPTY_BIT_SET;
    }

    if (exacts.isEmpty()) {
      return EMPTY_BIT_SET;
    } else if (exacts.size() == 1) {
      StructMethod exact = exacts.iterator().next();

      // Exact method is our own? No need to check ambiguity, we have our match!
      if (exact == currentMethod) {
        return EMPTY_BIT_SET;
      }
    }

    // Now check for ambiguity
    MethodDescriptor md = currentMethod == null ? MethodDescriptor.parseDescriptor(stringDescriptor) : currentMethod.methodDescriptor();
    for (StructMethod p : possible) {
      for (int i = 0; i < md.params.length; i++) {
        Exprent exp = lstParameters.get(i);

        // Poke through non-casting types
        if (exp instanceof FunctionExprent f && !f.doesCast()) {
          exp = f.getLstOperands().get(0);
        }

        VarType type = exp.getExprType();

        MethodDescriptor pmd = p.methodDescriptor();
        // Only consider non-equivalent types
        if (!md.params[i].equals(pmd.params[i])) {
          // If our desired method is higher in the lattice than

          if (md.params[i].higherCrossFamilyThan(pmd.params[i], false)) {
            ambiguous.set(i);
          } else if (type.equals(pmd.params[i])) {
            ambiguous.set(i);
          } else if (type.type == CodeType.NULL) {
            ambiguous.set(i);
          }
        }
      }
    }

    return ambiguous;
  }

  private boolean processGenericMapping(VarType from, VarType to, Map<VarType, List<VarType>> named, Map<VarType, List<VarType>> bounds) {
    if (VarType.VARTYPE_NULL.equals(to) || (to != null && to.type == CodeType.GENVAR && !named.containsKey(to.resizeArrayDim(0)))) {
      return false;
    }

    VarType current = genericsMap.get(from);
    if (!genericsMap.containsKey(from)) {
      putGenericMapping(from, to, named, bounds);

      return true;
    } else if (to != null && current != null && !to.equals(current)) {
      if (named.containsKey(current.resizeArrayDim(0))) {
        return false;
      }

      if (current.type != CodeType.GENVAR && to.type == CodeType.GENVAR) {
        if (named.containsKey(to.resizeArrayDim(0))) {
          VarType bound = named.get(to.resizeArrayDim(0)).get(0);
          if (!bound.equals(VarType.VARTYPE_OBJECT) && DecompilerContext.getStructContext().instanceOf(bound.value, current.value)) {
            return false;
          }
        }
      }

      if (to.isGeneric() && current.isGeneric() && GenericType.isAssignable(to, current, named)) {
        putGenericMapping(from, to, named, bounds);

        return true;
      }
    }

    return false;
  }

  private void putGenericMapping(VarType from, VarType to, Map<VarType, List<VarType>> named, Map<VarType, List<VarType>> bounds) {
    if (isMappingInBounds(from, to, named, bounds, new HashSet<>())) {
      genericsMap.put(from, to);
    }
  }

  private boolean isMappingInBounds(VarType from, VarType to, Map<VarType, List<VarType>> named, Map<VarType, List<VarType>> bounds, Set<Pair<VarType, VarType>> recursivelySeen) {
    if (!bounds.containsKey(from)) {
      return false;
    }

    if (to == null || (to.type == CodeType.GENVAR && !named.containsKey(to.resizeArrayDim(0)))) {
      return true;
    }

    java.util.function.BiFunction<VarType, VarType, Boolean>  verifier = (newTo, bound) -> {
      if (bound.type == CodeType.GENVAR) {
        java.util.function.Function<VarType, VarType> map = e -> {
          VarType mapped = genericsMap.get(e);
          if (mapped == null)
            mapped = named.containsKey(e) ? named.get(e).get(0) : null;
          return mapped;
        };
        VarType mapped = map.apply(bound);

        Map<VarType, VarType> seen = new HashMap<>();
        if (mapped != null && !mapped.equals(bound)) {
          VarType last = bound;
          while (bound != null) {
            last = bound;
            bound = map.apply(bound);

            // TODO: fixes potential infinite loop, is this valid?
            if (last.equals(bound)) {
              break;
            }
            if (seen.containsKey(last) && seen.get(last).equals(bound)) {
              // Not making any progress?
              break;
            } else {
              seen.put(last, bound);
            }
          }
          bound = last;

          if (bound.type != CodeType.GENVAR) {
            return DecompilerContext.getStructContext().instanceOf(newTo.value, bound.value);
          }
        }

        Pair<VarType, VarType> pair = Pair.of(bound, newTo);
        if (!recursivelySeen.contains(pair)) {
          recursivelySeen.add(pair);
          return isMappingInBounds(bound, newTo, named, bounds, recursivelySeen);
        }
      }

      if (newTo.type.ordinal() < CodeType.OBJECT.ordinal()) {
        return bound.equals(VarType.VARTYPE_OBJECT) || bound.equals(newTo);
      }

      if (newTo.type != CodeType.GENVAR) {
        if (!DecompilerContext.getStructContext().instanceOf(newTo.value, bound.value)) {
          return false;
        }
      }

      if (bound.isGeneric() && !((GenericType)bound).getArguments().isEmpty()) {
        GenericType genbound = (GenericType)bound;
        VarType _new = newTo;

        if (!newTo.value.equals(bound.value)) {
          _new = GenericType.getGenericSuperType(newTo, bound);
        }

        if (!_new.isGeneric() || ((GenericType)_new).getArguments().size() != genbound.getArguments().size()) {
          return false;
        }

        Map<VarType, VarType> toAdd = new HashMap<>();
        GenericType genNew = (GenericType)_new;
        for (int i = 0; i < genbound.getArguments().size(); ++i) {
          VarType boundArg = genbound.getArguments().get(i);
          VarType newArg = genNew.getArguments().get(i);

          if (boundArg == null) {
            continue;
          }

          if (!boundArg.equals(newArg)) {
            // T extends Comparable<T>
            if (from.equals(boundArg) && to.equals(newArg)) {
              continue;
            }

            // T extends Comparable<S>, S extends Object
            if (bounds.containsKey(boundArg)) {
              Pair<VarType, VarType> pair = Pair.of(bound, newTo);
              if (!recursivelySeen.contains(pair)) {
                recursivelySeen.add(pair);
                if (isMappingInBounds(boundArg, newArg, named, bounds, recursivelySeen)) {
                  toAdd.put(boundArg, newArg);
                  continue;
                }
              }
            }
            return false;
          }
        }
        toAdd.forEach((k, v) -> processGenericMapping(k, v, named, bounds));
      }
      return true;
    };

    List<VarType> toVerify = (to.type == CodeType.GENVAR) ? named.get(to.resizeArrayDim(0)) : Collections.singletonList(to);

    // We need to satisfy all the bounds for the type we are mapping to
    // The bounds can be satisfied by any of the bounds for the named type. Inference can add to a
    // bound list while it is being walked, so iterate a snapshot instead of the live list.
    return new java.util.ArrayList<>(bounds.get(from))
      .stream().allMatch(bound -> toVerify.stream().anyMatch(v -> verifier.apply(v, bound)));
  }

  private Map<VarType, List<VarType>> getGenericBounds(StructClass mthCls) {
    Map<VarType, List<VarType>> bounds = new HashMap<>();

    if (desc.getSignature() != null) {
      for (int x = 0; x < desc.getSignature().typeParameters.size(); x++) {
        bounds.putIfAbsent(GenericType.parse("T" + desc.getSignature().typeParameters.get(x) + ";"), desc.getSignature().typeParameterBounds.get(x));
      }
    }

    if (mthCls.getSignature() != null) {
      for (int x = 0; x < mthCls.getSignature().fparameters.size(); x++) {
        bounds.putIfAbsent(GenericType.parse("T" + mthCls.getSignature().fparameters.get(x) + ";"), mthCls.getSignature().fbounds.get(x));
      }
    }

    ClassNode cn = DecompilerContext.getClassProcessor().getMapRootClasses().get(mthCls.qualifiedName);
    cn = cn != null ? cn.parent : null;

    while (cn != null) {
      if (cn.classStruct.getSignature() != null) {
        for (int x = 0; x < cn.classStruct.getSignature().fparameters.size(); x++) {
          bounds.putIfAbsent(GenericType.parse("T" + cn.classStruct.getSignature().fparameters.get(x) + ";"), cn.classStruct.getSignature().fbounds.get(x));
        }
      }
      cn = cn.parent;
    }

    return bounds;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == instance) {
      instance = newExpr;
    }

    for (int i = 0; i < lstParameters.size(); i++) {
      if (oldExpr == lstParameters.get(i)) {
        lstParameters.set(i, newExpr);
      }
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof InvocationExprent)) return false;

    InvocationExprent it = (InvocationExprent)o;
    return InterpreterUtil.equalObjects(name, it.getName()) &&
           InterpreterUtil.equalObjects(classname, it.getClassname()) &&
           isStatic == it.isStatic() &&
           InterpreterUtil.equalObjects(instance, it.getInstance()) &&
           InterpreterUtil.equalObjects(descriptor, it.getDescriptor()) &&
           functype == it.getFunctype() &&
           InterpreterUtil.equalLists(lstParameters, it.getLstParameters());
  }

  public List<Exprent> getLstParameters() {
    return lstParameters;
  }

  public void setLstParameters(List<Exprent> lstParameters) {
    this.lstParameters = lstParameters;
  }

  public MethodDescriptor getDescriptor() {
    return descriptor;
  }

  public void setDescriptor(MethodDescriptor descriptor) {
    this.descriptor = descriptor;
  }

  public String getClassname() {
    return classname;
  }

  public void setClassname(String classname) {
    this.classname = classname;
  }

  public Type getFunctype() {
    return functype;
  }

  public void setFunctype(Type functype) {
    this.functype = functype;
  }

  public Exprent getInstance() {
    return instance;
  }

  public void setInstance(Exprent instance) {
    this.instance = instance;
  }

  public boolean isStatic() {
    return isStatic;
  }

  public void setStatic(boolean isStatic) {
    this.isStatic = isStatic;
  }

  public String getName() {
    return name;
  }

  public void setName(String name) {
    this.name = name;
  }

  public String getStringDescriptor() {
    return stringDescriptor;
  }

  public void setStringDescriptor(String stringDescriptor) {
    this.stringDescriptor = stringDescriptor;
  }

  public InvocationType getInvocationType() {
    return invocationType;
  }

  public String getInvokeDynamicClassSuffix() {
    return invokeDynamicClassSuffix;
  }

  public LinkConstant getBootstrapMethod() {
    return bootstrapMethod;
  }

  public List<PooledConstant> getBootstrapArguments() {
    return bootstrapArguments;
  }

  public void setSyntheticNullCheck() {
    isSyntheticNullCheck = true;
  }

  public boolean isSyntheticNullCheck() {
    return isSyntheticNullCheck;
  }

  /**
   * A poly expression's type comes from its target. javac does not carry the target into every
   * branch of one, so a call inferred to an enclosing type variable there needs the witness printed.
   */
  private static final ThreadLocal<int[]> POLY = ThreadLocal.withInitial(() -> new int[1]);

  public static void enterPoly() {
    POLY.get()[0]++;
  }

  public static void exitPoly() {
    POLY.get()[0]--;
  }

  public static boolean inPoly() {
    return POLY.get()[0] > 0;
  }

  private boolean hasWildcardArgs(List<String> fparams, Map<VarType, VarType> genericsMap) {
    List<VarType> probe = new java.util.ArrayList<>();
    getGenericArgs(fparams, genericsMap, probe);
    for (VarType arg : probe) {
      if (containsWildcard(arg)) {
        return true;
      }
    }
    return false;
  }

  private static boolean containsWildcard(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument == null) {
        return true;
      }
      if (containsWildcard(argument)) {
        return true;
      }
    }
    return false;
  }

  private boolean hasGenvarArgs(List<String> fparams, Map<VarType, VarType> genericsMap) {
    List<VarType> probe = new java.util.ArrayList<>();
    getGenericArgs(fparams, genericsMap, probe);
    for (VarType arg : probe) {
      if (arg.type == CodeType.GENVAR && arg != GenericType.DUMMY_VAR) {
        return true;
      }
    }
    return false;
  }

  /**
   * A this(...)/super(...) argument whose result type is one of the callee's own type variables
   * and whose value in the printer's inference was seeded by the target type alone. Constructor
   * overload resolution cannot pass the target type to a poly argument, so a source that compiled
   * must have pinned those type arguments explicitly; the target type itself is the constructor
   * parameter recorded in the pool descriptor and its generic Signature. The witness is printed
   * only when every type variable settles to a concrete type.
   */
  private boolean constructorDelegationDemand(List<String> fparams, VarType ret,
                                              Map<VarType, VarType> targetSeeded, boolean isNew) {
    if (!inConstructorDelegation() || isInvocationInstance || isNew || fparams.isEmpty()
      || targetSeeded.isEmpty()) {
      return false;
    }
    Set<VarType> resultVars = new HashSet<>();
    if (ret.type == CodeType.GENVAR) {
      resultVars.add(ret.resizeArrayDim(0));
    } else if (ret.isGeneric()) {
      resultVars.addAll(((GenericType) ret).getAllGenericVars());
    } else {
      return false;
    }
    boolean demanded = false;
    for (VarType variable : resultVars) {
      if (!fparams.contains(variable.value)) {
        continue;
      }
      VarType seeded = targetSeeded.get(variable);
      if (seeded != null && seeded.equals(genericsMap.get(variable))) {
        demanded = true;
      }
    }
    if (!demanded) {
      return false;
    }
    List<VarType> probe = new ArrayList<>();
    getGenericArgs(fparams, genericsMap, probe);
    return probe.size() == fparams.size() && allConcreteTypes(probe);
  }

  /**
   * An invocation in receiver position cannot take its type arguments from the surrounding
   * target: javac types a method's receiver without one, so a type variable that only the target
   * determines is left at its default there, and an inexact method reference argument supplies no
   * constraint that could recover it. The printer's inference did use the target (the declared
   * type of the field or assignment the whole chain flows into, a class-file signature); when the
   * target determines a type variable and the printer settles every type variable of the call,
   * that is the witness a compiling source must have written. It is printed only when it contains
   * no free type variable, reproduces the method the pool recorded, and the call site is in this
   * class's own pool.
   */
  private boolean receiverTargetDemand(List<String> fparams, Map<VarType, VarType> upperBoundsMap,
                                       Map<VarType, List<VarType>> bounds) {
    if (!isInvocationInstance || fparams.isEmpty() || desc == null || desc.getSignature() == null) {
      return false;
    }
    Set<VarType> targetSeeded = new HashSet<>();
    for (String fp : fparams) {
      VarType variable = GenericType.parse("T" + fp + ";");
      VarType target = upperBoundsMap.get(variable);
      VarType inferred = genericsMap.get(variable);
      if (target == null || GenericType.DUMMY_VAR.equals(target) || inferred == null) {
        continue;
      }
      if (sameType(inferred, target)) {
        targetSeeded.add(variable);
      }
    }
    if (targetSeeded.isEmpty()) {
      return false;
    }
    // Only a variable in the contravariant (receiver) position of a method reference is
    // unrecoverable for javac: it types the receiver from the method reference's target, and an
    // unbound reference to a generic class gives it no constraint there. A variable in the
    // covariant position is inferred from the reference's recorded return type, and printing it
    // would change the inference of the surrounding chain.
    List<VarType> parameterTypes = desc.getSignature().parameterTypes;
    int count = Math.min(parameterTypes.size(), lstParameters.size());
    boolean receiverSeeded = false;
    for (int i = 0; i < count; i++) {
      if (!(lstParameters.get(i) instanceof NewExprent expr) || !expr.isMethodReference()) {
        continue;
      }
      Set<VarType> covariant = new HashSet<>();
      Set<VarType> other = new HashSet<>();
      collectVariance(parameterTypes.get(i), true, covariant, other);
      other.retainAll(targetSeeded);
      if (!other.isEmpty()) {
        receiverSeeded = true;
        break;
      }
    }
    if (!receiverSeeded) {
      return false;
    }
    List<VarType> witness = new ArrayList<>();
    getGenericArgs(fparams, genericsMap, witness);
    if (witness.size() != fparams.size()) {
      return false;
    }
    for (VarType type : witness) {
      if (!isPrintableWitness(type)) {
        return false;
      }
    }
    if (!erasureMatchesDescriptor(fparams, witness, bounds)) {
      return false;
    }
    if (!isRecordedCallSite()) {
      return false;
    }
    return true;
  }

  /**
   * A call whose type variable occurs in no recorded parameter type, so javac cannot infer it
   * from any argument. Where the call is not in a target position javac defaults such a variable
   * to its declared bound, and the recorded expected type must then reject that instantiation -
   * otherwise a source that compiled need not have pinned anything and no witness is printed.
   * The witness must itself be a type variable the source can name: a concrete instantiation
   * would freeze an inference javac still has to solve with its surrounding diamond or call
   * chain. It is used only when its erasure reproduces the call the pool recorded at this site.
   */
  private boolean returnOnlyTypeVariableDemand(List<String> fparams, VarType ret,
                                               Map<VarType, List<VarType>> bounds, VarType upperBound, boolean isNew) {
    if (isNew || fparams.isEmpty() || desc == null || desc.getSignature() == null
      || ret == null || upperBound == null
      || upperBound.type == CodeType.GENVAR || upperBound.type == CodeType.VOID) {
      return false;
    }
    // A call with arguments in receiver position is inferred by javac from those arguments;
    // only a call that takes none has no constraint but the target there.
    if (isInvocationInstance && !lstParameters.isEmpty()) {
      return false;
    }
    GenericMethodDescriptor signature = desc.getSignature();
    Set<String> mentioned = new HashSet<>();
    for (VarType parameter : signature.parameterTypes) {
      collectTypeVariables(parameter, mentioned);
    }
    Map<VarType, List<VarType>> named = getNamedGenerics();
    List<VarType> witness = new ArrayList<>(fparams.size());
    Map<VarType, VarType> defaulted = new HashMap<>();
    boolean demanded = false;
    for (int i = 0; i < fparams.size(); i++) {
      String fp = fparams.get(i);
      VarType variable = GenericType.parse("T" + fp + ";");
      boolean inferable = mentioned.contains(fp);
      if (!inferable) {
        demanded = true;
      }
      VarType value = genericsMap.get(variable);
      if (!isWitnessType(value, named)) {
        return false;
      }
      // Only a type variable the source itself can name proves a pin: a concrete instantiation
      // (or one carrying wildcards) is also what javac's own inference over the surrounding
      // diamond or call chain produces, and naming it would freeze an inference javac still
      // needs to solve together with its context.
      if (!inferable && (value.type != CodeType.GENVAR || !isInScopeTypeVariable(value, named))) {
        return false;
      }
      witness.add(value);
      List<VarType> declared = i < signature.typeParameterBounds.size()
        ? signature.typeParameterBounds.get(i) : null;
      VarType bound = declared == null || declared.isEmpty() ? VarType.VARTYPE_OBJECT : declared.get(0);
      defaulted.put(variable, bound == null ? VarType.VARTYPE_OBJECT : bound);
    }
    if (!demanded) {
      return false;
    }
    // What javac infers without a witness: every variable at its declared bound. If that
    // instantiation already fits the recorded expected type, nothing proves the source pinned it.
    VarType inferred = ret.remap(defaulted);
    if (inferred != null && satisfiesUpperBound(inferred, upperBound)) {
      return false;
    }
    if (!erasureMatchesDescriptor(fparams, witness, bounds) || !isRecordedCallSite()) {
      return false;
    }
    witnessQualifier = true;
    return true;
  }

  /** A witness position: a printable type, or a type variable that is in scope where it prints. */
  private static boolean isWitnessType(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null || type == GenericType.DUMMY_VAR) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return isInScopeTypeVariable(type, named);
    }
    return isPrintableWitness(type);
  }

  /** The names of every type variable mentioned in a recorded type. */
  private static void collectTypeVariables(VarType type, Set<String> names) {
    if (type == null) {
      return;
    }
    if (type.type == CodeType.GENVAR) {
      names.add(type.value);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        collectTypeVariables(argument, names);
      }
    }
  }

  /**
   * Whether a value the arguments alone would produce is accepted by the recorded expected type.
   * Only used to prove that no witness was needed, so a wildcard (which accepts more) counts as
   * satisfied, while a type variable outside a wildcard is an exact requirement: the position is
   * invariant and only the same variable is an instance of it.
   */
  private static boolean satisfiesUpperBound(VarType value, VarType target) {
    if (value == null || target == null) {
      return false;
    }
    if (target.type == CodeType.GENVAR) {
      // The expected type itself is a variable whose value is unknown here; it may accept it.
      return true;
    }
    if (target instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return true;
    }
    if (target.type != CodeType.OBJECT) {
      return value.equals(target);
    }
    GenericType targetGeneric = target instanceof GenericType generic ? generic : null;
    if (targetGeneric == null || targetGeneric.getArguments().isEmpty()) {
      return value.type == CodeType.OBJECT && value.value.equals(target.value)
        && (!(value instanceof GenericType valueGeneric) || valueGeneric.getArguments().isEmpty());
    }
    if (!(value instanceof GenericType valueGeneric) || !value.value.equals(target.value)) {
      return false;
    }
    List<VarType> targetArgs = targetGeneric.getArguments();
    List<VarType> valueArgs = valueGeneric.getArguments();
    if (valueArgs.size() != targetArgs.size()) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      if (!satisfiesArgument(valueArgs.get(i), targetArgs.get(i))) {
        return false;
      }
    }
    return true;
  }

  /** One invariant type-argument position: only the very same type is accepted. */
  private static boolean satisfiesArgument(VarType value, VarType target) {
    if (target == null) {
      return true; // an unbounded wildcard
    }
    if (target.type == CodeType.GENVAR) {
      return value != null && value.type == CodeType.GENVAR && value.value.equals(target.value)
        && (!(value instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO);
    }
    if (target instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return true;
    }
    return satisfiesUpperBound(value, target);
  }

  /**
   * A type that can stand as a witness: no free type variable and no raw generic class. A raw
   * rendering of a generic class is not what the recorded types say and loses the information the
   * rest of the chain was typed with; unbounded wildcards are allowed and print as {@code ?}.
   */
  private static boolean isPrintableWitness(VarType type) {
    if (type == null || type == GenericType.DUMMY_VAR || type.type == CodeType.GENVAR) {
      return false;
    }
    GenericType generic = type instanceof GenericType g ? g : null;
    if (generic != null) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      List<VarType> arguments = generic.getArguments();
      for (VarType argument : arguments) {
        if (argument != null && !isPrintableWitness(argument)) {
          return false;
        }
      }
      if (!arguments.isEmpty()) {
        return true;
      }
    }
    return type.type != CodeType.OBJECT || !isGenericClass(type.value);
  }

  /**
   * Whether a witness entry the printer could only render as a bare generic class belongs to a
   * variable that a declared parameter carries as its own direct type argument. Such an argument
   * gives javac the variable's value from its recorded type, which is always written in full, so
   * a bare witness for it can only be the printer's inference losing arguments. A variable inside
   * a wildcard or a functional interface is not fixed by the argument (javac solves it from the
   * lambda body or leaves it to the target), so those witnesses stand.
   */
  private boolean dropsRawParameterWitness(List<String> fparams) {
    if (desc == null || desc.getSignature() == null) {
      return false;
    }
    List<VarType> parameters = desc.getSignature().parameterTypes;
    for (int i = 0; i < fparams.size() && i < genericArgs.size(); i++) {
      VarType type = genericArgs.get(i);
      if (type == null || type.type != CodeType.OBJECT || type.arrayDim != 0
        || (type instanceof GenericType generic && !generic.getArguments().isEmpty())
        || !isGenericClass(type.value)) {
        continue;
      }
      VarType variable = GenericType.parse("T" + fparams.get(i) + ";");
      for (VarType parameter : parameters) {
        if (parameter instanceof GenericType generic) {
          for (VarType argument : generic.getArguments()) {
            if (variable.equals(argument)) {
              return true;
            }
          }
        }
      }
    }
    return false;
  }

  /** Whether a class name denotes a class with type parameters, so a bare name is a raw type. */
  private static boolean isGenericClass(String internalName) {
    StructClass cls = DecompilerContext.getStructContext().getClass(internalName);
    if (cls != null && cls.getSignature() != null) {
      return !cls.getSignature().fparameters.isEmpty();
    }
    if (internalName.startsWith("java/") || internalName.startsWith("javax/")) {
      try {
        return Class.forName(internalName.replace('/', '.'), false, null).getTypeParameters().length > 0;
      }
      catch (Throwable ignored) {
        // Without the class there is no evidence that the name is raw.
      }
    }
    return false;
  }

  /**
   * The wildcard-parameterised type recorded for an {@code Optional.orElse}/{@code orElseGet}
   * argument, when the argument is a variable or field whose declaration carries wildcards.
   * A read of such a declaration captures the wildcard afresh, so the value cannot be assigned
   * to a parameter fixed by an earlier capture; the recorded declaration is what the source had
   * to pin, and it is the only nameable type that makes the argument valid.
   */
  private VarType optionalWildcardArgument() {
    if (isStatic || !"java/util/Optional".equals(classname)
      || lstParameters.size() != 1 || !("orElse".equals(name) || "orElseGet".equals(name))) {
      return null;
    }
    Exprent argument = lstParameters.get(0);
    if (!(argument instanceof VarExprent) && !(argument instanceof FieldExprent)) {
      return null;
    }
    VarType declared = argument.getInferredExprType(null);
    if (declared == null || declared.type != CodeType.OBJECT || declared.arrayDim != 0
      || !declared.isGeneric() || !hasWildcardArgument((GenericType) declared)) {
      return null;
    }
    return declared;
  }

  /** The map invocation whose element type the receiver Optional exposes. */
  private InvocationExprent optionalElementMap() {
    if (!(instance instanceof InvocationExprent receiver)) {
      return null;
    }
    // DataResult.result() exposes the DataResult's element; the map that produced it is next.
    if ("com/mojang/serialization/DataResult".equals(receiver.classname) && "result".equals(receiver.name)
      && receiver.lstParameters.isEmpty() && receiver.instance instanceof InvocationExprent map) {
      return map;
    }
    return "java/util/Optional".equals(receiver.classname) && "map".equals(receiver.name) ? receiver : null;
  }

  /** Whether a type mentions a wildcard at any depth. */
  private static boolean hasWildcardArgument(GenericType type) {
    for (VarType argument : type.getArguments()) {
      if (argument == null) {
        return true;
      }
      if (argument instanceof GenericType generic
        && (generic.getWildcard() != GenericType.WILDCARD_NO || hasWildcardArgument(generic))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the demanded wildcard type can stand as this map call's explicit type argument: the
   * functional argument is a lambda whose recorded instantiated return is that same class, the
   * witness is printable, its erasure reproduces the call the pool recorded, and the call site
   * belongs to this class.
   */
  private boolean optionalMapWitness(VarType demand, List<String> fparams,
                                     Map<VarType, List<VarType>> bounds) {
    if (demand == null || fparams.size() != 1 || lstParameters.size() != 1
      || desc == null || desc.getSignature() == null
      || !("com/mojang/serialization/DataResult".equals(classname) || "java/util/Optional".equals(classname))
      || !"map".equals(name)) {
      return false;
    }
    if (!(lstParameters.get(0) instanceof NewExprent lambda) || !lambda.isLambda()
      || lambda.isMethodReference()) {
      return false;
    }
    if (demand.type != CodeType.OBJECT || demand.arrayDim != 0 || !demand.isGeneric()
      || !hasWildcardArgument((GenericType) demand) || !isPrintableWitness(demand)) {
      return false;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(lambda.getNewType().value);
    if (node == null || node.lambdaInformation == null) {
      return false;
    }
    VarType recorded = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor).ret;
    if (recorded == null || recorded.type != CodeType.OBJECT || recorded.arrayDim != 0
      || !recorded.value.equals(demand.value)) {
      return false;
    }
    return erasureMatchesDescriptor(fparams, List.of(demand), bounds) && isRecordedCallSite();
  }

  /**
   * A method reference or lambda argument whose recorded instantiated type is wider than the
   * method it names: the class file's metafactory argument then proves the source fixed the call's
   * type variables itself, because javac's plain inference from the argument would have produced
   * the method's own return type. Print the inferred (recorded) type arguments as the witness,
   * but only when every type variable is determined concretely and the erasure reproduces the
   * exact method the target recorded at this call site.
   */
  private boolean tryDemandWitness(List<String> fparams, Map<VarType, List<VarType>> bounds) {
    if (fparams.isEmpty()) {
      return false;
    }
    // Most proofs here only hold for a receiver: an argument or assignment position hands the
    // call a target, and javac may have inferred the recorded type from it. A method reference's
    // recorded return at the functional method's own position is different, see
    // recordedSettledTypes.
    boolean instancePosition = isInvocationInstance;
    List<VarType> witness = demandWitness(fparams, instancePosition);
    if (witness == null) {
      return false;
    }
    if (!erasureMatchesDescriptor(fparams, witness, bounds)) {
      return false;
    }
    if (!isRecordedCallSite()) {
      return false;
    }
    genericArgs.clear();
    genericArgs.addAll(witness);
    return true;
  }

  /**
   * A call in receiver position whose type arguments the printer cannot settle. The class file
   * records what the outer invocation's functional argument returns: the implementation method's
   * tail is a local whose LocalVariableTypeTable gives the generic type it was declared with, or
   * a field whose Signature does. The outer class's type argument is that value's supertype, and
   * the receiver returns the outer class instance, so the recorded value fixes the receiver's
   * type variables through an invariant position (Map&lt;K, V&gt; accepts exactly a Map with
   * those arguments). The witness is printed only when it is fully printable, its erasure
   * reproduces the call the pool recorded, and the call site belongs to this class.
   */
  private boolean receiverRecordedValueDemand(List<String> fparams, VarType ret,
                                              Map<VarType, List<VarType>> bounds) {
    if (!isInvocationInstance || fparams.isEmpty() || ret == null || desc == null
      || ret.type != CodeType.OBJECT || !ret.isGeneric()) {
      return false;
    }
    InvocationExprent outer = OUTER_INVOCATION.get();
    if (outer == null || outer == this || outer.desc == null || outer.desc.getSignature() == null
      || outer.lstParameters.isEmpty()) {
      return false;
    }
    StructClass outerClass = DecompilerContext.getStructContext().getClass(outer.classname);
    if (outerClass == null || outerClass.getSignature() == null
      || outerClass.getSignature().fparameters.isEmpty() || !outer.classname.equals(ret.value)) {
      return false;
    }
    List<String> classParams = outerClass.getSignature().fparameters;
    if (((GenericType) ret).getArguments().size() != classParams.size()) {
      return false;
    }
    // A variable the printer could not print is in demand. A variable it did print is in demand
    // too when the outer call's recorded value settles every type variable of this call through
    // an invariant position: the printer's value there came from the surrounding target, which
    // javac does not hand a receiver, so the source must have written the same types itself.
    List<VarType> probe = new ArrayList<>();
    getGenericArgs(fparams, genericsMap, probe);
    boolean printerComplete = probe.size() == fparams.size();
    Map<VarType, VarType> partial = new HashMap<>();
    for (String fp : fparams) {
      VarType variable = GenericType.parse("T" + fp + ";");
      VarType inferred = genericsMap.get(variable);
      if (inferred != null && isPrintableWitness(inferred)) {
        partial.put(variable, inferred);
      }
    }
    VarType receiver = ret.remap(partial);
    if (receiver == null || !receiver.isGeneric() || !outer.classname.equals(receiver.value)) {
      return false;
    }
    List<VarType> receiverArgs = ((GenericType) receiver).getArguments();
    if (receiverArgs.size() != classParams.size()) {
      return false;
    }
    Map<VarType, VarType> bindings = bindRecordedLambdaValues(outer, receiverArgs, classParams, fparams);
    if (bindings == null) {
      return false;
    }
    if (bindings.isEmpty()) {
      if (!printerComplete) {
        return false;
      }
      // The printer's values already filled every position, so the substituted comparison bound
      // nothing. Bind the unsubstituted pattern instead: the class file's recorded value then
      // supplies the witness, and it must agree with every value the printer inferred.
      List<VarType> rawArgs = ((GenericType) ret).getArguments();
      if (rawArgs.size() != classParams.size()) {
        return false;
      }
      bindings = bindRecordedLambdaValues(outer, rawArgs, classParams, fparams);
      if (bindings == null || bindings.isEmpty()) {
        return false;
      }
      for (int i = 0; i < fparams.size(); i++) {
        VarType value = bindings.get(GenericType.parse("T" + fparams.get(i) + ";"));
        if (value == null || !sameType(value, probe.get(i))) {
          return false;
        }
      }
    }
    List<VarType> witness = new ArrayList<>(fparams.size());
    for (String fp : fparams) {
      VarType variable = GenericType.parse("T" + fp + ";");
      VarType value = bindings.get(variable);
      if (value == null) {
        value = genericsMap.get(variable);
      }
      if (!isPrintableWitness(value)) {
        return false;
      }
      witness.add(value);
    }
    if (!erasureMatchesDescriptor(fparams, witness, bounds) || !isRecordedCallSite()) {
      return false;
    }
    genericArgs.clear();
    genericArgs.addAll(witness);
    return true;
  }

  /**
   * Bind a receiver's type arguments to the values the outer call's recorded functional
   * arguments return. Returns null on a contradiction between two records, so the caller can
   * reject the whole witness rather than picking one.
   */
  private static Map<VarType, VarType> bindRecordedLambdaValues(InvocationExprent outer,
      List<VarType> receiverArgs, List<String> classParams, List<String> fparams) {
    Map<VarType, VarType> bindings = new HashMap<>();
    List<VarType> declared = outer.desc.getSignature().parameterTypes;
    int count = Math.min(declared.size(), outer.lstParameters.size());
    for (int i = 0; i < count; i++) {
      if (!(outer.lstParameters.get(i) instanceof NewExprent lambda) || !lambda.isLambda()) {
        continue;
      }
      Set<VarType> covariant = new HashSet<>();
      Set<VarType> other = new HashSet<>();
      collectVariance(declared.get(i), true, covariant, other);
      for (VarType variable : covariant) {
        if (variable.type != CodeType.GENVAR) {
          continue;
        }
        int index = classParams.indexOf(variable.value);
        if (index < 0) {
          continue;
        }
        VarType recorded = recordedLambdaValueSignature(lambda);
        if (recorded == null) {
          continue;
        }
        if (!bindRecordedValue(receiverArgs.get(index), recorded, fparams, bindings)) {
          return null;
        }
      }
    }
    return bindings;
  }

  /**
   * Bind the type variables of a receiver's type argument to the arguments a recorded value type
   * supplies. The receiver's argument and the recorded value must have the same raw class, and
   * every position is compared exactly, because the position is invariant; a wildcard in the
   * receiver's argument constrains nothing. A contradiction between two records rejects the
   * whole witness rather than picking one.
   */
  private static boolean bindRecordedValue(VarType pattern, VarType recorded, List<String> fparams,
                                           Map<VarType, VarType> bindings) {
    if (pattern == null || recorded == null) {
      return false;
    }
    if (pattern.type == CodeType.GENVAR) {
      if (!fparams.contains(pattern.value) || pattern.arrayDim != 0) {
        return false;
      }
      VarType prior = bindings.putIfAbsent(pattern, recorded);
      return prior == null || sameType(prior, recorded);
    }
    if (pattern.type != CodeType.OBJECT || !pattern.isGeneric()) {
      return false;
    }
    VarType view = recorded;
    if (!pattern.value.equals(recorded.value)) {
      view = GenericType.getGenericSuperType(recorded, pattern);
      if (!(view instanceof GenericType) || !pattern.value.equals(view.value)) {
        return false;
      }
    }
    List<VarType> patternArgs = ((GenericType) pattern).getArguments();
    List<VarType> recordedArgs = ((GenericType) view).getArguments();
    if (patternArgs.size() != recordedArgs.size()) {
      return false;
    }
    for (int i = 0; i < patternArgs.size(); i++) {
      VarType p = patternArgs.get(i);
      VarType r = recordedArgs.get(i);
      if (p == null || r == null) {
        return false;
      }
      if (p.type == CodeType.GENVAR && fparams.contains(p.value)) {
        VarType prior = bindings.putIfAbsent(p.resizeArrayDim(0), r);
        if (prior != null && !sameType(prior, r)) {
          return false;
        }
      }
      else if (p instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      else if (!sameType(p, r)) {
        return false;
      }
    }
    return true;
  }

  /**
   * The generic type of the value a lambda's recorded implementation method returns, read from
   * the class file alone: the LocalVariableTypeTable signature of the local it returns, or the
   * Signature of the field it reads. An erased descriptor names no type arguments and is not
   * used. Only a single-exit method is read.
   */
  private static VarType recordedLambdaValueSignature(NewExprent lambda) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(lambda.getNewType().value);
    if (node == null) {
      return null;
    }
    StructClass content = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);
    if (content == null) {
      return null;
    }
    StructMethod method = content.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (method == null) {
      return null;
    }
    boolean released = method.getInstructionSequence() == null;
    try {
      FullInstructionSequence seq = method.getInstructionSequence();
      if (seq == null) {
        method.expandData(content);
        seq = method.getInstructionSequence();
      }
      if (seq == null || seq.length() < 2 || seq.getInstr(seq.length() - 1).opcode != CodeConstants.opc_areturn) {
        return null;
      }
      for (int i = 0; i < seq.length() - 1; i++) {
        int opcode = seq.getInstr(i).opcode;
        if (opcode == CodeConstants.opc_areturn || opcode == CodeConstants.opc_ireturn
          || opcode == CodeConstants.opc_lreturn || opcode == CodeConstants.opc_freturn
          || opcode == CodeConstants.opc_dreturn || opcode == CodeConstants.opc_return) {
          return null;
        }
      }
      Instruction value = seq.getInstr(seq.length() - 2);
      if (value.opcode == CodeConstants.opc_aload || value.opcode == CodeConstants.opc_aload_0
        || value.opcode == CodeConstants.opc_aload_1 || value.opcode == CodeConstants.opc_aload_2
        || value.opcode == CodeConstants.opc_aload_3) {
        int slot = value.opcode == CodeConstants.opc_aload ? value.operand(0) : value.opcode - CodeConstants.opc_aload_0;
        StructLocalVariableTableAttribute lvt = method.getLocalVariableAttr();
        if (lvt != null) {
          Iterator<StructLocalVariableTableAttribute.LocalVariable> variables = lvt.getVariables().iterator();
          while (variables.hasNext()) {
            StructLocalVariableTableAttribute.LocalVariable variable = variables.next();
            if (variable.getVersion().var == slot && variable.getSignature() != null
              && value.startOffset >= variable.getStart() && value.startOffset < variable.getEnd()) {
              GenericFieldDescriptor descriptor = GenericMain.parseFieldSignature(variable.getSignature());
              if (descriptor != null) {
                return descriptor.type;
              }
            }
          }
        }
        return null;
      }
      if (value.group == CodeConstants.GROUP_FIELDACCESS) {
        LinkConstant link = content.getPool().getLinkConstant(value.operand(0));
        if (link == null) {
          return null;
        }
        StructClass owner = DecompilerContext.getStructContext().getClass(link.classname);
        StructField field = owner == null ? null : owner.getField(link.elementname, link.descriptor);
        GenericFieldDescriptor descriptor = field == null ? null : field.getSignature();
        return descriptor == null ? null : descriptor.type;
      }
    }
    catch (IOException ignored) {
      // Without the method's code there is no proof.
    }
    finally {
      if (released) {
        // Reading must not leave the sequence live: printer rules that consult the current
        // method's sequence would silently start firing inside a lambda body.
        method.releaseResources();
      }
    }
    return null;
  }

  /**
   * A witness printed for a type variable that feeds a functional argument's parameter position
   * must be accepted by the method reference the class file recorded. The metafactory's
   * instantiated method type lists the concrete parameter types that reference has, and a
   * functional parameter type is only adaptable to one of their supertypes; a witness that
   * violates this cannot come from any compiling source, so it is the printer's own inference
   * and is dropped, letting javac infer the type from the argument the source passed.
   */
  private boolean witnessContradictsRecordedMethodReference() {
    if (genericArgs.isEmpty() || desc == null || desc.getSignature() == null) {
      return false;
    }
    List<String> fparams = desc.getSignature().typeParameters;
    if (fparams.size() != genericArgs.size()) {
      return false;
    }
    Map<VarType, VarType> witness = new HashMap<>();
    Set<VarType> variables = new HashSet<>();
    for (int i = 0; i < fparams.size(); i++) {
      VarType variable = GenericType.parse("T" + fparams.get(i) + ";");
      variables.add(variable);
      witness.put(variable, genericArgs.get(i));
    }
    List<VarType> declared = desc.getSignature().parameterTypes;
    int count = Math.min(declared.size(), lstParameters.size());
    for (int i = 0; i < count; i++) {
      if (!(lstParameters.get(i) instanceof NewExprent ref) || !ref.isMethodReference()) {
        continue;
      }
      if (!(declared.get(i) instanceof GenericType parameter) || parameter.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      StructClass iface = DecompilerContext.getStructContext().getClass(parameter.value);
      if (iface == null || iface.getSignature() == null) {
        continue;
      }
      List<String> ifaceParams = iface.getSignature().fparameters;
      List<VarType> actual = parameter.getArguments();
      if (actual.size() != ifaceParams.size()) {
        continue;
      }
      StructMethod sam = ExprProcessor.functionalMethod(iface);
      if (sam == null || sam.getSignature() == null) {
        continue;
      }
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(ref.getNewType().value);
      if (node == null) {
        continue;
      }
      VarType[] recorded = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor).params;
      List<VarType> samParams = sam.getSignature().parameterTypes;
      if (recorded.length != samParams.size()) {
        continue;
      }
      for (int j = 0; j < samParams.size(); j++) {
        // Only a functional parameter that is exactly one of the interface's type variables is
        // judged; a type built from one needs its own variance analysis.
        VarType samParam = samParams.get(j);
        if (samParam.type != CodeType.GENVAR || samParam.arrayDim != 0) {
          continue;
        }
        int index = ifaceParams.indexOf(samParam.value);
        if (index < 0) {
          continue;
        }
        VarType argument = actual.get(index);
        if (!variables.contains(argument)) {
          continue;
        }
        VarType substituted = argument.remap(witness);
        if (substituted == null || substituted.type != CodeType.OBJECT || substituted.arrayDim != 0) {
          continue;
        }
        if (DecompilerContext.getStructContext().getClass(substituted.value) == null
            || DecompilerContext.getStructContext().getClass(recorded[j].value) == null) {
          continue;
        }
        if (!DecompilerContext.getStructContext().instanceOf(substituted.value, recorded[j].value)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * The type arguments the class file proves for this call: the printer's own inference when a
   * recorded argument agrees with it, else the recorded metafactory type itself when it settles
   * a type variable the printer's inference placed elsewhere. Null when nothing is proven.
   */
  private List<VarType> demandWitness(List<String> fparams, boolean instancePosition) {
    if (instancePosition && recordedArgumentConstraint(fparams)) {
      List<VarType> witness = new ArrayList<>(fparams.size());
      getGenericArgs(fparams, genericsMap, witness);
      if (witness.size() == fparams.size() && allConcreteTypes(witness)) {
        return witness;
      }
    }
    Map<VarType, VarType> settled = recordedSettledTypes(fparams, instancePosition);
    if (settled.isEmpty()) {
      return null;
    }
    List<VarType> witness = new ArrayList<>(fparams.size());
    for (String fp : fparams) {
      VarType value = settled.get(GenericType.parse("T" + fp + ";"));
      if (!isConcreteType(value)) {
        return null;
      }
      witness.add(value);
    }
    return witness;
  }

  private static boolean allConcreteTypes(List<VarType> types) {
    for (VarType type : types) {
      if (!isConcreteType(type)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Type variables a functional argument's recorded metafactory instantiated type settles to a
   * concrete value. The instantiated method type is the ground target type javac used, so its
   * return type is the value of the variable feeding the return position, provided that variable
   * is the only one in a covariant position of the declared parameter type, or is the functional
   * method's own return type variable when a method reference's declared parameter spells the
   * interface's arguments without wildcards. The recorded return must widen the implementation's
   * return: only then does it prove the source constrained the variable, because plain inference
   * from the argument would have produced the narrower implementation type.
   */
  private Map<VarType, VarType> recordedSettledTypes(List<String> fparams, boolean instancePosition) {
    Map<VarType, VarType> settled = new HashMap<>();
    if (desc == null || desc.getSignature() == null || fparams.isEmpty()) {
      return settled;
    }
    Set<VarType> methodVars = fparamTypes(fparams);
    List<VarType> parameterTypes = desc.getSignature().parameterTypes;
    int count = Math.min(parameterTypes.size(), lstParameters.size());
    for (int i = 0; i < count; i++) {
      Exprent argument = lstParameters.get(i);
      if (!(argument instanceof NewExprent lambda) || !lambda.isLambda()) {
        continue;
      }
      Set<VarType> covariant = new HashSet<>();
      Set<VarType> other = new HashSet<>();
      collectVariance(parameterTypes.get(i), true, covariant, other);
      covariant.removeAll(other);
      covariant.retainAll(methodVars);
      VarType variable = null;
      boolean samReturn = false;
      if (covariant.size() == 1 && instancePosition) {
        variable = covariant.iterator().next();
      }
      else if (covariant.isEmpty() && lambda.isMethodReference()) {
        // A method reference's instantiated return is the functional method's ground return
        // type, so it fixes the type variable sitting at that position even when the declared
        // parameter spells the interface's argument without a wildcard (Function<T, U>): javac
        // infers such a variable from the referenced method's own return, so a recorded return
        // that is wider can only come from the source constraining the call. This also holds
        // outside receiver position: a call whose target is an inference variable is inferred
        // standalone, so its own arguments are the only constraints javac has.
        variable = samReturnTypeVariable(parameterTypes.get(i), methodVars, parameterTypes, i);
        samReturn = variable != null;
      }
      if (variable == null) {
        continue;
      }
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(lambda.getNewType().value);
      if (node == null) {
        continue;
      }
      VarType instantiatedRet = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor).ret;
      VarType implRet = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor).ret;
      if (instantiatedRet == null || implRet == null || implRet.type != CodeType.OBJECT || implRet.arrayDim != 0) {
        continue;
      }
      VarType recorded = null;
      if (instantiatedRet.equals(implRet) && !node.lambdaInformation.is_method_reference) {
        // A lambda's synthetic method is generated with the ground target type javac chose. When
        // the value the method itself returns is a proper subtype of that recorded return, plain
        // inference from the body would have produced the narrower type, so the source pinned the
        // variable to the wider one (a witness, or an equally byte-neutral cast in the body).
        VarType bodyRet = recordedLambdaValueType(node);
        if (bodyRet != null && bodyRet.type == CodeType.OBJECT && bodyRet.arrayDim == 0
            && !bodyRet.equals(implRet)
            && DecompilerContext.getStructContext().instanceOf(bodyRet.value, implRet.value)
            && isConcreteType(implRet)) {
          recorded = implRet;
        }
      }
      if (recorded == null
          && !instantiatedRet.equals(implRet)
          && instantiatedRet.type == CodeType.OBJECT
          && instantiatedRet.arrayDim == 0
          && DecompilerContext.getStructContext().instanceOf(implRet.value, instantiatedRet.value)
          && isConcreteType(instantiatedRet)) {
        recorded = instantiatedRet;
      }
      // A metafactory record carries erasure only, so the value it settles a SAM return variable
      // to can be a bare generic class (a referenced method returning Holder.Reference widens to
      // Holder). A witness the printer can only render raw names a different type, and the call
      // is then left to javac.
      if (recorded == null || (samReturn && !isPrintableWitness(recorded))) {
        continue;
      }
      VarType prior = settled.putIfAbsent(variable, recorded);
      if (prior != null && !sameType(prior, recorded)) {
        return new HashMap<>();
      }
    }
    return settled;
  }

  /**
   * The method type variable at the functional method's return position, when that position is
   * exactly one of the interface's type variables and the variable occurs only once in the
   * declared parameter type and nowhere in the call's other parameters. Anywhere else it would
   * also constrain an argument position, which the recorded return does not settle.
   */
  private VarType samReturnTypeVariable(VarType declared, Set<VarType> methodVars,
                                        List<VarType> parameterTypes, int index) {
    if (!(declared instanceof GenericType parameter) || parameter.getWildcard() != GenericType.WILDCARD_NO) {
      return null;
    }
    StructClass iface = DecompilerContext.getStructContext().getClass(parameter.value);
    if (iface == null || iface.getSignature() == null) {
      return null;
    }
    List<String> ifaceParams = iface.getSignature().fparameters;
    List<VarType> actual = parameter.getArguments();
    if (actual.size() != ifaceParams.size()) {
      return null;
    }
    StructMethod sam = ExprProcessor.functionalMethod(iface);
    if (sam == null || sam.getSignature() == null) {
      return null;
    }
    VarType samRet = sam.getSignature().returnType;
    // A return type built from a variable (List<R>) would need its own variance analysis.
    if (samRet == null || samRet.type != CodeType.GENVAR || samRet.arrayDim != 0) {
      return null;
    }
    int position = ifaceParams.indexOf(samRet.value);
    if (position < 0 || position >= actual.size()) {
      return null;
    }
    VarType variable = actual.get(position);
    if (variable == null || variable.type != CodeType.GENVAR || !methodVars.contains(variable)
        || countGenvar(declared, variable) != 1) {
      return null;
    }
    for (int other = 0; other < parameterTypes.size(); other++) {
      if (other != index && countGenvar(parameterTypes.get(other), variable) != 0) {
        return null;
      }
    }
    return variable;
  }

  private static int countGenvar(VarType type, VarType variable) {
    if (type == null) {
      return 0;
    }
    if (type.type == CodeType.GENVAR) {
      return type.equals(variable) ? 1 : 0;
    }
    if (type instanceof GenericType generic) {
      int total = 0;
      for (VarType argument : generic.getArguments()) {
        total += countGenvar(argument, variable);
      }
      return total;
    }
    return 0;
  }

  /**
   * The type of the value a lambda's recorded implementation method returns, read from the class
   * file alone. Only a single-exit method whose returned value comes straight from an invocation
   * or a field read is judged; any other shape has no simple recorded producer type.
   */
  private static VarType recordedLambdaValueType(ClassNode node) {
    StructClass content = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);
    if (content == null) {
      return null;
    }
    StructMethod method = content.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (method == null) {
      return null;
    }
    boolean released = method.getInstructionSequence() == null;
    try {
      FullInstructionSequence seq = method.getInstructionSequence();
      if (seq == null) {
        method.expandData(content);
        seq = method.getInstructionSequence();
      }
      if (seq == null || seq.length() < 2 || seq.getInstr(seq.length() - 1).opcode != CodeConstants.opc_areturn) {
        return null;
      }
      for (int i = 0; i < seq.length() - 1; i++) {
        int opcode = seq.getInstr(i).opcode;
        if (opcode == CodeConstants.opc_areturn || opcode == CodeConstants.opc_ireturn
            || opcode == CodeConstants.opc_lreturn || opcode == CodeConstants.opc_freturn
            || opcode == CodeConstants.opc_dreturn || opcode == CodeConstants.opc_return) {
          return null;
        }
      }
      Instruction value = seq.getInstr(seq.length() - 2);
      if (value.group == CodeConstants.GROUP_INVOCATION) {
        LinkConstant link = content.getPool().getLinkConstant(value.operand(0));
        return link == null ? null : MethodDescriptor.parseDescriptor(link.descriptor).ret;
      }
      if (value.group == CodeConstants.GROUP_FIELDACCESS) {
        LinkConstant link = content.getPool().getLinkConstant(value.operand(0));
        return link == null ? null : new VarType(link.descriptor);
      }
    }
    catch (IOException ignored) {
      // Without the method's code there is no proof.
    }
    finally {
      if (released) {
        // Reading must not leave the sequence live: printer rules that consult the current
        // method's sequence would silently start firing inside a lambda body.
        method.releaseResources();
      }
    }
    return null;
  }

  /**
   * Collect the type variables of a declared type by position: those under a covariant
   * ({@code ? extends}) wildcard, and everyone else. A variable not under such a wildcard could
   * feed either the function's parameter or its return, so it cannot be told apart.
   */
  private static void collectVariance(VarType type, boolean covariant,
                                      Set<VarType> covariantVars, Set<VarType> otherVars) {
    if (type == null) {
      return;
    }
    if (type.type == CodeType.GENVAR) {
      (covariant ? covariantVars : otherVars).add(type);
      return;
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (argument == null) {
          continue;
        }
        int wildcard = argument instanceof GenericType ? ((GenericType) argument).getWildcard() : GenericType.WILDCARD_NO;
        if (wildcard == GenericType.WILDCARD_EXTENDS) {
          collectVariance(argument, covariant, covariantVars, otherVars);
        } else if (wildcard == GenericType.WILDCARD_UNBOUND) {
          continue;
        } else {
          collectVariance(argument, false, covariantVars, otherVars);
        }
      }
    }
  }

  /**
   * Whether an argument is a functional expression whose recorded metafactory instantiated type
   * widens the implementation method's return type at a position fed by a method type variable.
   * That widening can only come from a source-level constraint on the call's type arguments.
   */
  private boolean recordedArgumentConstraint(List<String> fparams) {
    if (desc == null || desc.getSignature() == null) {
      return false;
    }
    List<VarType> parameterTypes = desc.getSignature().parameterTypes;
    int count = Math.min(parameterTypes.size(), lstParameters.size());
    for (int i = 0; i < count; i++) {
      Exprent argument = lstParameters.get(i);
      if (!(argument instanceof NewExprent lambda) || !lambda.isLambda()) {
        continue;
      }
      Set<VarType> mentioned = new HashSet<>();
      collectGenvars(parameterTypes.get(i), mentioned);
      mentioned.retainAll(fparamTypes(fparams));
      if (mentioned.isEmpty()) {
        continue;
      }
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(lambda.getNewType().value);
      if (node == null) {
        continue;
      }
      VarType instantiatedRet = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor).ret;
      VarType implRet = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor).ret;
      if (instantiatedRet == null || implRet == null || instantiatedRet.equals(implRet)) {
        continue;
      }
      if (instantiatedRet.type != CodeType.OBJECT || implRet.type != CodeType.OBJECT
          || instantiatedRet.arrayDim != 0 || implRet.arrayDim != 0
          || !DecompilerContext.getStructContext().instanceOf(implRet.value, instantiatedRet.value)) {
        continue;
      }
      // The widening must be the recorded value of one of the type variables it feeds.
      for (VarType variable : mentioned) {
        VarType inferred = genericsMap.get(variable);
        if (inferred != null && isConcreteType(inferred) && sameType(inferred, instantiatedRet)) {
          return true;
        }
      }
    }
    return false;
  }

  private static Set<VarType> fparamTypes(List<String> fparams) {
    Set<VarType> types = new HashSet<>();
    for (String fp : fparams) {
      types.add(GenericType.parse("T" + fp + ";"));
    }
    return types;
  }

  private static void collectGenvars(VarType type, Set<VarType> out) {
    if (type == null) {
      return;
    }
    if (type.type == CodeType.GENVAR) {
      out.add(type);
      return;
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        collectGenvars(argument, out);
      }
    }
  }

  private static boolean sameType(VarType a, VarType b) {
    if (a instanceof GenericType generic) {
      return generic.equalsExact(b);
    }
    return b != null && !(b instanceof GenericType) && a.equals(b);
  }

  /** A type with no free type variable, wildcard or unbound argument anywhere inside it. */
  private static boolean isConcreteType(VarType type) {
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
      if (!isConcreteType(argument)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Substituting the witness into the declared generic signature and erasing must reproduce the
   * descriptor the pool recorded for the call; otherwise the witness names a different method.
   */
  private boolean erasureMatchesDescriptor(List<String> fparams, List<VarType> witness,
                                           Map<VarType, List<VarType>> bounds) {
    if (desc == null || desc.getSignature() == null) {
      return false;
    }
    Map<VarType, VarType> substitution = new HashMap<>();
    for (int i = 0; i < fparams.size(); i++) {
      substitution.put(GenericType.parse("T" + fparams.get(i) + ";"), witness.get(i));
    }
    List<VarType> parameters = desc.getSignature().parameterTypes;
    if (parameters.size() != descriptor.params.length) {
      return false;
    }
    for (int i = 0; i < parameters.size(); i++) {
      VarType erased = erase(parameters.get(i), substitution, bounds, new HashSet<>());
      if (erased == null || !erased.equals(descriptor.params[i])) {
        return false;
      }
    }
    VarType erasedRet = erase(desc.getSignature().returnType, substitution, bounds, new HashSet<>());
    return erasedRet != null && erasedRet.equals(descriptor.ret);
  }

  private static VarType erase(VarType type, Map<VarType, VarType> substitution,
                               Map<VarType, List<VarType>> bounds, Set<VarType> seen) {
    if (type == null) {
      return null;
    }
    if (type.type == CodeType.GENVAR) {
      VarType substituted = substitution.get(type);
      if (substituted != null) {
        return substituted.resizeArrayDim(substituted.arrayDim + type.arrayDim);
      }
      List<VarType> declared = bounds.get(type);
      if (declared != null && !declared.isEmpty() && seen.add(type)) {
        VarType erased = erase(declared.get(0), substitution, bounds, seen);
        seen.remove(type);
        if (erased != null) {
          return erased.resizeArrayDim(erased.arrayDim + type.arrayDim);
        }
      }
      return new VarType(CodeType.OBJECT, type.arrayDim, "java/lang/Object");
    }
    if (type.type == CodeType.OBJECT) {
      // Erasure drops type arguments and wildcards.
      return new VarType(CodeType.OBJECT, type.arrayDim, type.value);
    }
    return type;
  }

  /**
   * Whether the pool of the class being printed holds the method reference for this call and the
   * call site's own instruction points at it. Only a call the class file records can take a witness.
   */
  boolean isRecordedCallSite() {
    if (invocationType != InvocationType.VIRTUAL && invocationType != InvocationType.SPECIAL
        && invocationType != InvocationType.STATIC && invocationType != InvocationType.INTERFACE) {
      return false;
    }
    ClassNode node = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    if (node == null || bytecode == null || bytecode.isEmpty()) {
      return false;
    }
    StructClass cl = node.classStruct;
    ConstantPool pool = cl.getPool();
    boolean inPool = false;
    for (PooledConstant constant : pool.getPool()) {
      if (constant instanceof LinkConstant link
          && (link.type == CodeConstants.CONSTANT_Methodref || link.type == CodeConstants.CONSTANT_InterfaceMethodref)
          && classname.equals(link.classname) && name.equals(link.elementname)
          && stringDescriptor.equals(link.descriptor)) {
        inPool = true;
        break;
      }
    }
    if (!inPool) {
      return false;
    }
    StructMethod method = RoundTrip.currentMethod();
    if (method == null) {
      return false;
    }
    boolean released = method.getInstructionSequence() == null;
    try {
      FullInstructionSequence seq = method.getInstructionSequence();
      if (seq == null) {
        method.expandData(cl);
        seq = method.getInstructionSequence();
      }
      if (seq == null) {
        return false;
      }
      for (int offset = bytecode.nextSetBit(0); offset >= 0; offset = bytecode.nextSetBit(offset + 1)) {
        Integer index = seq.offsetToIndex().get(offset);
        if (index == null) {
          continue;
        }
        Instruction instruction = seq.getInstr(index);
        if (instruction.group != CodeConstants.GROUP_INVOCATION) {
          continue;
        }
        // A lifted initializer's offsets can name a position that is not this method's call in
        // the class's own pool; only a link constant there can be the recorded method.
        int operand = instruction.operand(0);
        if (operand <= 0 || operand >= pool.getPool().size()
          || !(pool.getConstant(operand) instanceof LinkConstant link)) {
          continue;
        }
        if (classname.equals(link.classname) && name.equals(link.elementname)
            && stringDescriptor.equals(link.descriptor)) {
          return true;
        }
      }
    } catch (IOException ignored) {
      return false;
    }
    finally {
      if (released) {
        // Reading must not leave the sequence live: printer rules that consult the current
        // method's sequence would silently start firing after this check.
        method.releaseResources();
      }
    }
    return false;
  }

  public List<VarType> getGenericArgs() {
    return genericArgs;
  }

  public Map<VarType, VarType> getGenericsMap() {
    return genericsMap;
  }

  public StructMethod getDesc() {
    if (desc == null) {
      StructClass cl = DecompilerContext.getStructContext().getClass(classname);
      desc = cl != null ? cl.getMethodRecursive(name, stringDescriptor) : null;
    }
    return desc;
  }

  public void setInvocationInstance() {
    isInvocationInstance = true;
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, lstParameters);
    measureBytecode(values, instance);
    measureBytecode(values);
  }

  public InvocationExprent markWasLazyCondy() {
    wasLazyCondy = true;
    return this;
  }

  @Override
  public void processSforms(SFormsConstructor sFormsConstructor, VarMapHolder varMaps, Statement stat, boolean calcLiveVars) {
    super.processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

    if (sFormsConstructor.trackFieldVars) {
      varMaps.getNormal().removeAllFields();
    }
  }

  // *****************************************************************************
  // IMatchable implementation
  // *****************************************************************************

  @Override
  public boolean match(MatchNode matchNode, MatchEngine engine) {
    if (!super.match(matchNode, engine)) {
      return false;
    }

    return matchNode.iterateRules((key, value) -> {
      if (key == MatchProperties.EXPRENT_PARAMETER) {
        return !value.isVariable() || (value.parameter < lstParameters.size() &&
          engine.checkAndSetVariableValue(value.value.toString(), lstParameters.get(value.parameter)));
      } else if (key == MatchProperties.EXPRENT_INVOCATION_CLASS) {
        return value.value.equals(this.classname);
      } else if (key == MatchProperties.EXPRENT_INVOCATION_SIGNATURE) {
        return value.value.equals(this.name + this.stringDescriptor);
      } else if (key == MatchProperties.EXPRENT_NAME) {
        return value.value.equals(this.name);
      }

      return true;
    });
  }

  protected static class BoxState {
    private boolean forceBoxing = false;
    private boolean forceUnboxing = false;
    private boolean keepCast = false;
  }
}

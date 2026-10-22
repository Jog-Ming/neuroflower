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
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
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
  private VarType remappedInstType = null;
  public boolean forceGenericQualfication = false;
  private final NullableConcurrentHashMap<VarType, VarType> genericsMap = new NullableConcurrentHashMap<>();
  private boolean isInvocationInstance = false;
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
                  if (to.type == CodeType.GENVAR && named.containsKey(from) && bounds.containsKey(from) && bounds.get(from).contains(VarType.VARTYPE_OBJECT) && !bounds.containsKey(to)) {
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
          // don't want the casted type
          if (instance instanceof FunctionExprent && ((FunctionExprent)instance).getFuncType() == FunctionType.CAST) {
            instType = ((FunctionExprent)instance).getLstOperands().get(0).getInferredExprType(instUB);
          }
          else {
            instType = instance.getInferredExprType(instUB);
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

            if (!suppress || DecompilerContext.getOption(IFernflowerPreferences.EXPLICIT_GENERIC_ARGUMENTS)) {
              getGenericArgs(fparams, genericsMap, genericArgs);
              if (genericArgs.isEmpty() && !isNew
                && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)) {
                // The printer's inference has no value for some type variable; an argument's
                // recorded metafactory type may still prove what the source passed.
                tryDemandWitness(fparams, bounds);
              }
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
      if (node == null || !classname.equals(node.classStruct.qualifiedName)) {
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
          VarType rightType = instance.getInferredExprType(leftType);

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
          TextBuffer res = instance.toJava(indent);

          ClassNode instNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
          // Don't cast to anonymous classes, since they by definition can't have a name
          // TODO: better fix may be to change equals to isSuperSet? all anonymous classes are superset of Object
          if (rightType.equals(VarType.VARTYPE_OBJECT) && !leftType.equals(rightType) && (instNode != null && instNode.type != ClassNode.Type.ANONYMOUS)) {
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

          VarType type = desc.getSignature().parameterTypes.get(y++).remap(hierarchyMap).remap(genericsMap);
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
    if (!lstParameters.isEmpty()) {
      buf.pushNewlineGroup(indent, 1);
      int callLine = RoundTrip.sourceLineEnd(this);
      int firstLine = start < lstParameters.size() ? RoundTrip.sourceLine(lstParameters.get(start)) : -1;
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
        ExprProcessor.getCastedExprent(lstParameters.get(i), types[i], buff, indent, ambiguous ? ExprProcessor.NullCastType.CAST : ExprProcessor.NullCastType.DONT_CAST_AT_ALL, ambiguous, true, true);

        int line = RoundTrip.sourceLine(lstParameters.get(i));
        // Only a later line is a break the original had; an equal or earlier one is inheritance
        // from the enclosing statement's marker.
        boolean forced = !firstParameter && line >= 0 && previousLine >= 0 && line > previousLine;

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
      int callLine = RoundTrip.sourceLineEnd(this);
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
    if (VarType.VARTYPE_NULL.equals(to) || (to != null && to.type == CodeType.GENVAR && !named.containsKey(to))) {
      return false;
    }

    VarType current = genericsMap.get(from);
    if (!genericsMap.containsKey(from)) {
      putGenericMapping(from, to, named, bounds);

      return true;
    } else if (to != null && current != null && !to.equals(current)) {
      if (named.containsKey(current)) {
        return false;
      }

      if (current.type != CodeType.GENVAR && to.type == CodeType.GENVAR) {
        if (named.containsKey(to)) {
          VarType bound = named.get(to).get(0);
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

    if (to == null || (to.type == CodeType.GENVAR && !named.containsKey(to))) {
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

    List<VarType> toVerify = (to.type == CodeType.GENVAR) ? named.get(to) : Collections.singletonList(to);

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
   * A method reference or lambda argument whose recorded instantiated type is wider than the
   * method it names: the class file's metafactory argument then proves the source fixed the call's
   * type variables itself, because javac's plain inference from the argument would have produced
   * the method's own return type. Print the inferred (recorded) type arguments as the witness,
   * but only when every type variable is determined concretely and the erasure reproduces the
   * exact method the target recorded at this call site.
   */
  private boolean tryDemandWitness(List<String> fparams, Map<VarType, List<VarType>> bounds) {
    if (fparams.isEmpty() || !isInvocationInstance) {
      return false;
    }
    List<VarType> witness = demandWitness(fparams);
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
  private List<VarType> demandWitness(List<String> fparams) {
    if (recordedArgumentConstraint(fparams)) {
      List<VarType> witness = new ArrayList<>(fparams.size());
      getGenericArgs(fparams, genericsMap, witness);
      if (witness.size() == fparams.size() && allConcreteTypes(witness)) {
        return witness;
      }
    }
    Map<VarType, VarType> settled = recordedSettledTypes(fparams);
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
   * is the only one in a covariant position of the declared parameter type. The recorded return
   * must widen the implementation's return: only then does it prove the source constrained the
   * variable, because plain inference from the argument would have produced the narrower
   * implementation type.
   */
  private Map<VarType, VarType> recordedSettledTypes(List<String> fparams) {
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
      if (covariant.size() != 1) {
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
      if (recorded == null) {
        continue;
      }
      VarType variable = covariant.iterator().next();
      VarType prior = settled.putIfAbsent(variable, recorded);
      if (prior != null && !sameType(prior, recorded)) {
        return new HashMap<>();
      }
    }
    return settled;
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
  private boolean isRecordedCallSite() {
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
        LinkConstant link = pool.getLinkConstant(instruction.operand(0));
        if (link != null && classname.equals(link.classname) && name.equals(link.elementname)
            && stringDescriptor.equals(link.descriptor)) {
          return true;
        }
      }
    } catch (IOException ignored) {
      return false;
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

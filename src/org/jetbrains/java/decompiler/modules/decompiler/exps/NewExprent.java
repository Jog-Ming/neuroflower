// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.io.IOException;
import java.util.*;

public class NewExprent extends Exprent {
  private InvocationExprent constructor;
  private final VarType newType;
  private final List<Exprent> lstDims;
  private List<Exprent> lstArrayElements = new ArrayList<>();
  private boolean directArrayInit;
  private boolean isVarArgParam;
  private boolean anonymous;
  private boolean lambda;
  private boolean methodReference = false;
  // Printed as the receiver of a call or field access: a receiver has no target type.
  private boolean isQualifier;

  private boolean enumConst;
  private List<VarType> genericArgs = new ArrayList<>();
  private VarType inferredLambdaType = null;
  // Set when the lambda's interface type came from the wildcard form of the called method's
  // parameter type rather than from resolved arguments; only an in-scope type variable return
  // is used from such a target.
  private boolean wildcardTargetLambda = false;
  // Type arguments the class file proved for a constructor call whose diamond javac would
  // otherwise close on a narrower type than the recorded method reference needs.
  private List<VarType> forcedConstructorArgs;
  // The recovered arguments are subtypes of what the expected type needs at an invariant
  // position: only a diamond can let javac infer the expected arguments from the target.
  private boolean targetedDiamond;
  // A diamond whose recorded target is a parameterized supertype: the arguments implied by
  // that supertype's instantiation are the ones the source wrote on the constructor.
  private List<VarType> impliedConstructorArgs;

  public NewExprent(VarType newType, ListStack<Exprent> stack, int arrayDim, BitSet bytecodeOffsets) {
    this(newType, getDimensions(arrayDim, stack), bytecodeOffsets);
  }

  public NewExprent(VarType newType, List<Exprent> lstDims, BitSet bytecodeOffsets) {
    super(Type.NEW);
    this.newType = newType;
    this.lstDims = lstDims;

    anonymous = false;
    lambda = false;
    if (newType.type == CodeType.OBJECT && newType.arrayDim == 0) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
      if (node != null && (node.type == ClassNode.Type.ANONYMOUS || node.type == ClassNode.Type.LAMBDA)) {
        anonymous = true;
        if (node.type == ClassNode.Type.LAMBDA) {
          lambda = true;
          methodReference = node.lambdaInformation.is_method_reference;
        }
      }
    }

    addBytecodeOffsets(bytecodeOffsets);
  }

  private static List<Exprent> getDimensions(int arrayDim, ListStack<Exprent> stack) {
    List<Exprent> lstDims = new ArrayList<>();
    for (int i = 0; i < arrayDim; i++) {
      lstDims.add(0, stack.pop());
    }
    return lstDims;
  }

  @Override
  public VarType getExprType() {
    return anonymous ? DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value).anonymousClassType : newType;
  }

  @Override
  public VarType getInferredExprType(VarType upperBound) {
    genericArgs.clear();
    if (!lambda && newType.type == CodeType.OBJECT) {
      StructClass node = DecompilerContext.getStructContext().getClass(newType.value);

      if (node != null && node.getSignature() != null) {
        if (anonymous) {
          if (VarType.VARTYPE_OBJECT.equals(node.getSignature().superclass) && !node.getSignature().superinterfaces.isEmpty()) {
            return node.getSignature().superinterfaces.get(0);
          }
          return node.getSignature().superclass;
        }
        else if (newType.arrayDim == 0 && !node.getSignature().fparameters.isEmpty()) {
          GenericClassDescriptor sig = node.getSignature();
          if (constructor != null) {
            InvocationExprent.enterPoly();
            VarType ret;
            try {
              ret = constructor.getInferredExprType(upperBound);
            } finally {
              InvocationExprent.exitPoly();
            }
            if (expectsWiderArguments(upperBound)) {
              targetedDiamond = true;
            }
            List<VarType> recovered = constructor.getGenericArgs();
            boolean diamond = recovered.isEmpty()
              || (recovered.size() == 1 && recovered.get(0) == GenericType.DUMMY_VAR);
            if (diamond && InvocationExprent.isLambdaBody(this)) {
              List<VarType> implied = impliedArguments(upperBound);
              if (implied != null) {
                impliedConstructorArgs = implied;
              }
            }
            return ret.type != CodeType.VOID ? ret : getExprType();
          }
          else {
            Map<VarType, VarType> genericsMap = new HashMap<>();
            this.gatherGenerics(upperBound, sig.genericType, genericsMap);
            this.getGenericArgs(sig.fparameters, genericsMap, genericArgs);
            VarType _new = sig.genericType.remap(genericsMap);
            if (sig.genericType != _new) {
              return _new;
            }
          }
        }
      }
      else if (newType.arrayDim > 0 && !lstArrayElements.isEmpty() && newType.value.equals(VarType.VARTYPE_OBJECT.value)) {
        VarType first = lstArrayElements.get(0).getInferredExprType(null);
        if (first.type == CodeType.GENVAR) {
          boolean matches = true;
          for (int i = 1; i < lstArrayElements.size(); ++i) {
            VarType type = lstArrayElements.get(i).getInferredExprType(null);
            if (!type.equals(first)) {
              matches = false;
              break;
            }
          }
          if (matches) {
            return first.resizeArrayDim(newType.arrayDim);
          }
        }
      }
    }

    if (lambda) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);

      if (node != null) {

        VarType classType = node.anonymousClassType;
        StructClass cls = DecompilerContext.getStructContext().getClass(classType.value);
        MethodDescriptor desc = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);
        StructClass methodCls = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);

        if (cls != null && cls.getSignature() != null && methodCls != null) {
          StructMethod refMethod = cls.getMethod(getLambdaMethodKey());
          StructMethod method = methodCls.getMethod(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);

          if (method != null && refMethod != null && refMethod.getSignature() != null) {
            GenericType ret = cls.getSignature().genericType;

            HashMap<VarType, VarType> genericsMap = new HashMap<>();
            Map<VarType, List<VarType>> named = getNamedGenerics();

            gatherGenerics(upperBound, ret, genericsMap);

            HashMap<VarType, VarType> instanceMap = new HashMap<>();
            if (isMethodReference() && methodCls.getSignature() != null) {
              VarType first = ret.getArguments().get(0);
              if (constructor.getInstance() != null) {
                VarType instanceType = constructor.getInstance().getInferredExprType(null);
                if (instanceType.isGeneric()) {
                  methodCls.getSignature().genericType.mapGenVarsTo((GenericType)instanceType, instanceMap);
                }
              }
              else if (method.getSignature() != null) {
                for (int i = 0; i < method.getSignature().parameterTypes.size(); ++i) {
                  VarType mtype = method.getSignature().parameterTypes.get(i);
                  VarType rtype = refMethod.getSignature().parameterTypes.get(i);
                  if (mtype.type == CodeType.GENVAR && rtype.type == CodeType.GENVAR) {
                    if (genericsMap.containsKey(rtype)) {
                      instanceMap.put(mtype, genericsMap.get(rtype));
                    }
                  }
                }
              }
            }

            // generated lambda methods have no generic info, so only map to generic var parameters
            List<VarType> types = method.getSignature() != null ? method.getSignature().parameterTypes : Arrays.asList(desc.params);
            for (int i = 0; i < types.size(); ++i) {
              List<VarType> parameterTypes = refMethod.getSignature().parameterTypes;
              if (i < parameterTypes.size() && parameterTypes.get(i).type == CodeType.GENVAR) {
                if (!genericsMap.containsKey(parameterTypes.get(i))) {
                  VarType realType = types.get(i);
                  StructClass typeCls = DecompilerContext.getStructContext().getClass(realType.value);
                  if (typeCls != null && typeCls.getSignature() != null && !realType.equals(typeCls.getSignature().genericType)) {
                    realType = typeCls.getSignature().genericType.resizeArrayDim(realType.arrayDim);
                  }
                  genericsMap.put(parameterTypes.get(i), realType);
                }
              }
            }

            if (refMethod.getSignature().returnType.type == CodeType.GENVAR) {
              VarType key = refMethod.getSignature().returnType;
              if (method.getName().equals(CodeConstants.INIT_NAME)) {
                if (methodCls.getSignature() != null) {
                  genericsMap.put(key, methodCls.getSignature().genericType);
                }
                else {
                  genericsMap.put(key, GenericType.parse("L" + methodCls.qualifiedName + ";"));
                }
              }
              else if (method.getSignature() != null || !desc.ret.equals(VarType.VARTYPE_OBJECT)) {
                VarType current = genericsMap.get(key);
                VarType returnType = method.getSignature() != null ? method.getSignature().returnType.remap(instanceMap) : desc.ret;
                StructClass retCls = returnType == null ? null : DecompilerContext.getStructContext().getClass(returnType.value);

                if (!isMethodReference() && retCls != null && retCls.getSignature() != null && !retCls.getSignature().genericType.equalsExact(returnType)) {
                  VarType retUB = current != null && current.equals(returnType) ? current : returnType;
                  VarType realType = getLambdaReturnType(node, refMethod, retUB, genericsMap);
                  if (realType != null) {
                    returnType = realType;
                  }
                }

                boolean add = current == null || returnType == null || returnType.isGeneric() ||
                  (!returnType.equals(genericsMap.get(key)) && (current.type != CodeType.GENVAR || !named.containsKey(current)));
                if (add) {
                  VarType prior = genericsMap.get(key);
                  boolean addToMap = true;
                  if (prior != null) {
                    if (prior.isGeneric() && !((GenericType)prior).isTypeUnfinished() && DecompilerContext.getStructContext().instanceOf(returnType.value, prior.value)) {
                      addToMap = false;
                    }
                  }

                  if (addToMap) {
                    genericsMap.put(key, returnType);
                  }
                }
              }
            }

            ret.getAllGenericVars().forEach(from -> {
              genericsMap.putIfAbsent(from, GenericType.DUMMY_VAR);
            });

            if (!genericsMap.isEmpty()) {
              VarType _new = ret.remap(genericsMap);
              if (_new != ret) {
                if (!_new.isGeneric() || !((GenericType)_new).hasUnknownGenericType(named.keySet())) {
                  inferredLambdaType = _new;
                  wildcardTargetLambda = false;
                }
                else if (inferredLambdaType == null && _new.isGeneric()
                  && _new.value.equals(classType.value) && cls.getSignature() != null) {
                  // The target still names the functional interface the lambda was built for,
                  // even though a wildcard in it leaves a variable unresolved. The interface's
                  // recorded SAM return type is then the target of the body's returns.
                  inferredLambdaType = _new;
                  wildcardTargetLambda = true;
                }
                return _new;
              }
            }
          }
        }
        else {
          inferredLambdaType = classType;
          wildcardTargetLambda = false;
        }
        // The expected type of a functional argument is often the wildcard form the called
        // method declares (Function<? super T, ? extends R>); the mapping above cannot bind
        // the interface's variables through the wildcards, but that recorded type still says
        // which interface and which arguments the lambda was built for. Keep it so the body's
        // target type comes from the class file's signature rather than from nowhere.
        if (inferredLambdaType == null && upperBound != null && upperBound.isGeneric()
          && upperBound.value.equals(classType.value) && cls != null && cls.getSignature() != null) {
          inferredLambdaType = upperBound;
          wildcardTargetLambda = true;
        }
      }
    }

    return getExprType();
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    if (newType.arrayDim != 0) {
      for (Exprent dim : lstDims) {
        result.addExprLowerBound(dim, VarType.VARTYPE_BYTECHAR);
        result.addExprUpperBound(dim, VarType.VARTYPE_INT);
      }

      if (newType.arrayDim == 1) {
        VarType leftType = newType.decreaseArrayDim();
        for (Exprent element : lstArrayElements) {
          result.addExprLowerBound(element, VarType.findFamilyBottom(leftType.typeFamily));
          result.addExprUpperBound(element, leftType);
        }
      }
    }
    else if (constructor != null) {
      return constructor.checkExprTypeBounds();
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    if (newType.arrayDim != 0) {
      lst.addAll(lstDims);
      lst.addAll(lstArrayElements);
    }
    else if (constructor != null) {
      Exprent constructor = this.constructor.getInstance();
      if (constructor != null) { // should be true only for a lambda expression with a virtual content method
        lst.add(constructor);
      }
      lst.addAll(this.constructor.getLstParameters());
    }

    return lst;
  }

  @Override
  public Exprent copy() {
    List<Exprent> lst = new ArrayList<>();
    for (Exprent expr : lstDims) {
      lst.add(expr.copy());
    }

    NewExprent ret = new NewExprent(newType, lst, bytecode);
    ret.setConstructor(constructor == null ? null : (InvocationExprent)constructor.copy());
    ret.setLstArrayElements(DecHelper.copyExprentList(lstArrayElements));
    ret.setDirectArrayInit(directArrayInit);
    ret.setAnonymous(anonymous);
    ret.setEnumConst(enumConst);
    return ret;
  }

  @Override
  public int getPrecedence() {
    return 1; // precedence of new
  }

  /** An expression kind whose line table entry is its own, not inherited from the statement. */
  private static boolean hasOwnLine(Exprent element) {
    return element instanceof InvocationExprent || element instanceof NewExprent
      || element instanceof FunctionExprent;
  }

  /** An element whose first token is on its own line: not a chained call's later qualifier. */
  private static boolean startsOnItsLine(Exprent element) {
    if (element instanceof InvocationExprent invocation && invocation.getInstance() != null) {
      int receiver = RoundTrip.sourceLine(invocation.getInstance());
      int call = RoundTrip.sourceLine(invocation);
      return receiver < 0 || call < 0 || receiver == call;
    }
    return true;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    if (anonymous) {
      ClassNode child = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);

      boolean selfReference = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE) == child;

      // IDEA-204310 - avoid backtracking later on for lambdas (causes spurious imports)
      if (!enumConst && (!lambda || DecompilerContext.getOption(IFernflowerPreferences.LAMBDA_TO_ANONYMOUS_CLASS))) {
        TextBuffer enclosing = null;

        if (!lambda && constructor != null) {
          enclosing = getQualifiedNewInstance(child.anonymousClassType.value, constructor.getLstParameters(), indent);
          if (enclosing != null) {
            buf.append(enclosing).append('.');
          }
        }

        buf.append("new ");

        if (selfReference) {
          buf.append("<anonymous constructor>");
        } else {
          String typename = ExprProcessor.getCastTypeName(child.anonymousClassType);
          if (enclosing != null) {
            ClassNode anonymousNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(child.anonymousClassType.value);
            if (anonymousNode != null) {
              typename = anonymousNode.simpleName;
            }
            else {
              typename = typename.substring(typename.lastIndexOf('.') + 1);
            }
          }

          boolean appendType = true;
          if (child.getWrapper() != null) {
            GenericClassDescriptor descriptor = child.getWrapper().getClassStruct().getSignature();
            if (descriptor != null) {
              if (descriptor.superinterfaces.isEmpty()) {
                appendAnonymousSuperType(buf, descriptor.superclass, child);
              } else {
                if (descriptor.superinterfaces.size() > 1 && !lambda) {
                  DecompilerContext.getLogger().writeMessage("Inconsistent anonymous class signature: " + child.classStruct.qualifiedName,
                    IFernflowerLogger.Severity.WARN);
                }
                appendAnonymousSuperType(buf, descriptor.superinterfaces.get(0), child);
              }
              appendType = false;
            }
          }

          if (appendType) {
            buf.appendCastTypeName(typename, child.anonymousClassType);
          }
        }
      }

      if (!lambda && constructor != null) {
        List<VarType> args = constructor.getGenericArgs();
        boolean diamond = args.size() == 1 && args.get(0) == GenericType.DUMMY_VAR;
        if (args.isEmpty() && DecompilerContext.getOption(
              org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences.ROUND_TRIP_DIAMOND)
            && hasTypeParameters(newType)) {
          // No type arguments were recovered, but javac can infer them from the context; the
          // original wrote `new Foo<>()`, and the raw type would break the caller's inference.
          buf.append("<>");
          args = List.of(GenericType.DUMMY_VAR);
          diamond = false;
        } else {
          appendParameters(buf, args);
        }
        buf.append('(');
        if (diamond) {
          InvocationExprent.enterPoly();
        }
        boolean anonymousCreation = child != null;
        if (anonymousCreation) {
          InvocationExprent.enterAnonymousCreation();
        }
        try {
          constructor.setCallerOpeningLine(RoundTrip.sourceLine(this));
          buf.append(constructor.appendParamList(indent));
        } finally {
          if (anonymousCreation) {
            InvocationExprent.exitAnonymousCreation();
          }
          if (diamond) {
            InvocationExprent.exitPoly();
          }
        }
      }
      else {
        appendParameters(buf, genericArgs);
        buf.append('(');
      }

      buf.append(')');

      if (enumConst && buf.length() == 2) {
        buf.setLength(0);
      }

      if (lambda) {
        if (!DecompilerContext.getOption(IFernflowerPreferences.LAMBDA_TO_ANONYMOUS_CLASS)) {
          buf.setLength(0);  // remove the usual 'new <class>()', it will be replaced with lambda style '() ->'
        }
        setLambdaGenericTypes();
        Exprent methodObject = constructor == null ? null : constructor.getInstance();
        if (methodObject == null && constructor != null && child != null
            && child.lambdaInformation.is_content_method_static && !constructor.getLstParameters().isEmpty()) {
          // A static lambda bridge takes the captured receiver as its first parameter; a method
          // reference bound to it prints that value as the reference's qualifier.
          methodObject = constructor.getLstParameters().get(0);
        }
        if (methodObject != null && isMethodReference()) {
          forceRecordedReceiverType(methodObject);
        }
        // The lambda's line is the line of the call that carries it; the invokeDynamic's own
        // table entry can interpolate to an earlier line when the call spans lines.
        int callLine = InvocationExprent.enclosingCallLine();
        new ClassWriter().classLambdaToJava(child, buf, methodObject, indent,
          callLine >= 0 ? callLine : RoundTrip.sourceLine(this), methodReferenceQualifier(), getFunctionalReturnType());
      }
      else if (!selfReference) {
        String regionClass = child == null || child.classStruct == null ? null : child.classStruct.qualifiedName;
        int region = regionClass == null ? -1 : buf.beginRegion(regionClass);
        try {
          new ClassWriter().writeClass(child, buf, indent);
        }
        finally {
          if (region >= 0) {
            buf.endRegion(regionClass, region);
          }
        }
      }
    }
    else if (directArrayInit) {
      VarType leftType = newType.decreaseArrayDim();
      buf.append('{');
      if (!lstArrayElements.isEmpty()) {
        buf.pushNewlineGroup(indent, 2);
        buf.appendPossibleNewline();
        buf.pushNewlineGroup(indent, 0);
      }
      for (int i = 0; i < lstArrayElements.size(); i++) {
        if (i > 0) {
          buf.append(",").appendPossibleNewline(" ");
        }
        ExprProcessor.getCastedExprent(lstArrayElements.get(i), leftType, buf, indent, false);
      }
      if (!lstArrayElements.isEmpty()) {
        buf.popNewlineGroup();
        buf.appendPossibleNewline("", true);
        buf.popNewlineGroup();
      }
      buf.append('}');
    }
    else if (newType.arrayDim == 0) {
      if (!enumConst) {
        TextBuffer enclosing = null;
        boolean implicitEnclosing = constructor != null
          && implicitEnclosingInstance(newType.value, constructor.getLstParameters());

        if (constructor != null) {
          // Evaluate the qualified form as before even when the source wrote the implicit one:
          // its printing seeds types the surrounding expressions rely on.
          enclosing = getQualifiedNewInstance(newType.value, constructor.getLstParameters(), indent);
          if (enclosing != null && !implicitEnclosing) {
            buf.append(enclosing).append('.');
          }
        }

        buf.append("new ");

        String typename = ExprProcessor.getTypeName(newType);
        if (enclosing == null) {
          String qualified = qualifiedInnerNewType(newType);
          if (qualified != null && !implicitEnclosing) {
            typename = qualified;
          }
        }
        else if (!implicitEnclosing) {
          ClassNode newNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
          if (newNode != null) {
            typename = newNode.simpleName;
          }
          else {
            typename = typename.substring(typename.lastIndexOf('.') + 1);
          }
        }
        buf.appendTypeName(typename, newType);
      }

      if (constructor != null) {
        int start = enumConst ? 2 : 0;
        if (!enumConst || start < constructor.getLstParameters().size()) {
          List<VarType> args = forcedConstructorArgs != null ? forcedConstructorArgs
            : impliedConstructorArgs != null ? impliedConstructorArgs : constructor.getPrintedGenericArgs();
          if (targetedDiamond && forcedConstructorArgs == null) {
            // The recovered arguments are only subtypes of the expected ones; printing them
            // would pin javac to a type the target rejects, so the source wrote the diamond.
            buf.append("<>");
            constructor.setCallerOpeningLine(RoundTrip.sourceLine(this));
            buf.append('(').append(constructor.appendParamList(indent)).append(')');
            return buf;
          }
          // A receiver has no target type. A diamond printed because the value sits inside an
          // enclosing argument list would infer its arguments from the constructor's arguments
          // alone, and when those leave a variable unconstrained javac closes it on its bound:
          // the chained receiver then loses the parameterization the caller needs. The original
          // wrote the raw type in that position, and erasure makes the two spellings identical.
          boolean receiverDiamond = args.isEmpty() && isQualifier;
          if (args.isEmpty() && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DIAMOND)
              && InvocationExprent.inArgument() && hasTypeParameters(newType) && !receiverDiamond) {
            // No recovered type arguments, but javac infers them from the context; the original
            // wrote the diamond, and a raw type would break the caller's inference.
            buf.append("<>");
          } else {
            appendParameters(buf, args);
          }
          constructor.setCallerOpeningLine(RoundTrip.sourceLine(this));
          buf.append('(').append(constructor.appendParamList(indent)).append(')');
        }
      }
    }
    else if (isVarArgParam) {
      // just print the array elements
      VarType leftType = newType.decreaseArrayDim();
      // The array's own line is the packaging instruction's, which inherits whichever call the
      // elements are arguments of; the elements' lines are only comparable with that call's.
      int callLine = InvocationExprent.enclosingCallLine();
      int previousEnd = callLine >= 0 ? callLine : RoundTrip.sourceLine(this);
      // An invocation, a creation and a conditional expression carry a line entry of their own; a
      // variable or constant carries none, so its line is whatever the statement before it left
      // and no gap from it to a later element proves anything.
      boolean enabled = RoundTrip.selector("vararg-elements");
      boolean previousOwnLine = true;
      for (int i = 0; i < lstArrayElements.size(); i++) {
        Exprent element = lstArrayElements.get(i);
        int line = RoundTrip.sourceLine(element);
        int end = RoundTrip.sourceLineEnd(element);
        // An element the original put on a later line starts a line here. A later element whose
        // own line is inherited but whose invoke is later was written on that later line, for the
        // same reason as an argument.
        boolean later = enabled && previousOwnLine
          && line >= 0 && previousEnd >= 0 && line > previousEnd;
        boolean ownLater = enabled && element instanceof InvocationExprent
          && line >= 0 && previousEnd >= 0 && line <= previousEnd && end > previousEnd;
        if (i > 0) {
          buf.append(",");
          if (later || ownLater) {
            buf.appendLineSeparator();
          } else {
            buf.appendPossibleNewline(" ");
          }
        } else if (later || ownLater) {
          buf.appendLineSeparator();
        }

        // new String[][]{{"abc"}, {"DEF"}} => new String[]{"abc"}, new String[]{"DEF"}
        if (element instanceof NewExprent) {
          ((NewExprent) element).setDirectArrayInit(false);
        }
        ExprProcessor.getCastedExprent(element, leftType, buf, indent, false);
        if (end >= 0) {
          previousEnd = end;
        }
        previousOwnLine = element instanceof InvocationExprent || element instanceof NewExprent
          || element instanceof FunctionExprent;
      }

      // if there is just one element of Object[] type it needs to be casted to resolve ambiguity
      if (lstArrayElements.size() == 1) {
        VarType elementType = lstArrayElements.get(0).getExprType();
        if (elementType.type == CodeType.OBJECT && elementType.value.equals("java/lang/Object") && elementType.arrayDim >= 1) {
          buf.prepend("(Object)");
          buf.addClassToken(1, 6, "java/lang/Object");
        }
      }
    }
    else {
      buf.append("new ").appendTypeName(newType);

      if (lstArrayElements.isEmpty()) {
        for (int i = 0; i < newType.arrayDim; i++) {
          buf.append('[');
          if (i < lstDims.size()) {
            if (lstDims.get(i).type == Type.CONST) {
              ((ConstExprent)lstDims.get(i)).adjustConstType(VarType.VARTYPE_INT);
            }
            buf.append(lstDims.get(i).toJava(indent));
          }
          buf.append(']');
        }
      }
      else {
        for (int i = 0; i < newType.arrayDim; i++) {
          buf.append("[]");
        }

        VarType leftType = newType.decreaseArrayDim();
        buf.append('{');
        buf.pushNewlineGroup(indent, 1);
        // The target's table gives every element its own line when the source wrote the array
        // across lines; an equal or absent line is no evidence of a break.
        int arrayLine = RoundTrip.sourceLine(this);
        Exprent firstElement = lstArrayElements.get(0);
        int firstLine = RoundTrip.sourceLine(firstElement);
        // A variable or constant carries no line entry: its line is inherited from the statement,
        // so a gap from it to a later element proves nothing. Only an expression with its own
        // entry can anchor a break, on either side.
        boolean firstOwnLine = hasOwnLine(firstElement) && startsOnItsLine(firstElement);
        if (arrayLine >= 0 && firstOwnLine && firstLine > arrayLine) {
          buf.appendLineSeparator().appendIndent(indent + 1);
        } else {
          buf.appendPossibleNewline();
        }
        buf.pushNewlineGroup(indent, 0);
        boolean previousOwnLine = firstOwnLine;
        for (int i = 0; i < lstArrayElements.size(); i++) {
          if (i > 0) {
            Exprent element = lstArrayElements.get(i);
            buf.append(",");
            int previousLine = RoundTrip.sourceLine(lstArrayElements.get(i - 1));
            int line = RoundTrip.sourceLine(element);
            if (previousOwnLine && hasOwnLine(element) && startsOnItsLine(element)
              && previousLine >= 0 && line > previousLine) {
              buf.appendLineSeparator().appendIndent(indent + 1);
            } else {
              buf.appendPossibleNewline(" ");
            }
          }
          ExprProcessor.getCastedExprent(lstArrayElements.get(i), leftType, buf, indent, false);
          previousOwnLine = hasOwnLine(lstArrayElements.get(i));
        }
        buf.popNewlineGroup();
        buf.appendPossibleNewline("", true);
        buf.append('}');
        buf.popNewlineGroup();
      }
    }

    return buf;
  }

  // TODO move to InvocationExprent
  public static boolean probablySyntheticParameter(String className) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(className);
    return node != null && node.type == ClassNode.Type.ANONYMOUS;
  }

  public static TextBuffer getQualifiedNewInstance(String classname, List<Exprent> lstParams, int indent) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);

    if (node != null && node.type != ClassNode.Type.ROOT && node.type != ClassNode.Type.LOCAL
        && (node.access & CodeConstants.ACC_STATIC) == 0) {
      if (!lstParams.isEmpty()) {
        Exprent enclosing = lstParams.get(0);

        boolean isQualifiedNew = false;

        if (enclosing instanceof VarExprent) {
          VarExprent varEnclosing = (VarExprent)enclosing;

          StructClass current_class = ((ClassNode)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE)).classStruct;
          String this_classname = varEnclosing.getProcessor().getThisVars().get(new VarVersionPair(varEnclosing));

          if (!current_class.qualifiedName.equals(this_classname)) {
            isQualifiedNew = true;
          }
        }
        else {
          isQualifiedNew = true;
        }

        if (isQualifiedNew) {
          return enclosing.toJava(indent);
        }
      }
    }

    return null;
  }

  /**
   * True when the creation's enclosing instance is a lexically enclosing {@code this} and the
   * target did not null-check it. javac emits {@code dup; Objects.requireNonNull; pop} after the
   * enclosing expression of a qualified creation inside a nested class, and nothing for the
   * implicit form, so the absence of that check is the source's unqualified {@code new Inner()}.
   */
  private boolean implicitEnclosingInstance(String classname, List<Exprent> lstParams) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
    if (node == null || node.type == ClassNode.Type.ROOT || node.type == ClassNode.Type.LOCAL
        || (node.access & CodeConstants.ACC_STATIC) != 0 || lstParams.isEmpty()
        || !(lstParams.get(0) instanceof VarExprent enclosing)) {
      return false;
    }
    ClassNode current = (ClassNode) DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    if (current == null) {
      return false;
    }
    String owner = enclosing.getProcessor().getThisVars().get(new VarVersionPair(enclosing));
    if (owner == null || current.classStruct.qualifiedName.equals(owner)) {
      // Not a captured outer instance; the printer already leaves the current class's own this
      // unqualified.
      return false;
    }
    return !enclosingInstanceChecked(this);
  }

  /** True when the target emitted the null check javac gives a qualified member-class creation. */
  private static boolean enclosingInstanceChecked(Exprent creation) {
    StructMethod method = RoundTrip.currentMethod();
    if (method == null || creation.bytecode == null || creation.bytecode.isEmpty()) {
      return true;
    }
    StructClass cl = DecompilerContext.getStructContext().getClass(method.getClassQualifiedName());
    if (cl == null) {
      return true;
    }
    boolean hadData = method.getInstructionSequence() != null;
    try {
      method.expandData(cl);
      FullInstructionSequence seq = method.getInstructionSequence();
      if (seq == null) {
        return true;
      }
      Integer index = seq.offsetToIndex().get(creation.bytecode.nextSetBit(0));
      if (index == null) {
        return true;
      }
      for (int i = index; i < Math.min(seq.length(), index + 32); i++) {
        Instruction ins = seq.getInstr(i);
        if (ins.opcode == CodeConstants.opc_invokespecial) {
          return false;
        }
        if (ins.opcode == CodeConstants.opc_invokestatic) {
          LinkConstant target = cl.getPool().getLinkConstant(ins.operand(0));
          if (target != null && "java/util/Objects".equals(target.classname)
              && "requireNonNull".equals(target.elementname)) {
            return true;
          }
        }
      }
      return true;
    } catch (IOException e) {
      return true;
    } finally {
      // The method's data was released before printing; leave it that way.
      if (!hadData) {
        method.releaseResources();
      }
    }
  }

  private static VarType getLambdaReturnType(ClassNode node, StructMethod desc, VarType upperBound, Map<VarType, VarType> genericsMap) {
    ClassWrapper wrapper = node.getWrapper();
    Map<String, VarType> inferredLambdaTypes = Exprent.inferredLambdaTypes.get();

    if (wrapper != null) {
      MethodWrapper mt = wrapper.getMethodWrapper(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);

      if (mt != null && mt.root != null) {
        List<String> paramNames = new ArrayList<>();

        MethodDescriptor md_content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
        MethodDescriptor md_lambda = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);

        int index = node.lambdaInformation.is_content_method_static ? 0 : 1;
        int start_index = md_content.params.length - md_lambda.params.length;

        int j = 0;
        for (int i = 0; i < md_content.params.length; i++) {
          if (i >= start_index) {
            VarVersionPair vpp = new VarVersionPair(index, 0);
            VarType curType = mt.varproc.getVarType(vpp);
            VarType infType = desc.getSignature().parameterTypes.get(j++).remap(genericsMap);

            if (infType != null && !infType.equals(VarType.VARTYPE_VOID)) {
              if (!curType.equals(infType) || (infType.isGeneric() && !((GenericType)infType).equalsExact(curType))) {
                String varName = mt.varproc.getVarName(vpp);
                paramNames.add(varName);
                inferredLambdaTypes.put(varName, infType);
              }
            }
          }
          index += md_content.params[i].stackSize;
        }

        DummyExitStatement dummyExit = mt.root.getDummyExit();

        for (StatEdge edge : dummyExit.getAllPredecessorEdges()) {
          Statement source = edge.getSource();
          List<Exprent> lstExpr = source.getExprents();

          if (lstExpr != null && !lstExpr.isEmpty()) {
            Exprent expr = lstExpr.get(lstExpr.size() - 1);
            if (expr instanceof ExitExprent) {
              ExitExprent ex = (ExitExprent)expr;
              if (ex.getExitType() == ExitExprent.Type.RETURN) {
                VarType realRetType = ex.getValue().getInferredExprType(upperBound);
                if (realRetType.isGeneric()) {
                  paramNames.forEach(inferredLambdaTypes::remove);
                  return realRetType;
                }
              }
            }
          }
        }

        paramNames.forEach(inferredLambdaTypes::remove);
      }
    }
    return null;
  }

  /** The parameter slot of an enclosed lambda's method that carries this name, or -1. */
  private static int namedParameterSlot(ClassNode child, MethodWrapper enclosed, String name) {
    MethodDescriptor descriptor = MethodDescriptor.parseDescriptor(child.lambdaInformation.content_method_descriptor);
    int slot = child.lambdaInformation.is_content_method_static ? 0 : 1;
    for (VarType parameter : descriptor.params) {
      if (name.equals(enclosed.varproc.getVarName(new VarVersionPair(slot, 0)))) {
        return slot;
      }
      slot += parameter.stackSize;
    }
    return -1;
  }

  private void setLambdaGenericTypes() {
    if (inferredLambdaType != null) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
      StructClass cls = DecompilerContext.getStructContext().getClass(inferredLambdaType.value);

      if (node != null && cls != null) {
        StructMethod desc = cls.getMethod(getLambdaMethodKey());
        ClassWrapper wrapper = node.getWrapper();
        MethodWrapper methodWrapper = wrapper != null ? wrapper.getMethodWrapper(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor) : null;

        if (desc != null && desc.getSignature() != null && methodWrapper != null && methodWrapper.root != null) {
          if (!desc.getClassQualifiedName().equals(inferredLambdaType.value)) {
            StructClass candidate = DecompilerContext.getStructContext().getClass(desc.getClassQualifiedName());
            if (candidate.getSignature() != null) {
              cls = candidate;
              inferredLambdaType = GenericType.getGenericSuperType(inferredLambdaType, candidate.getSignature().genericType);
            }
          }
          if (cls.getSignature() == null) {
            // Without the interface's declared type parameters nothing can be mapped.
            return;
          }

          Map<VarType, VarType> tempMap = new HashMap<>();
          if (inferredLambdaType.isGeneric()) {
            cls.getSignature().genericType.mapGenVarsTo((GenericType)inferredLambdaType, tempMap);
          }

          if (wildcardTargetLambda) {
            // The lambda's interface type came from the wildcard form of the called method's
            // parameter type. Only a recorded return type that resolves to one type variable
            // in the caller's scope is used: a value the body returns as a class can never be
            // that variable, so the source cast it (the cast erases to the same bytes), and
            // the class file's functional interface signature names the variable.
            VarType rawRet = desc.getSignature().returnType;
            VarType mappedRet = rawRet.type == CodeType.GENVAR ? tempMap.get(rawRet.resizeArrayDim(0)) : null;
            // Only the wildcard form (? extends R) is the called method's recorded demand on
            // the body; a return type that is the variable itself carries no such wrapper, and
            // a body's own inference is what the source relied on there.
            if (!(mappedRet instanceof GenericType wildcardRet)
              || wildcardRet.getWildcard() == GenericType.WILDCARD_NO) {
              return;
            }
            VarType retTarget = stripWildcard(mappedRet);
            if (retTarget != null && retTarget.type == CodeType.GENVAR
              && isInScopeTypeVariable(retTarget, getNamedGenerics())) {
              GenericMethodDescriptor genDesc = new GenericMethodDescriptor(Collections.emptyList(), Collections.emptyList(), Collections.emptyList(), retTarget, Collections.emptyList());
              applyReturnTarget(methodWrapper.root, genDesc);
            }
            return;
          }

          MethodDescriptor md_content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
          MethodDescriptor md_lambda = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);

          int index = node.lambdaInformation.is_content_method_static ? 0 : 1;
          int start_index = md_content.params.length - md_lambda.params.length;

          int j = 0;
          for (int i = 0; i < md_content.params.length; i++) {
            if (i >= start_index) {
              VarVersionPair vpp = new VarVersionPair(index, 0);
              VarType curType = methodWrapper.varproc.getVarType(vpp);
              VarType infType = desc.getSignature().parameterTypes.get(j++).remap(tempMap);

              if (infType != null && !infType.equals(VarType.VARTYPE_VOID) && curType != null) {
                if (!curType.equals(infType) || (infType.isGeneric() && !((GenericType)infType).equalsExact(curType))) {
                  methodWrapper.varproc.setVarType(vpp, infType);
                  String paramName = methodWrapper.varproc.getVarName(vpp);

                  LinkedList<ClassNode> nested = new LinkedList<>(node.nested);
                  while (!nested.isEmpty()) {
                    ClassNode childNode = nested.removeFirst();
                    nested.addAll(childNode.nested);

                    if (childNode.type == ClassNode.Type.LAMBDA && !childNode.lambdaInformation.is_method_reference) {
                      MethodWrapper enclosedMethod = wrapper.getMethodWrapper(childNode.lambdaInformation.content_method_name, childNode.lambdaInformation.content_method_descriptor);

                      if (enclosedMethod != null) {
                        // A captured variable becomes a leading parameter of the enclosed synthetic
                        // method at a slot of its own; its name, not the outer index, finds it. Only
                        // an erased type is refined: a parameter that already carries generics got
                        // them from its own call site, and overriding those changes the printed
                        // casts of an unrelated chain.
                        int slot = namedParameterSlot(childNode, enclosedMethod, paramName);
                        if (slot >= 0) {
                          VarVersionPair enclosedPair = new VarVersionPair(slot, 0);
                          VarType enclosedType = enclosedMethod.varproc.getVarType(enclosedPair);
                          if (enclosedType == null
                              || (enclosedType.type == CodeType.OBJECT && !enclosedType.isGeneric())) {
                            enclosedMethod.varproc.setVarType(enclosedPair, infType);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            index += md_content.params[i].stackSize;
          }

          VarType curType = md_content.ret;
          VarType infType = desc.getSignature().returnType.remap(tempMap);

          if (infType != null && !infType.equals(VarType.VARTYPE_VOID)) {
            if (!curType.equals(infType) || (infType.isGeneric() && !((GenericType)infType).equalsExact(curType))) {
              GenericMethodDescriptor genDesc = new GenericMethodDescriptor(Collections.emptyList(), Collections.emptyList(), Collections.emptyList(), infType, Collections.emptyList());
              DummyExitStatement dummyExit = methodWrapper.root.getDummyExit();

              for (StatEdge edge : dummyExit.getAllPredecessorEdges()) {
                Statement source = edge.getSource();
                List<Exprent> lstExpr = source.getExprents();

                if (lstExpr != null && !lstExpr.isEmpty()) {
                  Exprent expr = lstExpr.get(lstExpr.size() - 1);
                  if (expr instanceof ExitExprent) {
                    ExitExprent ex = (ExitExprent)expr;
                    if (ex.getExitType() == ExitExprent.Type.RETURN) {
                      ex.getMethodDescriptor().genericInfo = genDesc;
                      break; // desc var should be the same for all returns
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  /** Give every return in a lambda body the functional method's recorded return type. */
  private static void applyReturnTarget(Statement stat, GenericMethodDescriptor genDesc) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN
          && exit.getMethodDescriptor() != null) {
          exit.getMethodDescriptor().genericInfo = genDesc;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (child != null) {
        applyReturnTarget(child, genDesc);
      }
    }
  }

  public boolean doesClassHaveMethodsNamedSame() {
    if (this.lambda && this.methodReference) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(this.newType.value);

      if (node != null) {
        String name = node.lambdaInformation.content_method_name;
        ClassNode contentClass = DecompilerContext.getClassProcessor().getMapRootClasses().get(node.lambdaInformation.content_class_name);

        if (contentClass == null) {
          return false;
        }

        boolean foundOne = false;
        for (StructMethod method : contentClass.classStruct.getMethods()) {
          if (method.getName().equals(name)) {
            if (foundOne) {
              return true;
            } else {
              foundOne = true;
            }
          }
        }
      }
    }

    return false;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == constructor) {
      constructor = (InvocationExprent)newExpr;
    }

    if (constructor != null) {
      constructor.replaceExprent(oldExpr, newExpr);
    }

    for (int i = 0; i < lstDims.size(); i++) {
      if (oldExpr == lstDims.get(i)) {
        lstDims.set(i, newExpr);
      }
    }

    for (int i = 0; i < lstArrayElements.size(); i++) {
      if (oldExpr == lstArrayElements.get(i)) {
        lstArrayElements.set(i, newExpr);
      }
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof NewExprent)) return false;

    NewExprent ne = (NewExprent)o;
    return InterpreterUtil.equalObjects(newType, ne.getNewType()) &&
           InterpreterUtil.equalLists(lstDims, ne.getLstDims()) &&
           InterpreterUtil.equalObjects(constructor, ne.getConstructor()) &&
           directArrayInit == ne.directArrayInit &&
           InterpreterUtil.equalLists(lstArrayElements, ne.getLstArrayElements());
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, lstArrayElements);
    measureBytecode(values, lstDims);
    measureBytecode(values, constructor);
    measureBytecode(values);
  }

  public InvocationExprent getConstructor() {
    return constructor;
  }

  public void setConstructor(InvocationExprent constructor) {
    this.constructor = constructor;
  }

  public List<Exprent> getLstDims() {
    return lstDims;
  }

  public VarType getNewType() {
    return newType;
  }

  public List<Exprent> getLstArrayElements() {
    return lstArrayElements;
  }

  public void setLstArrayElements(List<Exprent> lstArrayElements) {
    this.lstArrayElements = lstArrayElements;
  }

  public void setDirectArrayInit(boolean directArrayInit) {
    this.directArrayInit = directArrayInit;
  }

  public boolean isDirectArrayInit() {
    return directArrayInit;
  }

  public void setVarArgParam(boolean isVarArgParam) {
    this.isVarArgParam = isVarArgParam;
  }

  public boolean isVarArgParam() {
    return this.isVarArgParam;
  }

  public boolean isLambda() {
    return lambda;
  }

  public boolean isAnonymous() {
    return anonymous;
  }

  public void setAnonymous(boolean anonymous) {
    this.anonymous = anonymous;
  }

  public boolean isEnumConst() {
    return enumConst;
  }

  public void setEnumConst(boolean enumConst) {
    this.enumConst = enumConst;
  }

  @Override
  public void setIsQualifier() {
    isQualifier = true;
  }

  /**
   * Prints the supertype an anonymous class is written against, with a diamond where javac was
   * given one.
   *
   * <p>A capturing anonymous class compiled from explicit type arguments carries a synthetic
   * constructor signature; one compiled from a diamond carries none. The class's own signature is
   * the same either way, so the constructor attribute is the only record of which form the original
   * source used, and printing the arguments where the original had a diamond adds an attribute the
   * class does not have. A class that captures nothing carries no signature in either form and is
   * left alone, since there the arguments are also recoverable from the context.
   *
   * <p>A receiver has no target type, so a diamond there cannot be inferred and cannot be the
   * form the source wrote: the explicit arguments are printed even without the constructor's
   * signature.
   */
  private void appendAnonymousSuperType(TextBuffer buf, VarType superType, ClassNode node) {
    if (superType instanceof GenericType && !((GenericType)superType).getArguments().isEmpty()
        && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DIAMOND)
        && node.classStruct != null) {
      for (StructMethod method : node.classStruct.getMethods()) {
        if (CodeConstants.INIT_NAME.equals(method.getName()) && !method.getDescriptor().startsWith("()")) {
          if (method.getSignature() == null && !isQualifier) {
            buf.appendCastTypeName(new VarType(superType.type, superType.arrayDim, superType.value)).append("<>");
            return;
          }
          break;
        }
      }
    }
    buf.appendCastTypeName(superType);
  }

  private static boolean hasTypeParameters(VarType type) {
    if (type == null || !type.equals(VarType.VARTYPE_OBJECT)) {
      var node = DecompilerContext.getStructContext().getClass(type.value);
      return node != null && node.getSignature() != null && !node.getSignature().fparameters.isEmpty();
    }
    return false;
  }

  /**
   * The name of a non-static inner class declared inside the class being decompiled, qualified by
   * its outer type's arguments.
   *
   * <p>javac rejects type arguments written on a raw type, so a source that compiled never says
   * {@code new Outer.Inner<T>()} for a class that needs the outer's parameters; it writes
   * {@code new Outer<T>.Inner<>()}. A member class that holds an outer instance carries the
   * compiler's synthetic {@code this$0} field recording that outer, and the arguments the outer
   * needs are exactly the type parameters the current class declares.
   */
  private static String qualifiedInnerNewType(VarType type) {
    if (type == null || type.type != CodeType.OBJECT || type.arrayDim != 0 || type.isGeneric()) {
      return null;
    }
    StructClass inner = DecompilerContext.getStructContext().getClass(type.value);
    if (inner == null) {
      return null;
    }
    StructClass outer = capturedOuterClass(inner);
    if (outer == null || outer.getSignature() == null || outer.getSignature().fparameters.isEmpty()) {
      return null;
    }
    StructClass current = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
    String outerName = outer.qualifiedName;
    String prefix = outerName + "$";
    if (current == null || !(current.qualifiedName.equals(outerName) || current.qualifiedName.startsWith(prefix))) {
      return null;
    }
    if (type.value == null || !type.value.startsWith(prefix) || type.value.indexOf('$', prefix.length()) >= 0) {
      return null;
    }
    StringBuilder signature = new StringBuilder("L").append(outerName).append('<');
    for (String parameter : outer.getSignature().fparameters) {
      signature.append('T').append(parameter).append(';');
    }
    signature.append(">.").append(type.value.substring(prefix.length())).append(';');
    VarType view = GenericType.parse(signature.toString());
    return view.isGeneric() ? ExprProcessor.getTypeName(view) : null;
  }

  /** The outer class whose instance a member class holds in the compiler's synthetic field. */
  private static StructClass capturedOuterClass(StructClass inner) {
    for (StructField field : inner.getFields()) {
      String name = field.getName();
      if (name.startsWith("this$") && field.getDescriptor().startsWith("L") && field.getDescriptor().endsWith(";")) {
        return DecompilerContext.getStructContext().getClass(field.getDescriptor().substring(1, field.getDescriptor().length() - 1));
      }
    }
    return null;
  }

  public boolean isMethodReference() {
    return methodReference;
  }

  /** The functional interface type this lambda was inferred against, if any. */
  public VarType getInferredLambdaType() {
    return inferredLambdaType;
  }

  /**
   * The SAM's return type as this functional argument was inferred to produce, instantiated from
   * the functional interface's recorded type. A type variable that stays unresolved here belongs
   * to the referenced class or the interface itself; print-time code cannot name it, and a
   * call's own inference cannot bind it to a type variable of the caller either.
   */
  public VarType getFunctionalReturnType() {
    if (!lambda || inferredLambdaType == null || !inferredLambdaType.isGeneric()) {
      return null;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return null;
    }
    StructClass iface = DecompilerContext.getStructContext().getClass(node.anonymousClassType.value);
    if (iface == null || iface.getSignature() == null) {
      return null;
    }
    StructMethod sam = iface.getMethod(getLambdaMethodKey());
    if (sam == null || sam.getSignature() == null || sam.getSignature().returnType == null) {
      return null;
    }
    Map<VarType, VarType> map = new HashMap<>();
    iface.getSignature().genericType.mapGenVarsTo((GenericType) inferredLambdaType, map);
    return sam.getSignature().returnType.remap(map);
  }

  /**
   * The arguments of a diamond whose recorded target is a parameterized supertype of the
   * constructed class ({@code new C<>()} where the target is {@code Map<List<Runnable>>}):
   * reading the target through the class's recorded supertype signature (C<K,V> as Map<K,V>)
   * solves the class's variables. The erased constructor invocation is the one the target
   * recorded, and the source named the arguments the target required.
   */
  private List<VarType> impliedArguments(VarType upperBound) {
    if (!(upperBound instanceof GenericType target) || target.type != CodeType.OBJECT
      || target.arrayDim != 0 || target.getWildcard() != GenericType.WILDCARD_NO) {
      return null;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(newType.value);
    if (cls == null || cls.getSignature() == null) {
      return null;
    }
    GenericClassDescriptor signature = cls.getSignature();
    if (signature.fparameters.isEmpty()) {
      return null;
    }
    VarType view = target.value.equals(newType.value)
      ? signature.genericType : GenericType.getGenericSuperType(signature.genericType, target);
    if (!(view instanceof GenericType superView) || !target.value.equals(superView.value)
      || superView.getArguments().size() != target.getArguments().size()) {
      return null;
    }
    Map<VarType, VarType> solved = new HashMap<>();
    superView.mapGenVarsTo(target, solved);
    List<VarType> args = new ArrayList<>(signature.fparameters.size());
    for (String parameter : signature.fparameters) {
      VarType value = solved.get(GenericType.parse("T" + parameter + ";"));
      if (!isImpliedType(value)) {
        return null;
      }
      args.add(value);
    }
    return args;
  }

  /** A type the implied arguments can name: no free variable, wildcard or raw generic. */
  private static boolean isImpliedType(VarType type) {
    if (type == null || type == GenericType.DUMMY_VAR || type.type == CodeType.GENVAR) {
      return false;
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      for (VarType argument : generic.getArguments()) {
        if (!isImpliedType(argument)) {
          return false;
        }
      }
      return true;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    return cls == null || cls.getSignature() == null || cls.getSignature().fparameters.isEmpty();
  }

  /**
   * The recovered constructor arguments do not satisfy the expected type at an invariant
   * position, but they are subtypes of the expected ones and the constructor takes the class's
   * own type variables: only a diamond lets javac infer the expected arguments from the target.
   */
  private boolean expectsWiderArguments(VarType upperBound) {
    if (!DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DIAMOND) || constructor == null
      || !(upperBound instanceof GenericType target) || target.type != CodeType.OBJECT
      || target.arrayDim != 0 || target.getWildcard() != GenericType.WILDCARD_NO
      || !target.value.equals(newType.value)) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(newType.value);
    if (cls == null || cls.getSignature() == null) {
      return false;
    }
    GenericClassDescriptor signature = cls.getSignature();
    List<VarType> targetArgs = target.getArguments();
    if (targetArgs.size() != signature.fparameters.size()) {
      return false;
    }
    StructMethod desc = constructor.getDesc();
    if (desc == null) {
      return false;
    }
    if (desc.getSignature() != null && desc.getSignature().parameterTypes.size() == signature.fparameters.size()) {
      // The constructor's own Signature names the class's variables: a diamond can infer them.
      for (String fp : signature.fparameters) {
        boolean present = false;
        for (VarType parameter : desc.getSignature().parameterTypes) {
          if (parameter != null && parameter.type == CodeType.GENVAR && parameter.arrayDim == 0
            && parameter.value.equals(fp)) {
            present = true;
          }
        }
        if (!present) {
          return false;
        }
      }
    } else {
      // No constructor Signature: the erased parameters must still be the class's variables'
      // bounds, in order, for the target to drive inference through them.
      VarType[] parameters = MethodDescriptor.parseDescriptor(desc.getDescriptor()).params;
      if (parameters.length != signature.fparameters.size()) {
        return false;
      }
      for (int i = 0; i < parameters.length; i++) {
        List<VarType> declared = i < signature.fbounds.size() ? signature.fbounds.get(i) : null;
        VarType bound = declared == null || declared.isEmpty() || declared.get(0).type == CodeType.GENVAR
          ? VarType.VARTYPE_OBJECT : declared.get(0);
        if (bound.type == CodeType.OBJECT) {
          if (!parameters[i].equals(VarType.VARTYPE_OBJECT)) {
            return false;
          }
        } else if (!parameters[i].equals(new VarType(bound.type, bound.arrayDim, bound.value))) {
          return false;
        }
      }
    }
    List<VarType> recovered = constructor.getGenericArgs();
    if (recovered.size() != targetArgs.size()) {
      return false;
    }
    boolean differs = false;
    for (int i = 0; i < recovered.size(); i++) {
      VarType mine = recovered.get(i);
      VarType want = targetArgs.get(i);
      if (mine == null || want == null) {
        return false;
      }
      if (mine.type == CodeType.GENVAR || want.type == CodeType.GENVAR) {
        if (mine.equals(want)) {
          continue;
        }
        return false;
      }
      if (mine.type != CodeType.OBJECT || want.type != CodeType.OBJECT) {
        return false;
      }
      if (sameDiamondType(mine, want)) {
        continue;
      }
      if (!DecompilerContext.getStructContext().instanceOf(mine.value, want.value)) {
        return false;
      }
      differs = true;
    }
    return differs;
  }

  private static boolean sameDiamondType(VarType a, VarType b) {
    if (a instanceof GenericType generic) {
      return generic.equalsExact(b);
    }
    return b != null && !(b instanceof GenericType) && a.equals(b);
  }

  /**
   * A bound method reference's recorded instantiated type proves the receiver's parameterized
   * type. The metafactory's instantiated method type is the functional method javac adapted, and
   * when its return type is a class but the referenced method's erased return is Object while its
   * generic signature returns the receiver class's own sole type variable, the only way javac
   * produced that adaptation is a receiver typed {@code C<Return>}: the variable had to be bound
   * to the recorded return type. The receiver expression is printed as the reference's qualifier,
   * and a diamond constructor inside it is the element that carried the type argument in source;
   * printing the recorded argument there keeps javac's inference of the constructor from closing
   * on Object and rejecting the reference. Nothing is forced unless every recorded fact agrees.
   */

  private void forceRecordedReceiverType(Exprent receiver) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null || !node.lambdaInformation.is_method_reference
      || node.lambdaInformation.is_content_method_static) {
      return;
    }
    MethodDescriptor sam = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);
    MethodDescriptor content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
    VarType samReturn = sam.ret;
    if (samReturn.type != CodeType.OBJECT || samReturn.arrayDim != 0
      || samReturn.value.equals(content.ret.value)) {
      return;
    }
    StructClass receiverClass = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);
    if (receiverClass == null || receiverClass.getSignature() == null
      || receiverClass.getSignature().fparameters.size() != 1) {
      return;
    }
    StructMethod referenced = receiverClass.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (referenced == null || referenced.getSignature() == null) {
      return;
    }
    VarType declared = referenced.getSignature().returnType;
    if (declared == null || declared.type != CodeType.GENVAR
      || !declared.value.equals(receiverClass.getSignature().fparameters.get(0))) {
      return;
    }
    for (Exprent expr : receiver.getAllExprents(true, true)) {
      if (expr instanceof NewExprent created && created != this && !created.isLambda() && !created.isAnonymous()
        && created.newType.type == CodeType.OBJECT && created.newType.arrayDim == 0
        && created.newType.value.equals(receiverClass.qualifiedName) && created.constructor != null) {
        created.forcedConstructorArgs = new ArrayList<>(List.of(samReturn));
        return;
      }
    }
  }

  /**
   * The instantiated class a static or constructor method reference names, when the recorded
   * types prove the source pinned its type arguments. The printer's inference took the value's
   * type from the target (a recorded signature); javac types a method reference without the
   * target of the chain it is passed into, and a type variable no constructor argument constrains
   * then defaults to its declared bound. The qualifier is printed only when the recorded
   * instantiation names a type variable that is in scope and is not that bound.
   */
  private VarType methodReferenceQualifier() {
    if (!DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_DEMAND_WITNESS)
      || !lambda || !isMethodReference() || inferredLambdaType == null || !inferredLambdaType.isGeneric()) {
      return null;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return null;
    }
    // Only a static method or a constructor names its class as the reference's qualifier.
    if (!node.lambdaInformation.is_content_method_static
      && !CodeConstants.INIT_NAME.equals(node.lambdaInformation.content_method_name)) {
      return null;
    }
    String contentClass = node.lambdaInformation.content_class_name;
    StructClass target = DecompilerContext.getStructContext().getClass(contentClass);
    if (target == null || target.getSignature() == null || target.getSignature().fparameters.isEmpty()) {
      return null;
    }
    // A class type variable the reference's own parameters mention is inferred by javac from the
    // arguments; naming it on the qualifier would contradict that inference.
    StructMethod content = target.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    Set<String> fromArguments = new HashSet<>();
    if (content != null && content.getSignature() != null) {
      for (VarType parameter : content.getSignature().parameterTypes) {
        collectTypeVariableNames(parameter, fromArguments);
      }
    }
    StructClass iface = DecompilerContext.getStructContext().getClass(node.anonymousClassType.value);
    if (iface == null || iface.getSignature() == null) {
      return null;
    }
    StructMethod sam = iface.getMethod(getLambdaMethodKey());
    if (sam == null || sam.getSignature() == null || sam.getSignature().returnType == null) {
      return null;
    }
    // A functional interface with no parameters gives javac nothing but the target to infer the
    // reference's type arguments from; naming our own inference there pins whatever the printer
    // happened to compute (ArrayList<E>::new where the stream's element type is what the
    // collection must hold, and E belongs to the enclosing class).
    if (sam.getSignature().parameterTypes.isEmpty()) {
      return null;
    }
    Map<VarType, VarType> map = new HashMap<>();
    iface.getSignature().genericType.mapGenVarsTo((GenericType) inferredLambdaType, map);
    VarType produced = unwrapWildcard(sam.getSignature().returnType.remap(map));
    if (produced == null || produced.type != CodeType.OBJECT || !produced.isGeneric()
      || !contentClass.equals(produced.value)) {
      return null;
    }
    GenericClassDescriptor signature = target.getSignature();
    List<VarType> args = ((GenericType) produced).getArguments();
    if (args.size() != signature.fparameters.size()) {
      return null;
    }
    Map<VarType, List<VarType>> named = getNamedGenerics();
    boolean pinned = false;
    for (int i = 0; i < args.size(); i++) {
      VarType arg = args.get(i);
      if (!isReferenceArgument(arg, named)) {
        return null;
      }
      if (fromArguments.contains(signature.fparameters.get(i))) {
        return null;
      }
      List<VarType> declared = signature.fbounds.size() > i ? signature.fbounds.get(i) : null;
      VarType bound = declared == null || declared.isEmpty() ? null : declared.get(0);
      if (isInScopeTypeVariable(arg, named)
        && (bound == null || bound.type != CodeType.GENVAR || !bound.value.equals(arg.value))) {
        pinned = true;
      }
    }
    return pinned ? produced : null;
  }

  /** The names of every type variable mentioned in a recorded type. */
  private static void collectTypeVariableNames(VarType type, Set<String> names) {
    if (type == null) {
      return;
    }
    if (type.type == CodeType.GENVAR) {
      names.add(type.value);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        collectTypeVariableNames(argument, names);
      }
    }
  }

  /** Strip a wildcard wrapper to the type it bounds; other types are returned unchanged. */
  private static VarType stripWildcard(VarType type) {
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return GenericType.withWildcard(generic, GenericType.WILDCARD_NO);
    }
    return type;
  }

  /** Strip the wildcards a functional interface's return position wraps a value in. */
  private static VarType unwrapWildcard(VarType type) {
    while (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      List<VarType> arguments = generic.getArguments();
      if (arguments.size() != 1 || arguments.get(0) == null) {
        return null;
      }
      type = arguments.get(0);
    }
    return type;
  }

  /** A type argument a source can write: an in-scope type variable or a printable generic type. */
  private static boolean isReferenceArgument(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null || type == GenericType.DUMMY_VAR) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return isInScopeTypeVariable(type, named);
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      for (VarType argument : generic.getArguments()) {
        if (argument != null && !isReferenceArgument(argument, named)) {
          return false;
        }
      }
      return !generic.getArguments().isEmpty() || !hasTypeParameters(type);
    }
    return type.type == CodeType.OBJECT;
  }

  public String getLambdaMethodKey() {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node != null && constructor != null) {
      String descriptor = ((PrimitiveConstant)constructor.getBootstrapArguments().get(0)).getString();
      return InterpreterUtil.makeUniqueKey(node.lambdaInformation.method_name, descriptor);
    }
    return "";
  }


  public String getLambdaContentMethodKey() {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node != null && constructor != null) {
      return InterpreterUtil.makeUniqueKey(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);
    }
    return "";
  }

  public void setInvocationInstance() {
    if (constructor != null) {
      constructor.setInvocationInstance();
    }
  }

  @Override
  public void processSforms(SFormsConstructor sFormsConstructor, VarMapHolder varMaps, Statement stat, boolean calcLiveVars) {
    super.processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

    if (sFormsConstructor.trackFieldVars && this.getNewType().type == CodeType.OBJECT) {
      varMaps.getNormal().removeAllFields();
    }
  }
}

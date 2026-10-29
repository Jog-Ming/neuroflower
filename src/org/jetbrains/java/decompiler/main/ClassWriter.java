// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import java.util.concurrent.atomic.AtomicBoolean;

import net.fabricmc.fernflower.api.FabricJavadocStyle;
import net.fabricmc.fernflower.api.IFabricJavadocProvider;
import org.jetbrains.java.decompiler.api.java.JavaPassLocation;
import org.jetbrains.java.decompiler.api.plugin.StatementWriter;
import org.jetbrains.java.decompiler.api.plugin.pass.PassContext;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.ExceptionHandler;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.CancelationManager;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.DecompileRecord;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarTypeProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.modules.renamer.PoolInterceptor;
import org.jetbrains.java.decompiler.struct.*;
import org.jetbrains.java.decompiler.struct.attr.*;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.FieldDescriptor;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericFieldDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericsChecker;
import org.jetbrains.java.decompiler.util.*;
import org.jetbrains.java.decompiler.util.collections.VBStyleCollection;

import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

public class ClassWriter implements StatementWriter {
  private static final Set<String> ERROR_DUMP_STOP_POINTS = new HashSet<>(Arrays.asList(
    "Fernflower.decompileContext",
    "MethodProcessor.codeToJava",
    "ClassWriter.writeMethod",
    "ClassWriter.methodLambdaToJava",
    "ClassWriter.classLambdaToJava"
  ));
  private final PoolInterceptor interceptor;
  private final IFabricJavadocProvider javadocProvider;

  public ClassWriter() {
    interceptor = DecompilerContext.getPoolInterceptor();
    javadocProvider = (IFabricJavadocProvider) DecompilerContext.getProperty(IFabricJavadocProvider.PROPERTY_NAME);
  }

  public boolean endsWithSemicolon(Exprent expr) {
    return !(expr instanceof SwitchHeadExprent ||
      expr instanceof MonitorExprent ||
      expr instanceof IfExprent ||
      (expr instanceof VarExprent && ((VarExprent)expr).isClassDef()));
  }

  private static boolean invokeProcessors(TextBuffer buffer, ClassNode node) {
    ClassWrapper wrapper = node.getWrapper();
    if (wrapper == null) {
      buffer.append("/* $VF: Couldn't be decompiled. Class " + node.classStruct.qualifiedName + " wasn't processed yet! */");
      List<String> lines = new ArrayList<>();
      lines.addAll(ClassWriter.getErrorComment());
      for (String line : lines) {
        buffer.append("//");
        if (!line.isEmpty()) buffer.append(' ').append(line);
        buffer.appendLineSeparator();
      }
      return false; // Doesn't make sense! how is this null? referencing an anonymous class in another object?
    }
    StructClass cl = wrapper.getClassStruct();

    // Very late switch processing, needs entire class to be decompiled for eclipse switchmap style switch-on-enum
    for (MethodWrapper method : wrapper.getMethods()) {
      DecompileRecord rec = new DecompileRecord(method.methodStruct);
      DecompilerContext.resetMethod(method);

      if (method.root != null) {
        try {
          if (SwitchHelper.simplifySwitches(method.root, method.methodStruct, method.root)) {
            rec.add("FinalSimplifySwitches", method.root);
          }

          // This is awful and really doesn't belong here, but this breaks simplify switches (for some reason...) so it needs to go after
          if (DecompilerContext.getOption(IFernflowerPreferences.PRETTIFY_IFS)) {
            if (IfHelper.prettifyIfs(method.root, method.methodStruct)) {
              rec.add("FinalPrettifyIfs", method.root);
            }
          }

          PassContext pctx = new PassContext(method.root, null, method.methodStruct, method.classStruct, method.varproc, rec);
          DecompilerContext.getCurrentContext().structContext.getPluginContext()
            .runPasses(JavaPassLocation.LATE_PROCESSING, pctx);

          if (!rec.getNames().isEmpty()) {
            DotExporter.toDotFile(rec, method.methodStruct, "lateDecompileRecord", false);
          }
        } catch (CancelationManager.CanceledException e) {
          throw e;
        } catch (Throwable e) {
          DecompilerContext.getLogger().writeMessage("Method " + method.methodStruct.getName() + " " + method.methodStruct.getDescriptor() + " in class " + node.classStruct.qualifiedName + " couldn't be written.",
            IFernflowerLogger.Severity.WARN,
            e);
          DotExporter.errorToDotFile(method.root, method.methodStruct, "failProcessing");
          method.decompileError = e;
        }
      }
    }

    try {
      InitializerProcessor.extractInitializers(wrapper);
      InitializerProcessor.hideInitalizers(wrapper);

      if (node.type == ClassNode.Type.ROOT &&
        cl.getVersion().has14ClassReferences() &&
        DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_CLASS_1_4)) {
        ClassReference14Processor.processClassReferences(node);
      }

      if (cl.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM)) {
        EnumProcessor.clearEnum(wrapper);
      }

      for (MethodWrapper mw : wrapper.getMethods()) {
        DecompilerContext.resetMethod(mw);
        RecordHelper.fixupCanonicalConstructor(mw, cl);
        if (mw.root != null) {
          mw.varproc.rerunClashing(mw.root);
        }
      }
    } catch (CancelationManager.CanceledException e) {
      throw e;
    } catch (Throwable t) {
      DecompilerContext.getLogger().writeMessage("Class " + node.simpleName + " couldn't be written.",
        IFernflowerLogger.Severity.WARN,
        t);
      writeException(buffer, t);

      return false;
    }

    return true;
  }

  public static void writeException(TextBuffer buffer, Throwable t) {
    buffer.append("// $VF: Couldn't be decompiled");
    buffer.appendLineSeparator();
    if (DecompilerContext.getOption(IFernflowerPreferences.DUMP_EXCEPTION_ON_ERROR)) {
      List<String> lines = new ArrayList<>();
      lines.addAll(ClassWriter.getErrorComment());
      collectErrorLines(t, lines);
      for (String line : lines) {
        buffer.append("//");
        if (!line.isEmpty()) buffer.append(' ').append(line);
        buffer.appendLineSeparator();
      }
    }
  }

  public void classLambdaToJava(ClassNode node, TextBuffer buffer, Exprent method_object, int indent,
                                int creationLine, VarType referenceQualifier, VarType functionalReturn) {
    ClassWrapper wrapper = node.getWrapper();
    if (wrapper == null) {
      return;
    }

    boolean lambdaToAnonymous = DecompilerContext.getOption(IFernflowerPreferences.LAMBDA_TO_ANONYMOUS_CLASS);

    ClassNode outerNode = (ClassNode)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);

    try {
      StructClass cl = wrapper.getClassStruct();

      DecompilerContext.getLogger().startWriteClass(node.simpleName);

      if (node.lambdaInformation.is_method_reference) {
        if (!node.lambdaInformation.is_content_method_static && method_object != null) {
          // reference to a virtual method
          method_object.getInferredExprType(new VarType(CodeType.OBJECT, 0, node.lambdaInformation.content_class_name));
          TextBuffer instance = method_object.toJava(indent);
          // If the instance is casted, then we need to wrap it
          if (method_object instanceof FunctionExprent && ((FunctionExprent)method_object).getFuncType() == FunctionType.CAST && ((FunctionExprent)method_object).doesCast()) {
            buffer.append('(').append(instance).append(')');
          }
          else {
            buffer.append(instance);
          }
        }
        else {
          // reference to a static method or a constructor: the class is the qualifier, and the
          // type arguments recorded for the created value belong on it.
          buffer.appendCastTypeName(referenceQualifier != null
            ? referenceQualifier
            : new VarType(node.lambdaInformation.content_class_name, true));
        }

        buffer.append("::")
          .appendMethod(CodeConstants.INIT_NAME.equals(node.lambdaInformation.content_method_name) ? "new" : node.lambdaInformation.content_method_name,
            false, node.lambdaInformation.content_class_name, node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);
      }
      else {
        // lambda method
        StructMethod mt = cl.getMethod(node.lambdaInformation.content_method_key);
        MethodWrapper methodWrapper = wrapper.getMethodWrapper(mt.getName(), mt.getDescriptor());
        MethodDescriptor md_content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
        MethodDescriptor md_lambda = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);

        // javac compiles a method reference whose inference depends on the call site's target into a
        // synthetic bridge whose declared parameters differ from the functional method's. A lambda's
        // parameters are congruent with the functional method's, so the mismatch is a `::` in the
        // source; the bridge body forwards its parameters to one method, which is the reference.
        if (!lambdaToAnonymous
            && writeLambdaMethodReference(node, cl, mt, method_object, buffer, indent, md_content, md_lambda)) {
          return;
        }

        boolean simpleLambda = false;
        boolean written = false;

        if (!lambdaToAnonymous) {
          RootStatement root = wrapper.getMethodWrapper(mt.getName(), mt.getDescriptor()).root;
          if (root != null) {
            restoreFoldedInstanceField(node, methodWrapper, root);
          }
          // A lambda body is a method of its own in the class file, and a `store N; load N; ret`
          // tail inside it is the same evidence as in any method. The restore has to run with the
          // lambda's method in scope: outside it, the enclosing method's instruction table answers
          // for offsets that belong to the body.
          StructMethod outerStructMethod = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
          DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, mt);
          try {
            TryReturnFold.fold(root);
            ReturnedVariable.restore(root);
          }
          finally {
            DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, outerStructMethod);
          }
          if (DecompilerContext.getOption(IFernflowerPreferences.MARK_CORRESPONDING_SYNTHETICS)) {
            buffer.append("/* ")
              .appendMethod(node.lambdaInformation.content_method_name,
                true, node.lambdaInformation.content_class_name, node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor)
              .append(" */ ");
          }
          // Array constructor lambda
          if (md_lambda.params.length == 1 && md_lambda.params[0].equals(VarType.VARTYPE_INT) && md_lambda.ret.arrayDim > 0) {
            if (root.getFirst() instanceof BasicBlockStatement && root.getFirst().getExprents().size() == 1) {
              Exprent exp = root.getFirst().getExprents().get(0);
              if (exp instanceof ExitExprent) {
                ExitExprent exit = (ExitExprent) exp;
                Exprent returnValue = exit.getValue();
                if (returnValue instanceof NewExprent) {
                  NewExprent newExp = (NewExprent) returnValue;
                  if (newExp.getNewType().arrayDim > 0 && !newExp.isDirectArrayInit() && newExp.getLstArrayElements().isEmpty() && newExp.getLstDims().size() > 0) {
                    Exprent size = newExp.getLstDims().get(newExp.getLstDims().size() - 1);
                    if (size instanceof VarExprent) {
                      VarExprent sizeVar = (VarExprent) size;
                      // The synthetic method receives the captured values before the lambda's own
                      // parameters, so the array size is the lambda parameter only when its slot is
                      // the first of the trailing functional parameters: `size -> new T[capacity]`
                      // captures capacity and keeps the lambda form.
                      int lambdaSlot = node.lambdaInformation.is_content_method_static ? 0 : 1;
                      for (int i = 0; i < md_content.params.length - md_lambda.params.length; i++) {
                        lambdaSlot += md_content.params[i].stackSize;
                      }
                      if (sizeVar.getIndex() == lambdaSlot) {
                        VarType returnType = md_lambda.ret;
                        buffer.appendCastTypeName(returnType);
                        buffer.append("::new");
                        written = true;
                      }
                    }
                  }
                }
              }
            }
          }
          if (!written) {
            boolean lambdaParametersNeedParentheses = md_lambda.params.length != 1;
  
            if (lambdaParametersNeedParentheses) {
              buffer.append('(');
            }
  
            boolean firstParameter = true;
            int index = node.lambdaInformation.is_content_method_static ? 0 : 1;
            int start_index = md_content.params.length - md_lambda.params.length;
  
            for (int i = 0; i < md_content.params.length; i++) {
              if (i >= start_index) {
                if (!firstParameter) {
                  buffer.append(", ");
                }
                VarType type = md_content.params[i];
  
                String clashingName = methodWrapper.varproc.getClashingName(new VarVersionPair(index, 0));
                String parameterName = methodWrapper.varproc.getVarName(new VarVersionPair(index, 0));
                if (parameterName == null) {
                  parameterName = "param" + index; // null iff decompiled with errors
                }
                // Must use clashing name if it exists
                if (clashingName != null) {
                  parameterName = clashingName;
                }
                parameterName = methodWrapper.methodStruct.getVariableNamer().renameParameter(mt.getAccessFlags(), type, parameterName, index);
                buffer.appendVariable(parameterName, true, true, node.lambdaInformation.content_class_name, node.lambdaInformation.content_method_name, md_content, index, parameterName);
  
                firstParameter = false;
              }
  
              index += md_content.params[i].stackSize;
            }
  
            if (lambdaParametersNeedParentheses) {
              buffer.append(")");
            }
            buffer.append(" ->");
  
            if (DecompilerContext.getOption(IFernflowerPreferences.INLINE_SIMPLE_LAMBDAS) && methodWrapper.decompileError == null && root != null) {
              Statement firstStat = root.getFirst();
              if (firstStat instanceof BasicBlockStatement && firstStat.getExprents() != null && firstStat.getExprents().size() == 1) {
                Exprent firstExpr = firstStat.getExprents().get(0);
                boolean isVarDefinition = firstExpr instanceof AssignmentExprent &&
                  ((AssignmentExprent)firstExpr).getLeft() instanceof VarExprent &&
                  ((VarExprent)((AssignmentExprent)firstExpr).getLeft()).isDefinition();
  
                boolean isThrow = firstExpr instanceof ExitExprent &&
                  ((ExitExprent)firstExpr).getExitType() == ExitExprent.Type.THROW;
  
                if (!isVarDefinition && !isThrow) {
                  simpleLambda = true;
                  MethodWrapper outerWrapper = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
                  DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, methodWrapper);
                  StructMethod outerStruct = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
                  DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, methodWrapper.methodStruct);
                  try {
                    // The functional method's recorded return type is the target of an
                    // expression body: a poly call there can need the witness the source wrote
                    // for a type variable the arguments leave to the target.
                    VarType bodyTarget = functionalReturn;
                    if (bodyTarget instanceof GenericType wildcard) {
                      bodyTarget = wildcard.getWildcard() == GenericType.WILDCARD_EXTENDS
                        ? GenericType.withWildcard(wildcard, GenericType.WILDCARD_NO) : null;
                    }
                    if (bodyTarget != null && bodyTarget.type == CodeType.OBJECT && bodyTarget.arrayDim == 0) {
                      Exprent value = firstExpr instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN
                        ? exit.getValue() : firstExpr;
                      if (value != null) {
                        InvocationExprent.enterLambdaBody(value);
                        try {
                          value.getInferredExprType(bodyTarget);
                        } finally {
                          InvocationExprent.exitLambdaBody();
                        }
                      }
                    }
                    ExitExprent.enterLambdaReturn(bodyTarget);
                    TextBuffer codeBuffer;
                    try {
                      codeBuffer = firstExpr.toJava(indent);
                    } finally {
                      ExitExprent.exitLambdaReturn();
                    }

                    // A block lambda records a line entry at its implicit return: that entry is
                    // the closing brace's line. An expression lambda's return has no entry of
                    // its own, so only an exact entry selects the block form.
                    if (blockLambdaClosingLine(methodWrapper) >= 0) {
                      buffer.append(" {").appendLineSeparator();
                      methodLambdaToJava(node, wrapper, mt, buffer, indent + 1, !lambdaToAnonymous);
                      buffer.appendIndent(indent).append("}");
                      simpleLambda = true;
                      written = true;
                    } else {
                    // The target's lambda body may start on a later line than the expression
                    // that creates the lambda; an expression lambda prints inline otherwise.
                    // When the enclosing call already broke before this argument, the text starts
                    // on the body's line and only the argument break remains.
                    boolean breakBody = creationLine >= 0
                      && RoundTrip.methodLine(methodWrapper.methodStruct) > creationLine
                      && !InvocationExprent.argumentStartedLine();

                    if (firstExpr instanceof ExitExprent)
                      codeBuffer.setStart(6); // skip return
                    else if (!breakBody)
                      codeBuffer.prepend(" ");
                    if (breakBody) {
                      buffer.appendLineSeparator();
                    }

                    codeBuffer.addBytecodeMapping(root.getDummyExit().bytecode);
                    buffer.append(codeBuffer, node.classStruct.qualifiedName, InterpreterUtil.makeUniqueKey(methodWrapper.methodStruct.getName(), methodWrapper.methodStruct.getDescriptor()));
                    }
                  }
                  catch (CancelationManager.CanceledException e) {
                    throw e;
                  }
                  catch (Throwable ex) {
                    DecompilerContext.getLogger().writeMessage("Method " + mt.getName() + " " + mt.getDescriptor() + " in class " + node.classStruct.qualifiedName + " couldn't be written.",
                      IFernflowerLogger.Severity.WARN,
                      ex);
                    methodWrapper.decompileError = ex;
                    buffer.append(" // $VF: Couldn't be decompiled");
                  }
                  finally {
                    DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, outerWrapper);
                    DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, outerStruct);
                  }
                }
              } else if (firstStat instanceof BasicBlockStatement && firstStat.getExprents() != null && firstStat.getExprents().isEmpty()) {
                // An empty body is still a body: when the target's method starts on a later line
                // than the lambda was created on, the braces were written on that later line.
                if (creationLine >= 0 && RoundTrip.methodLine(methodWrapper.methodStruct) > creationLine) {
                  buffer.appendLineSeparator().append("{}");
                } else {
                  buffer.append(" {}");
                }
                simpleLambda = true;
              }
            }
          }
        }

        if ((!simpleLambda && !written) || lambdaToAnonymous) {
          // The target's first body line is the lambda expression's own line when the source
          // wrote `{ return ...` inline; a body starting later keeps the brace's line.
          int lambdaBodyLine = methodWrapper == null ? -1 : RoundTrip.methodLine(methodWrapper.methodStruct);
          if (creationLine >= 0 && lambdaBodyLine == creationLine) {
            buffer.append(" { ");
          } else {
            buffer.append(" {").appendLineSeparator();
          }

          VarType lambdaReturn = functionalReturn;
          if (lambdaReturn instanceof GenericType wildcard) {
            lambdaReturn = wildcard.getWildcard() == GenericType.WILDCARD_EXTENDS
              ? GenericType.withWildcard(wildcard, GenericType.WILDCARD_NO) : null;
          }
          ExitExprent.enterLambdaReturn(lambdaReturn);
          try {
            methodLambdaToJava(node, wrapper, mt, buffer, indent + 1, !lambdaToAnonymous);
          } finally {
            ExitExprent.exitLambdaReturn();
          }

          buffer.appendIndent(indent).append("}");
        }
      }
    }
    finally {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, outerNode);
    }

    DecompilerContext.getLogger().endWriteClass();
  }

  /**
   * Writes the method reference javac compiled into this synthetic lambda bridge, or returns
   * false. javac creates such a bridge when the source wrote {@code ::} and the reference's
   * inference needed the call site's target: the bridge declares the referenced method's parameter
   * types, which differ from the functional method's, while a lambda's parameters are congruent
   * with the functional method's. The bridge body must forward every declared parameter, in order,
   * to exactly one invocation; that invocation is the reference.
   */
  private boolean writeLambdaMethodReference(ClassNode node, StructClass cl, StructMethod mt,
                                             Exprent methodObject, TextBuffer buffer, int indent,
                                             MethodDescriptor md_content, MethodDescriptor md_lambda) {
    if (!RoundTrip.selector("methodrefbridge") || !node.lambdaInformation.is_content_method_static) {
      return false;
    }
    int prefix = md_content.params.length - md_lambda.params.length;
    if (prefix < 0 || prefix > 1) {
      return false;
    }
    if (prefix == 1 && methodObject == null) {
      // A bound reference's qualifier is the captured receiver; without it the text is unknown.
      return false;
    }
    boolean differs = false;
    for (int i = 0; i < md_lambda.params.length; i++) {
      if (!md_content.params[prefix + i].equals(md_lambda.params[i])) {
        differs = true;
        break;
      }
    }
    if (!differs) {
      // A lambda that captures `this` is lowered to an instance body. A static bridge whose first
      // parameter is that captured instance and whose remaining parameters are forwarded
      // unchanged is javac's lowering of a bound method reference `this::name`, whose declared
      // parameters coincide with the functional method's. A captured expression can only be an
      // invocation after the receiver-temp fold: a lambda's capture is always a local.
      if (prefix != 1 || !boundQualifier(methodObject)) {
        return false;
      }
    }
    FullInstructionSequence seq;
    try {
      mt.expandData(cl);
      seq = mt.getInstructionSequence();
    } catch (IOException e) {
      return false;
    }
    if (seq == null || seq.isEmpty()) {
      return false;
    }
    // A constructor reference: javac's bridge allocates the referenced class and hands the
    // forwarded parameters to its constructor. A lambda's body carries the functional method's
    // instantiated parameters, so the primitive or erased parameter types of the bridge are the
    // record of the adaptation a `::new` performs.
    if (RoundTrip.selector("methodrefbridge") && differs && staticNoCapture(prefix)
        && writeConstructorReference(cl, seq, md_content, buffer)) {
      return true;
    }
    // A varargs method reference: javac's bridge packs the single parameter into an array and
    // calls the varargs method with it. A lambda's body has the functional method's own parameter
    // types, so only a reference (whose bridge widens them) shows up with `differs` set. The
    // varargs method may be static or an instance method on a captured receiver.
    if (RoundTrip.selector("methodrefvarargs") && differs && prefix <= 1
        && (prefix == 0 ? methodObject == null : methodObject != null)
        && writeVarargsForward(cl, seq, md_content, md_lambda, prefix, methodObject, buffer, indent)) {
      return true;
    }
    int index = 0;
    int paramIndex = 0;
    int slot = 0;
    boolean sawLoad = false;
    String receiverCast = null;
    String[] argCasts = new String[md_content.params.length];
    while (index < seq.length()) {
      Instruction ins = seq.getInstr(index);
      Integer load = loadSlot(ins);
      if (load != null) {
        if (paramIndex >= md_content.params.length || load != slot) {
          return false;
        }
        slot += md_content.params[paramIndex].stackSize;
        paramIndex++;
        sawLoad = true;
        index++;
      } else if (ins.opcode == CodeConstants.opc_checkcast && sawLoad) {
        // The reference's declared parameter type narrows a forwarded value; the cast belongs to
        // the reference, not to the printed text.
        if (paramIndex >= 1 && paramIndex <= md_content.params.length) {
          argCasts[paramIndex - 1] = cl.getPool().getPrimitiveConstant(ins.operand(0)).getString();
        }
        if (paramIndex == 1) {
          receiverCast = argCasts[0];
        }
        index++;
      } else {
        break;
      }
    }
    // A congruent bound reference to a varargs method packs an empty trailing array after the
    // forwarded parameters (`iconst_0; anewarray A`, `expr::getPath` against
    // `getPath(String, String...)`). Only a reference bridge whose qualifier is not a capture
    // reaches this shape with `differs` clear; the same bytes under `differs` belong to a lambda
    // that must keep printing as one, so the pack is accepted only here.
    String packedType = null;
    if (!differs && index + 1 < seq.length() && intConstant(seq.getInstr(index)) == 0
        && seq.getInstr(index + 1).opcode == CodeConstants.opc_anewarray) {
      packedType = cl.getPool().getPrimitiveConstant(seq.getInstr(index + 1).operand(0)).getString();
      index += 2;
    }
    if (paramIndex != md_content.params.length || index >= seq.length()) {
      return false;
    }
    Instruction call = seq.getInstr(index);
    boolean staticCall = call.opcode == CodeConstants.opc_invokestatic;
    if (!staticCall && call.opcode != CodeConstants.opc_invokevirtual
        && call.opcode != CodeConstants.opc_invokeinterface
        && call.opcode != CodeConstants.opc_invokespecial) {
      return false;
    }
    LinkConstant target = cl.getPool().getLinkConstant(call.operand(0));
    if (target == null || target.elementname == null || target.descriptor == null) {
      return false;
    }
    MethodDescriptor md_target = MethodDescriptor.parseDescriptor(target.descriptor);
    int passed = staticCall ? md_content.params.length : md_content.params.length - 1;
    if (passed < 0 || md_target.params.length != passed + (packedType == null ? 0 : 1)) {
      return false;
    }
    if (packedType != null) {
      // The packed array is the varargs method's last parameter, holding the forwarded value's
      // element type.
      VarType packedParam = md_target.params[passed];
      if (packedParam == null || packedParam.arrayDim != 1 || !packedType.equals(packedParam.value)) {
        return false;
      }
    }
    // A static bridge with a capture that calls a static method forwards captured values into
    // arguments, which is a lambda body, not a reference.
    if (staticCall && prefix > 0) {
      return false;
    }
    // The printed `::` must be applicable where the bridge was: every instantiated functional
    // parameter has to be passable to the referenced method's parameter, and an unbound receiver
    // to the type the body casts it to. A wildcard-erased lambda with a cast is not a reference.
    // An unbound reference spends its first functional parameter as the receiver; a bound one
    // passes its captured receiver and every functional parameter as an argument.
    int argBase = !staticCall && prefix == 0 ? 1 : 0;
    for (int i = argBase; i < md_lambda.params.length; i++) {
      VarType targetParam = md_target.params[i - argBase];
      // A static bridge that casts its forwarded argument to exactly the referenced method's
      // parameter type is adapting the functional parameter's intersection-bound erasure: the
      // source's reference was applicable through the cast, which javac inserted itself.
      boolean adapted = staticCall && prefix == 0 && argCasts[i] != null
        && targetParam != null && targetParam.type == CodeType.OBJECT && targetParam.arrayDim == 0
        && argCasts[i].equals(targetParam.value);
      if (!passable(md_lambda.params[i], targetParam) && !adapted) {
        return false;
      }
    }
    if (!staticCall) {
      VarType receiverType = prefix == 1
        ? methodObject.getInferredExprType(md_content.params[0])
        : md_lambda.params[0];
      String owner = prefix == 0 && receiverCast != null ? receiverCast : target.classname;
      // A checkcast the bridge applies to its forwarded receiver is javac's own adaptation of an
      // unbound reference whose parameter is an intersection type: the source named the cast's
      // type, and the reference was applicable there through the parameter's recorded bounds.
      // The cast to the method's own owner is that record, and the erasure of the functional
      // parameter (Enum) is not an instance of it.
      boolean castProvesReceiver = prefix == 0 && receiverCast != null && receiverCast.equals(target.classname);
      if (!castProvesReceiver
        && (receiverType == null || receiverType.type != CodeType.OBJECT
            || !DecompilerContext.getStructContext().instanceOf(receiverType.value, owner))) {
        return false;
      }
    }
    index++;
    while (index < seq.length() && (seq.getInstr(index).opcode == CodeConstants.opc_checkcast
        || seq.getInstr(index).opcode == CodeConstants.opc_pop)) {
      index++;
    }
    // javac adapts a primitive/wrapper return mismatch inside the bridge (`isFocused()Z` against
    // a Supplier): the reference itself performs that adaptation at the call site, so the boxing
    // or unboxing conversion is the compiler's, not a statement the source wrote.
    index = skipReturnConversion(cl, seq, index, call);
    while (index < seq.length() && (seq.getInstr(index).opcode == CodeConstants.opc_checkcast
        || seq.getInstr(index).opcode == CodeConstants.opc_pop)) {
      index++;
    }
    if (index + 1 != seq.length() || !isReturn(seq.getInstr(index).opcode)) {
      return false;
    }

    if (prefix == 0) {
      // A static method reference or an unbound instance method reference: the owner is the name.
      buffer.appendCastTypeName(new VarType(target.classname, true));
      buffer.append("::").appendMethod(target.elementname, false, target.classname,
        target.elementname, target.descriptor);
      return true;
    }
    // Bound to the captured receiver (`expr::name`); a cast instance stays parenthesized.
    methodObject.getInferredExprType(md_content.params[0]);
    TextBuffer instance = methodObject.toJava(indent);
    if (methodObject instanceof FunctionExprent function && function.getFuncType() == FunctionType.CAST
        && function.doesCast()) {
      buffer.append('(').append(instance).append(')');
    } else {
      buffer.append(instance);
    }
    buffer.append("::").appendMethod(target.elementname, false, target.classname,
      target.elementname, target.descriptor);
    return true;
  }

  /**
   * The index after a primitive/wrapper conversion javac inserts between a method reference's
   * bridge call and its return: {@code Boolean.valueOf(Z)Boolean} when the referenced method
   * returns a primitive and the functional method returns the wrapper, or {@code intValue()I}
   * for the reverse. Anything else leaves the index where it was.
   */
  private static int skipReturnConversion(StructClass cl, FullInstructionSequence seq, int index,
                                          Instruction call) {
    if (index >= seq.length()) {
      return index;
    }
    Instruction conversion = seq.getInstr(index);
    boolean boxing = conversion.opcode == CodeConstants.opc_invokestatic;
    if (!boxing && conversion.opcode != CodeConstants.opc_invokevirtual) {
      return index;
    }
    LinkConstant callTarget = cl.getPool().getLinkConstant(call.operand(0));
    LinkConstant conversionTarget = cl.getPool().getLinkConstant(conversion.operand(0));
    if (callTarget == null || callTarget.descriptor == null || conversionTarget == null
        || conversionTarget.descriptor == null || conversionTarget.elementname == null) {
      return index;
    }
    MethodDescriptor callDescriptor = MethodDescriptor.parseDescriptor(callTarget.descriptor);
    MethodDescriptor md = MethodDescriptor.parseDescriptor(conversionTarget.descriptor);
    if (callDescriptor.ret == null || callDescriptor.ret.arrayDim != 0 || md.ret == null
        || md.ret.arrayDim != 0) {
      return index;
    }
    if (boxing) {
      // The wrapper's valueOf takes exactly the referenced method's primitive return.
      if (!"valueOf".equals(conversionTarget.elementname) || md.params.length != 1
          || md.params[0] == null || md.params[0].arrayDim != 0
          || wrapperPrimitive(md.ret.value) != callDescriptor.ret.type) {
        return index;
      }
      return index + 1;
    }
    // Unboxing: the referenced method returned the wrapper the functional method narrows.
    if (md.params.length != 0 || wrapperPrimitive(callDescriptor.ret.value) != md.ret.type
        || !conversionTarget.elementname.endsWith("Value")) {
      return index;
    }
    return index + 1;
  }

  /** The primitive a wrapper class boxes, or null when the class is not a wrapper. */
  private static CodeType wrapperPrimitive(String className) {
    return switch (className) {
      case "java/lang/Boolean" -> CodeType.BOOLEAN;
      case "java/lang/Byte" -> CodeType.BYTE;
      case "java/lang/Character" -> CodeType.CHAR;
      case "java/lang/Short" -> CodeType.SHORT;
      case "java/lang/Integer" -> CodeType.INT;
      case "java/lang/Long" -> CodeType.LONG;
      case "java/lang/Float" -> CodeType.FLOAT;
      case "java/lang/Double" -> CodeType.DOUBLE;
      default -> null;
    };
  }

  /** The value of a small integer constant instruction, or Integer.MIN_VALUE. */
  private static int intConstant(Instruction ins) {
    int op = ins.opcode;
    if (op >= CodeConstants.opc_iconst_m1 && op <= CodeConstants.opc_iconst_5) {
      return op - CodeConstants.opc_iconst_0;
    }
    if (op == CodeConstants.opc_bipush || op == CodeConstants.opc_sipush) {
      return ins.operand(0);
    }
    return Integer.MIN_VALUE;
  }

  private static boolean staticNoCapture(int prefix) {
    return prefix == 0;
  }

  /**
   * Whether a captured receiver can be printed as the qualifier of `expr::name`: the receiver
   * `this`, or an invocation the receiver-temp fold put in the capture's place. A lambda
   * expression's capture is always a local, so an invocation here is that fold's marker.
   */
  private static boolean boundQualifier(Exprent methodObject) {
    return methodObject instanceof InvocationExprent
      || methodObject instanceof VarExprent receiver && "this".equals(receiver.getName());
  }

  /**
   * Writes a varargs method reference whose bridge packs the single functional argument into a
   * one-element array. The bridge's shape is {@code [receiver;] iconst_1; anewarray A; dup;
   * iconst_0; load x; aastore; invoke [A]; [pop]; return}: javac lowers {@code Type::name} or
   * {@code recv::name} against a functional parameter narrower than the varargs method's element
   * type into exactly this body. Returns false when the body differs.
   */
  private boolean writeVarargsForward(StructClass cl, FullInstructionSequence seq, MethodDescriptor md_content,
                                      MethodDescriptor md_lambda, int prefix, Exprent methodObject,
                                      TextBuffer buffer, int indent) {
    if (md_content.params.length != prefix + 1 || md_lambda.params.length != 1
        || seq.length() < prefix + 8) {
      return false;
    }
    int index = 0;
    if (prefix == 1) {
      Integer receiver = loadSlot(seq.getInstr(index));
      if (receiver == null || receiver != 0) {
        return false;
      }
      index++;
    }
    int elementSlot = prefix == 1 ? md_content.params[0].stackSize : 0;
    if (intConstant(seq.getInstr(index)) != 1
        || seq.getInstr(index + 1).opcode != CodeConstants.opc_anewarray
        || seq.getInstr(index + 2).opcode != CodeConstants.opc_dup
        || intConstant(seq.getInstr(index + 3)) != 0
        || loadSlot(seq.getInstr(index + 4)) == null
        || loadSlot(seq.getInstr(index + 4)) != elementSlot
        || seq.getInstr(index + 5).opcode != CodeConstants.opc_aastore) {
      return false;
    }
    int callIndex = index + 6;
    Instruction call = seq.getInstr(callIndex);
    boolean staticCall = call.opcode == CodeConstants.opc_invokestatic;
    if (!staticCall && call.opcode != CodeConstants.opc_invokevirtual
        && call.opcode != CodeConstants.opc_invokeinterface) {
      return false;
    }
    LinkConstant target = cl.getPool().getLinkConstant(call.operand(0));
    if (target == null || target.elementname == null || target.descriptor == null) {
      return false;
    }
    MethodDescriptor md_target = MethodDescriptor.parseDescriptor(target.descriptor);
    if (md_target.params.length != 1 || md_target.params[0].arrayDim != 1) {
      return false;
    }
    String arrayType = cl.getPool().getPrimitiveConstant(seq.getInstr(index + 1).operand(0)).getString();
    if (!md_target.params[0].value.equals(arrayType)) {
      return false;
    }
    VarType element = md_target.params[0].decreaseArrayDim();
    if (!passable(md_lambda.params[0], element)) {
      return false;
    }
    int tail = callIndex + 1;
    while (tail < seq.length() && (seq.getInstr(tail).opcode == CodeConstants.opc_pop
        || seq.getInstr(tail).opcode == CodeConstants.opc_pop2)) {
      tail++;
    }
    if (tail + 1 != seq.length() || !isReturn(seq.getInstr(tail).opcode)) {
      return false;
    }
    if (staticCall) {
      if (prefix != 0) {
        return false;
      }
      buffer.appendCastTypeName(new VarType(target.classname, true));
      buffer.append("::").appendMethod(target.elementname, false, target.classname,
        target.elementname, target.descriptor);
      return true;
    }
    // The receiver is the captured value; its type must be an instance of the method's owner.
    VarType receiverType = methodObject.getInferredExprType(md_content.params[0]);
    if (receiverType == null || receiverType.type != CodeType.OBJECT
      || !DecompilerContext.getStructContext().instanceOf(receiverType.value, target.classname)) {
      return false;
    }
    TextBuffer instance = methodObject.toJava(indent);
    if (methodObject instanceof FunctionExprent function && function.getFuncType() == FunctionType.CAST
        && function.doesCast()) {
      buffer.append('(').append(instance).append(')');
    } else {
      buffer.append(instance);
    }
    buffer.append("::").appendMethod(target.elementname, false, target.classname,
      target.elementname, target.descriptor);
    return true;
  }

  /**
   * Writes a constructor reference whose bridge allocates the class and forwards the functional
   * arguments to its constructor: {@code new T; dup; load...; invokespecial T.<init>; areturn}.
   * javac creates this bridge when the reference needs an adaptation (a primitive parameter where
   * the functional method instantiates a wrapper), which is what the bridge's parameter types
   * record; a lambda's body carries the functional method's own types instead.
   */
  private boolean writeConstructorReference(StructClass cl, FullInstructionSequence seq,
                                            MethodDescriptor md_content, TextBuffer buffer) {
    if (seq.length() < 5
        || seq.getInstr(0).opcode != CodeConstants.opc_new
        || seq.getInstr(1).opcode != CodeConstants.opc_dup) {
      return false;
    }
    String created = cl.getPool().getPrimitiveConstant(seq.getInstr(0).operand(0)).getString();
    int index = 2;
    int paramIndex = 0;
    int slot = 0;
    while (paramIndex < md_content.params.length) {
      if (index >= seq.length()) {
        return false;
      }
      Integer load = loadSlot(seq.getInstr(index));
      if (load == null || load != slot) {
        return false;
      }
      slot += md_content.params[paramIndex].stackSize;
      paramIndex++;
      index++;
    }
    if (seq.getInstr(index).opcode != CodeConstants.opc_invokespecial) {
      return false;
    }
    LinkConstant constructor = cl.getPool().getLinkConstant(seq.getInstr(index).operand(0));
    if (constructor == null || !CodeConstants.INIT_NAME.equals(constructor.elementname)
      || constructor.descriptor == null || !created.equals(constructor.classname)) {
      return false;
    }
    MethodDescriptor md_constructor = MethodDescriptor.parseDescriptor(constructor.descriptor);
    if (md_constructor.params.length != md_content.params.length) {
      return false;
    }
    for (int i = 0; i < md_content.params.length; i++) {
      if (!md_content.params[i].equals(md_constructor.params[i])) {
        return false;
      }
    }
    index++;
    if (index + 1 != seq.length() || seq.getInstr(index).opcode != CodeConstants.opc_areturn) {
      return false;
    }
    buffer.appendCastTypeName(new VarType(created, true)).append("::new");
    return true;
  }

  /** Whether an expression of type {@code from} is passable to {@code to} without a cast. */
  private static boolean passable(VarType from, VarType to) {
    if (from == null || to == null || from.isGeneric() || to.isGeneric()) {
      return false;
    }
    if (from.equals(to)) {
      return true;
    }
    if (from.type != CodeType.OBJECT || to.type != CodeType.OBJECT
        || from.value == null || to.value == null) {
      return false;
    }
    return DecompilerContext.getStructContext().instanceOf(from.value, to.value);
  }

  /** The local slot an instruction loads, or null when it is not a load. */
  private static Integer loadSlot(Instruction ins) {
    int op = ins.opcode;
    if (op >= CodeConstants.opc_iload && op <= CodeConstants.opc_aload) {
      return ins.operand(0);
    }
    if (op >= CodeConstants.opc_iload_0 && op <= CodeConstants.opc_aload_3) {
      return (op - CodeConstants.opc_iload_0) % 4;
    }
    return null;
  }

  private static boolean isReturn(int opcode) {
    return opcode == CodeConstants.opc_return || opcode == CodeConstants.opc_areturn
      || opcode == CodeConstants.opc_ireturn || opcode == CodeConstants.opc_lreturn
      || opcode == CodeConstants.opc_freturn || opcode == CodeConstants.opc_dreturn;
  }

  public void writeClassHeader(StructClass cl, TextBuffer buffer, ImportCollector importCollector) {
    int index = cl.qualifiedName.lastIndexOf('/');
    if (index >= 0) {
      String packageName = cl.qualifiedName.substring(0, index).replace('/', '.');
      buffer.append("package ").append(packageName).append(';').appendLineSeparator().appendLineSeparator();
    }

    importCollector.writeImports(buffer, true);
  }

  public void writeClass(ClassNode node, TextBuffer buffer, int indent) {
    ClassNode outerNode = (ClassNode)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
    // A class body printed inside a lambda body is not that lambda: its returns belong to their
    // own method, and the functional method's type can even be void there.
    VarType outerLambdaReturn = ExitExprent.takeLambdaReturn();

    try {
      // last minute processing
      boolean ok = invokeProcessors(buffer, node);

      if (!ok) {
        return;
      }

      ClassWrapper wrapper = node.getWrapper();
      StructClass cl = wrapper.getClassStruct();

      DecompilerContext.getLogger().startWriteClass(cl.qualifiedName);

      if (DecompilerContext.getOption(IFernflowerPreferences.SOURCE_FILE_COMMENTS)) {
        StructSourceFileAttribute sourceFileAttr = node.classStruct
          .getAttribute(StructGeneralAttribute.ATTRIBUTE_SOURCE_FILE);

        if (sourceFileAttr != null) {
          ConstantPool pool = node.classStruct.getPool();
          String sourceFile = sourceFileAttr.getSourceFile(pool);

          buffer
            .appendIndent(indent)
            .append("// $VF: Compiled from " + sourceFile)
            .appendLineSeparator();
        }
      }

      // write class definition
      writeClassDefinition(node, buffer, indent);

      final AtomicBoolean hasContent = new AtomicBoolean(false);
      // writeClassDefinition will skip adding a trailing newline for anonymous classes.
      // This allows us to only add it if we end up writing any content for the class, so something
      // like `new Object() {}` will not have a newline in between `{` and `}`.
      // The runnable should be executed immediately before writing any anonymous class content to the buffer.
      // hasContent also fills a similar purpose, determining whether elements need an extra newline prepended due to previous content being written.
      final Runnable haveContent = () -> {
        if (!hasContent.get() && node.type == ClassNode.Type.ANONYMOUS) {
          buffer.appendLineSeparator();
        }
        hasContent.set(true);
      };

      String methodToDecompile = (String) DecompilerContext.getProperty(IFernflowerPreferences.METHOD_TO_DECOMPILE);

      // fields
      List<StructRecordComponent> components = methodToDecompile.isEmpty() ? cl.getRecordComponents() : null;
      List<StructField> nonEnumFields = new ArrayList<>();
      if (methodToDecompile.isEmpty()) {
        List<StructField> enumFields = new ArrayList<>();

        for (StructField fd : cl.getFields()) {
          boolean isEnum = fd.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);
          if (isEnum) {
            enumFields.add(fd);
          } else {
            nonEnumFields.add(fd);
          }
        }

        boolean enums = false;
        for (StructField fd : enumFields) {
          if (enums) {
            buffer.append(',').appendLineSeparator();
          }
          enums = true;

          haveContent.run();
          writeField(buffer, indent, fd, wrapper);
        }

        if (enums) {
          buffer.append(';').appendLineSeparator();
        }
      }

      VBStyleCollection<StructMethod, String> methods = cl.getMethods();
      List<Integer> methodOrder = methodWriteOrder(node, methods);

      // The class file lists every member class last, but the source may have declared it between
      // two methods, and a member's first line in the target's table says where. Printing in that
      // order is what lets javac reproduce the original line table and nesting order.
      List<int[]> plan = new ArrayList<>();
      java.util.Set<Integer> blockSequences = new java.util.HashSet<>();
      boolean ordered = RoundTrip.selector("rt-member-order");
      int sequence = 0;
      for (int i = 0; i < nonEnumFields.size(); i++) {
        plan.add(new int[]{0, i, ordered ? fieldLine(wrapper, cl, nonEnumFields.get(i)) : -1, sequence++});
      }
      for (int i : methodOrder) {
        StructMethod mt = methods.get(i);
        int line = ordered ? methodLine(mt) : -1;
        boolean enumBlock = false;
        if (ordered && !"off".equals(System.getenv("NEUROFLOWER_ENUMBLOCK"))
            && CodeConstants.CLINIT_NAME.equals(mt.getName())) {
          int block = staticBlockLine(wrapper, cl);
          if (block >= 0) {
            line = block;
            enumBlock = true;
          } else {
            // A plain class's static block is not at <clinit> offset 0: the field initializers
            // are inlined first, each on its own declaration line. The block starts at the first
            // entry that no field accounts for; ranking it by offset 0 would pull it in front of
            // every method declared between the last field and the block.
            int own = staticBlockOwnLine(wrapper, cl);
            if (own >= 0) {
              line = own;
            }
          }
        }
        if (enumBlock) {
          blockSequences.add(sequence);
        }
        plan.add(new int[]{1, i, line, sequence++});
      }
      // The target's NestMembers lists the nested types in reverse declaration order; a member
      // class without a line table of its own (an annotation type, say) cannot be placed by its
      // first line and needs this rank to keep the original's declaration order.
      Map<String, Integer> nestRank = new java.util.HashMap<>();
      StructNestMembersAttribute nestMembers =
        cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_NEST_MEMBERS);
      if (nestMembers != null) {
        java.util.List<String> names = nestMembers.getClasses(cl.getPool());
        for (int i = 0; i < names.size(); i++) {
          nestRank.put(names.get(i), names.size() - 1 - i);
        }
      }
      for (int i = 0; i < node.nested.size(); i++) {
        ClassNode inner = node.nested.get(i);
        int rank = inner.type == ClassNode.Type.MEMBER && inner.classStruct != null
          ? nestRank.getOrDefault(inner.classStruct.qualifiedName, Integer.MAX_VALUE) : Integer.MAX_VALUE;
        plan.add(new int[]{2, i, ordered && inner.type == ClassNode.Type.MEMBER ? classLine(inner) : -1, sequence++, rank});
      }
      if (ordered) {
        // A member class with no line table of its own is placed next to the member class the
        // original declared just before it, which the target's NestMembers names.
        java.util.List<int[]> ranked = new java.util.ArrayList<>(); // {rank, known line}
        for (int[] member : plan) {
          if (member[0] == 2 && member.length > 4 && member[4] != Integer.MAX_VALUE && member[2] >= 0) {
            ranked.add(new int[]{member[4], member[2]});
          }
        }
        ranked.sort(Comparator.comparingInt(a -> a[0]));
        for (int[] member : plan) {
          if (member[0] != 2 || member[2] >= 0 || member.length <= 4 || member[4] == Integer.MAX_VALUE) {
            continue;
          }
          int line = -1;
          for (int[] known : ranked) {
            if (known[0] < member[4]) {
              line = known[1];
            }
          }
          if (line < 0) {
            // Declared before every member class that has a line: share the nearest later one,
            // and the rank order in the sort keeps it in front.
            for (int[] known : ranked) {
              if (known[0] > member[4]) {
                line = known[1];
                break;
              }
            }
          }
          member[2] = line;
        }
        // A member class with no line and no member class to be ranked against has no evidence
        // of where it sat among the methods: the plan's own order is the class file's, which
        // lists member classes after every member. Give it a line after all of them rather than
        // the last method's, which its NestMembers rank would otherwise sort it in front of.
        boolean rankedMemberClass = false;
        for (int[] member : plan) {
          if (member[0] == 2 && member.length > 4 && member[4] != Integer.MAX_VALUE && member[2] >= 0) {
            rankedMemberClass = true;
            break;
          }
        }
        boolean tailMembers = RoundTrip.selector("rt-member-tail");
        int maxFieldLine = -1;
        for (int[] member : plan) {
          if (member[0] == 0 && member[2] >= 0) {
            maxFieldLine = Math.max(maxFieldLine, member[2]);
          }
        }
        // The legacy arrangement, kept to restore an unlined method that the rule below would
        // otherwise move across a member class (RecipeProvider's buildRecipes past Runner).
        int planSize = plan.size();
        int[] original = new int[planSize];
        int[] legacy = new int[planSize];
        for (int i = 0; i < planSize; i++) {
          original[i] = plan.get(i)[2];
          legacy[i] = original[i];
        }
        int legacyCarry = -1;
        for (int i = 0; i < planSize; i++) {
          if (legacy[i] < 0) {
            if (tailMembers && plan.get(i)[0] == 2 && !rankedMemberClass) {
              continue;
            }
            legacy[i] = legacyCarry;
          } else {
            legacyCarry = legacy[i];
          }
        }
        legacyCarry = Integer.MAX_VALUE;
        for (int i = planSize - 1; i >= 0; i--) {
          if (legacy[i] < 0) {
            legacy[i] = legacyCarry;
          } else {
            legacyCarry = legacy[i];
          }
        }
        // A constructor's line is the class or initializer anchor, not a declaration position:
        // when a field follows it, carrying it to an unlined member pulls that member in front of
        // the field the source declared first (RuleTest's CODEC). Without such a field the old
        // behaviour stands.
        int carried = -1;
        // An interface has no constructor to anchor an unlined method, and a preceding static
        // method's line is not where the source put it: the field's initializer line is the only
        // declaration evidence left, and the source declared such methods after the field.
        boolean noCtor = true;
        for (int i : methodOrder) {
          if (CodeConstants.INIT_NAME.equals(methods.get(i).getName())) {
            noCtor = false;
            break;
          }
        }
        // Members with no line of their own stay next to the neighbour that has one.
        for (int[] member : plan) {
          if (member[2] < 0) {
            if (tailMembers && member[0] == 2 && !rankedMemberClass) {
              continue; // the backward pass puts it after every lined member
            }
            member[2] = noCtor && member[0] == 1 && maxFieldLine > carried ? maxFieldLine : carried;
          } else if (!(isCtorMember(member, methods) && maxFieldLine > member[2])) {
            carried = member[2];
          }
        }
        carried = Integer.MAX_VALUE;
        for (int i = plan.size() - 1; i >= 0; i--) {
          int[] member = plan.get(i);
          if (member[2] < 0) {
            member[2] = carried;
          } else if (!(isCtorMember(member, methods) && maxFieldLine > member[2])) {
            carried = member[2];
          }
        }
        // An unlined method the rule moved past a member class goes back to its legacy line.
        for (int i = 0; i < planSize; i++) {
          if (original[i] >= 0 || plan.get(i)[0] != 1 || plan.get(i)[2] <= legacy[i]) {
            continue;
          }
          for (int j = 0; j < planSize; j++) {
            if (plan.get(j)[0] == 2 && node.nested.get(plan.get(j)[1]).type == ClassNode.Type.MEMBER
              && legacy[j] > legacy[i] && legacy[j] <= plan.get(i)[2]) {
              plan.get(i)[2] = legacy[i];
              break;
            }
          }
        }
        // A member with no line of its own — a method without code, a field without an initializer
        // line — has no evidence of where the source put it, and the carry above hands it a
        // neighbour's line. When that line would sort it after a member the class file lists
        // later, the source cannot have had that order: take the later neighbour's line instead,
        // and the sequence tie-break keeps the file order. This corrects the carry; it never
        // replaces a line the target actually recorded.
        if (RoundTrip.selector("memberfileorder")) {
          for (int i = 0; i < planSize; i++) {
            int[] member = plan.get(i);
            if (original[i] >= 0 || member[2] < 0 || member[0] != 1) {
              continue;
            }
            MethodWrapper wrapperOf = wrapper.getMethodWrapper(member[1]);
            if (wrapperOf != null && wrapperOf.root != null) {
              continue; // a method with code has a table of its own
            }
            // Only a leading run of code-less methods: once a method with a line has been seen,
            // the carry's placement is the one the target's own table implies.
            boolean leading = true;
            for (int j = 0; j < i; j++) {
              if (plan.get(j)[0] == 1 && original[j] >= 0) {
                leading = false;
                break;
              }
            }
            if (!leading) {
              continue;
            }
            for (int j = i + 1; j < planSize; j++) {
              // Only another method bounds a method: the class file lists fields first whatever
              // the source order, so a field's position says nothing about where a method sat.
              if (original[j] < 0 || plan.get(j)[0] != 1 || plan.get(j)[2] < 0) {
                continue;
              }
              // A constructor's or static block's line is the class header or an initializer
              // anchor, not a declaration position: neither can bound a method's place.
              StructMethod boundMethod = methods.get(plan.get(j)[1]);
              if (CodeConstants.INIT_NAME.equals(boundMethod.getName())
                  || CodeConstants.CLINIT_NAME.equals(boundMethod.getName())) {
                continue;
              }
              if (plan.get(j)[2] < member[2]) {
                member[2] = plan.get(j)[2];
              }
              break;
            }
          }
        }
        // Fields keep their declaration order: a forward reference from an initializer to a later
        // field is illegal, and their own lines are only as trustworthy as their initializers.
        int previousField = -1;
        int lastField = -1;
        for (int[] member : plan) {
          if (member[0] != 0) {
            continue;
          }
          if (previousField >= 0) {
            member[2] = Math.max(member[2], previousField);
          }
          previousField = member[2];
          lastField = Math.max(lastField, member[2]);
        }
        // A constructor or static block re-inlines the fields' initializers, so its first line
        // belongs to a field that was lifted out of it. It must stay after every field, unless it
        // is an enum's static block that provably precedes them.
        String ctorMode = System.getenv("NEUROFLOWER_CTORLINE");
        boolean ctorLine = !"off".equals(ctorMode);
        int firstField = Integer.MAX_VALUE;
        java.util.Set<Integer> fieldLineValues = new java.util.HashSet<>();
        if (ctorLine) {
          for (int[] member : plan) {
            if (member[0] == 0 && member[2] >= 0) {
              firstField = Math.min(firstField, member[2]);
              fieldLineValues.add(member[2]);
            }
          }
        }
        if (lastField >= 0) {
          for (int[] member : plan) {
            if (member[0] == 1) {
              StructMethod mt = methods.get(member[1]);
              if (CodeConstants.INIT_NAME.equals(mt.getName()) || CodeConstants.CLINIT_NAME.equals(mt.getName())) {
                // A static block's line is a real declaration line when an initializer was lifted
                // out of the block's tail: that initializer's code follows the block's, so the
                // field is declared after it (InputConstants' UNKNOWN) and the clamp would drag
                // the block past it. Without such a tail the block must stay after every field:
                // it may read a field declared below it, which only compiles after the field.
                boolean scoped = "all".equals(ctorMode) || CodeConstants.INIT_NAME.equals(mt.getName())
                  || CodeConstants.CLINIT_NAME.equals(mt.getName())
                     && endsWithLiftedInitializer(wrapper.getMethodWrapper(member[1]), wrapper);
                // A lifted initializer's line is one of the field lines; a genuine declaration
                // line that merely precedes a later field must not be dragged after it.
                boolean realLine = ctorLine && scoped && member[2] >= 0
                  && (member[2] < firstField || !fieldLineValues.contains(member[2]));
                if (!blockSequences.contains(member[3]) && !realLine) {
                  member[2] = Math.max(member[2], lastField);
                }
              }
            }
          }
        }
        plan.sort(Comparator.comparingInt((int[] m) -> m[2])
          .thenComparingInt(m -> m.length > 4 ? m[4] : Integer.MAX_VALUE)
          .thenComparingInt(m -> m[3]));
      }

      boolean enums = !nonEnumFields.isEmpty() && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM)
        && cl.getFields().stream().anyMatch(fd -> fd.hasModifier(CodeConstants.ACC_ENUM));
      for (int[] member : plan) {
        switch (member[0]) {
          case 0 -> {
            StructField fd = nonEnumFields.get(member[1]);
            boolean hide = fd.isSynthetic() && DecompilerContext.getOption(IFernflowerPreferences.REMOVE_SYNTHETIC) ||
              wrapper.getHiddenMembers().contains(InterpreterUtil.makeUniqueKey(fd.getName(), fd.getDescriptor()));
            if (hide) continue;

            if (components != null && fd.getAccessFlags() == (CodeConstants.ACC_FINAL | CodeConstants.ACC_PRIVATE) &&
              components.stream().anyMatch(c -> c.getName().equals(fd.getName()) && c.getDescriptor().equals(fd.getDescriptor()))) {
              // Record component field: skip it
              continue;
            }

            if (enums) {
              // Add an extra line break between enums and non-enum fields
              buffer.appendLineSeparator();
              enums = false;
            }

            haveContent.run();
            writeField(buffer, indent, fd, wrapper);
          }
          case 1 -> {
            int i = member[1];
            StructMethod mt = methods.get(i);
            boolean hide;
            if (methodToDecompile.isEmpty() || (node.type != ClassNode.Type.ROOT && node.type != ClassNode.Type.MEMBER)) {
              hide = mt.isSynthetic() && DecompilerContext.getOption(IFernflowerPreferences.REMOVE_SYNTHETIC) ||
                     mt.hasModifier(CodeConstants.ACC_BRIDGE) && DecompilerContext.getOption(IFernflowerPreferences.REMOVE_BRIDGE) ||
                     wrapper.getHiddenMembers().contains(InterpreterUtil.makeUniqueKey(mt.getName(), mt.getDescriptor()));
            } else {
              hide = !methodToDecompile.equals(cl.qualifiedName + "." + mt.getName() + mt.getDescriptor()) &&
                     (node.type != ClassNode.Type.ROOT || !methodToDecompile.equals(mt.getName() + mt.getDescriptor()));
            }
            if (hide) continue;

            TextBuffer methodBuffer = new TextBuffer();
            boolean methodSkipped = !writeMethod(node, mt, i, methodBuffer, indent + 1);
            if (!methodSkipped) {
              if (hasContent.get()) {
                buffer.appendLineSeparator();
              }
              haveContent.run();
              buffer.append(methodBuffer);
            }
          }
          case 2 -> {
            ClassNode inner = node.nested.get(member[1]);
            if (inner.type != ClassNode.Type.MEMBER) {
              continue;
            }
            StructClass innerCl = inner.classStruct;
            boolean hide;
            if (methodToDecompile.isEmpty()) {
              boolean isSynthetic = (inner.access & CodeConstants.ACC_SYNTHETIC) != 0 || innerCl.isSynthetic();
              hide = isSynthetic && DecompilerContext.getOption(IFernflowerPreferences.REMOVE_SYNTHETIC) ||
                     wrapper.getHiddenMembers().contains(innerCl.qualifiedName);
            } else {
              hide = !methodToDecompile.startsWith(innerCl.qualifiedName + ".");
            }
            if (hide) continue;

            if (hasContent.get()) {
              buffer.appendLineSeparator();
            }
            TextBuffer clsBuffer = new TextBuffer();
            int region = clsBuffer.beginRegion(innerCl.qualifiedName);
            try {
              writeClass(inner, clsBuffer, indent + 1);
            }
            finally {
              clsBuffer.endRegion(innerCl.qualifiedName, region);
            }
            haveContent.run();
            buffer.append(clsBuffer);
          }
          default -> {
          }
        }
      }

      if (hasContent.get() || node.type != ClassNode.Type.ANONYMOUS) {
        // Skip indent for anonymous classes with no content, since we also skipped the newline in the cls definition
        buffer.appendIndent(indent);
      }
      buffer.append('}');

      if (node.type != ClassNode.Type.ANONYMOUS) {
        buffer.appendLineSeparator();
      }
    }
    finally {
      ExitExprent.restoreLambdaReturn(outerLambdaReturn);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, outerNode);
    }

    DecompilerContext.getLogger().endWriteClass();
  }

  public static void packageInfoToJava(StructClass cl, TextBuffer buffer) {
    appendAnnotations(buffer, 0, cl, -1);

    int index = cl.qualifiedName.lastIndexOf('/');
    String packageName = cl.qualifiedName.substring(0, index).replace('/', '.');
    buffer.append("package ").append(packageName).append(';').appendLineSeparator().appendLineSeparator();
  }

  public static void moduleInfoToJava(StructClass cl, TextBuffer buffer) {
    appendAnnotations(buffer, 0, cl, -1);

    StructModuleAttribute moduleAttribute = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_MODULE);

    if ((moduleAttribute.moduleFlags & CodeConstants.ACC_OPEN) != 0) {
      buffer.append("open ");
    }

    buffer.append("module ").append(moduleAttribute.moduleName).append(" {").appendLineSeparator();

    writeModuleInfoBody(buffer, moduleAttribute);

    buffer.append('}').appendLineSeparator();
  }

  private static void writeModuleInfoBody(TextBuffer buffer, StructModuleAttribute moduleAttribute) {
    boolean newLineNeeded = false;

    List<StructModuleAttribute.RequiresEntry> requiresEntries = moduleAttribute.requires;
    if (!requiresEntries.isEmpty()) {
      for (StructModuleAttribute.RequiresEntry requires : requiresEntries) {
        if (!isGenerated(requires.flags)) {
          buffer.appendIndent(1).append("requires ");
          if ((requires.flags & CodeConstants.ACC_TRANSITIVE) != 0) {
            buffer.append("transitive ");
          }
          if ((requires.flags & CodeConstants.ACC_STATIC_PHASE) != 0) {
            buffer.append("static ");
          }
          buffer.append(requires.moduleName.replace('/', '.')).append(';').appendLineSeparator();
          newLineNeeded = true;
        }
      }
    }

    List<StructModuleAttribute.ExportsEntry> exportsEntries = moduleAttribute.exports;
    if (!exportsEntries.isEmpty()) {
      if (newLineNeeded) buffer.appendLineSeparator();
      for (StructModuleAttribute.ExportsEntry exports : exportsEntries) {
        if (!isGenerated(exports.flags)) {
          buffer.appendIndent(1).append("exports ").append(exports.packageName.replace('/', '.'));
          List<String> exportToModules = exports.exportToModules;
          if (exportToModules.size() > 0) {
            buffer.append(" to").appendLineSeparator();
            appendFQClassNames(buffer, exportToModules);
          }
          buffer.append(';').appendLineSeparator();
          newLineNeeded = true;
        }
      }
    }

    List<StructModuleAttribute.OpensEntry> opensEntries = moduleAttribute.opens;
    if (!opensEntries.isEmpty()) {
      if (newLineNeeded) buffer.appendLineSeparator();
      for (StructModuleAttribute.OpensEntry opens : opensEntries) {
        if (!isGenerated(opens.flags)) {
          buffer.appendIndent(1).append("opens ").append(opens.packageName.replace('/', '.'));
          List<String> opensToModules = opens.opensToModules;
          if (opensToModules.size() > 0) {
            buffer.append(" to").appendLineSeparator();
            appendFQClassNames(buffer, opensToModules);
          }
          buffer.append(';').appendLineSeparator();
          newLineNeeded = true;
        }
      }
    }

    List<String> usesEntries = moduleAttribute.uses;
    if (!usesEntries.isEmpty()) {
      if (newLineNeeded) buffer.appendLineSeparator();
      for (String uses : usesEntries) {
        buffer.appendIndent(1).append("uses ").append(ExprProcessor.buildJavaClassName(uses)).append(';').appendLineSeparator();
      }
      newLineNeeded = true;
    }

    List<StructModuleAttribute.ProvidesEntry> providesEntries = moduleAttribute.provides;
    if (!providesEntries.isEmpty()) {
      if (newLineNeeded) buffer.appendLineSeparator();
      for (StructModuleAttribute.ProvidesEntry provides : providesEntries) {
        buffer.appendIndent(1).append("provides ").append(ExprProcessor.buildJavaClassName(provides.interfaceName)).append(" with").appendLineSeparator();
        appendFQClassNames(buffer, provides.implementationNames.stream().map(ExprProcessor::buildJavaClassName).collect(Collectors.toList()));
        buffer.append(';').appendLineSeparator();
      }
    }
  }

  private static boolean isGenerated(int flags) {
    return (flags & (CodeConstants.ACC_SYNTHETIC | CodeConstants.ACC_MANDATED)) != 0;
  }

  private void writeClassDefinition(ClassNode node, TextBuffer buffer, int indent) {
    boolean markSynthetics = DecompilerContext.getOption(IFernflowerPreferences.MARK_CORRESPONDING_SYNTHETICS);
    ClassWrapper wrapper = node.getWrapper();
    StructClass cl = wrapper.getClassStruct();

    if (node.type == ClassNode.Type.ANONYMOUS) {
      if (markSynthetics) {
        appendSyntheticClassComment(cl, buffer);
      }
      buffer.append(" {");
      // Omit trailing newline, will be added by the caller if there is any content in the class
      return;
    }

    int flags = node.type == ClassNode.Type.ROOT ? cl.getAccessFlags() : node.access;
    boolean isDeprecated = cl.hasAttribute(StructGeneralAttribute.ATTRIBUTE_DEPRECATED);
    boolean isSynthetic = (flags & CodeConstants.ACC_SYNTHETIC) != 0 || cl.hasAttribute(StructGeneralAttribute.ATTRIBUTE_SYNTHETIC);
    boolean isEnum = DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM) && (flags & CodeConstants.ACC_ENUM) != 0;
    boolean isInterface = (flags & CodeConstants.ACC_INTERFACE) != 0;
    boolean isAnnotation = (flags & CodeConstants.ACC_ANNOTATION) != 0;
    boolean isModuleInfo = (flags & CodeConstants.ACC_MODULE) != 0 && cl.hasAttribute(StructGeneralAttribute.ATTRIBUTE_MODULE);
    StructPermittedSubclassesAttribute permittedSubClassesAttr = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_PERMITTED_SUBCLASSES);
    List<String> permittedSubClasses = permittedSubClassesAttr != null ? permittedSubClassesAttr.getClasses() : Collections.emptyList();
    boolean isSealed = permittedSubClassesAttr != null && !permittedSubClasses.isEmpty();
    boolean isFinal = (flags & CodeConstants.ACC_FINAL) != 0;
    boolean isNonSealed = !isSealed && !isFinal && cl.getVersion().hasSealedClasses() && isSuperClassSealed(cl);

    if (isDeprecated) {
      if (!containsDeprecatedAnnotation(cl)) {
        appendDeprecation(buffer, indent);
      }
    }

    // Classes defined inside of interfaces are implicitly public/static (JLS 9.5 Member Type Declarations)
    if (
      node.type == ClassNode.Type.MEMBER &&
      (node.parent.getWrapper().getClassStruct().getAccessFlags() & CodeConstants.ACC_INTERFACE) != 0
    ) {
      flags &= ~CodeConstants.ACC_PUBLIC;
      flags &= ~CodeConstants.ACC_STATIC;
    }

    if (interceptor != null) {
      String oldName = interceptor.getOldName(cl.qualifiedName);
      appendRenameComment(buffer, oldName, MType.CLASS, indent);
    }

    if (isSynthetic) {
      appendComment(buffer, "synthetic class", indent);
    }

    if (javadocProvider != null) {
      appendJavadoc(buffer, javadocProvider.getClassJavadocStyle(cl), javadocProvider.getClassDoc(cl), indent);
    }

    appendAnnotations(buffer, indent, cl, -1);

    buffer.appendIndent(indent);

    if (isEnum) {
      // remove abstract and final flags (JLS 8.9 Enums)
      flags &= ~CodeConstants.ACC_ABSTRACT;
      flags &= ~CodeConstants.ACC_FINAL;

      // remove implicit static flag for local enums (JLS 14.3 Local class and interface declarations)
      if (node.type == ClassNode.Type.MEMBER || node.type == ClassNode.Type.LOCAL) {
        flags &= ~CodeConstants.ACC_STATIC;
      }
    }

    List<StructRecordComponent> components = cl.getRecordComponents();

    if (components != null) {
      // records are implicitly static and final
      flags &= ~CodeConstants.ACC_FINAL;
      flags &= ~CodeConstants.ACC_STATIC;
    }

    appendModifiers(buffer, flags, CLASS_ALLOWED, isInterface, CLASS_EXCLUDED);

    if (!isEnum && isSealed) {
      buffer.append("sealed ");
    } else if (isNonSealed) {
      buffer.append("non-sealed ");
    }
    if (isEnum) {
      buffer.append("enum ");
    }
    else if (isInterface) {
      if (isAnnotation) {
        buffer.append('@');
      }
      buffer.append("interface ");
    }
    else if (isModuleInfo) {
      StructModuleAttribute moduleAttribute = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_MODULE);

      if ((moduleAttribute.moduleFlags & CodeConstants.ACC_OPEN) != 0) {
        buffer.append("open ");
      }

      buffer.append("module ");
      buffer.append(moduleAttribute.moduleName);
    }
    else if (components != null) {
      buffer.append("record ");
    }
    else {
      buffer.append("class ");
    }
    buffer.appendClass(node.simpleName, true, cl.qualifiedName);

    GenericClassDescriptor descriptor = cl.getSignature();
    if (descriptor != null) {
      VarType superclass = new VarType(cl.superClass.getString(), true);
      List<VarType> interfaces = Arrays.stream(cl.getInterfaceNames())
        .map(s -> new VarType(s, true))
        .toList();

      descriptor.verifyTypes(superclass, interfaces);
    }

    if (descriptor != null && !descriptor.fparameters.isEmpty()) {
      appendTypeParameters(buffer, descriptor.fparameters, descriptor.fbounds);
    }

    if (components != null) {
      buffer.append('(');
      RecordHelper.appendRecordComponents(buffer, cl, components, indent);
      buffer.append(')');
    }

    buffer.pushNewlineGroup(indent, 1);

    if (!isEnum && !isInterface && components == null && cl.superClass != null) {
      VarType supertype = new VarType(cl.superClass.getString(), true);
      if (!VarType.VARTYPE_OBJECT.equals(supertype)) {
        buffer.appendPossibleNewline(" ");
        buffer.append("extends ");
        buffer.appendCastTypeName(descriptor == null ? supertype : descriptor.superclass);
      }
    }

    if (!isAnnotation) {
      int[] interfaces = cl.getInterfaces();
      if (interfaces.length > 0) {
        buffer.appendPossibleNewline(" ");
        buffer.append(isInterface ? "extends " : "implements ");
        for (int i = 0; i < interfaces.length; i++) {
          if (i > 0) {
            buffer.append(",");
            buffer.appendPossibleNewline(" ");
          }

          if (descriptor == null || descriptor.superinterfaces.size() > i) {
            buffer.appendCastTypeName(descriptor == null ? new VarType(cl.getInterface(i), true) : descriptor.superinterfaces.get(i));
          }
        }
      }
    }

    if (!isEnum && isSealed) {
      buffer.appendPossibleNewline(" ");
      buffer.append("permits ");
      for (int i = 0; i < permittedSubClasses.size(); i++) {
        if (i > 0) {
          buffer.append(",");
          buffer.appendPossibleNewline(" ");
        }
        buffer.appendCastTypeName(new VarType(permittedSubClasses.get(i), true));
      }
    }

    buffer.popNewlineGroup();

    if (markSynthetics && node.type == ClassNode.Type.LOCAL) {
      appendSyntheticClassComment(cl, buffer);
    }

    buffer.append(" {").appendLineSeparator();
  }

  private static boolean isSuperClassSealed(StructClass cl) {
    if (cl.superClass != null) {
      StructClass superClass = DecompilerContext.getStructContext().getClass((String) cl.superClass.value);
      if (superClass != null && superClass.hasAttribute(StructGeneralAttribute.ATTRIBUTE_PERMITTED_SUBCLASSES)) {
        return true;
      }
    }
    for (String iface : cl.getInterfaceNames()) {
      StructClass ifaceClass = DecompilerContext.getStructContext().getClass(iface);
      if (ifaceClass != null && ifaceClass.hasAttribute(StructGeneralAttribute.ATTRIBUTE_PERMITTED_SUBCLASSES)) {
        return true;
      }
    }
    return false;
  }

  private void writeField(TextBuffer buffer, int indent, StructField fd, ClassWrapper wrapper) {
    TextBuffer fieldBuffer = new TextBuffer();
    // A static field's initializer, and every enum constant, lives in <clinit>; an instance
    // initializer keeps the constructor's offsets. Printing either needs that method's line table
    // for its argument and chain breaks. Fields are written outside any method's context, where
    // the previous method would otherwise supply the wrong lines -- or none at all.
    StructMethod outerStruct = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    StructMethod context = fd.hasModifier(CodeConstants.ACC_STATIC)
      ? wrapper.getClassStruct().getMethod(CodeConstants.CLINIT_NAME, "()V")
      : wrapper.getDynamicInitializerOwner();
    if (context != null) {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, context);
    }
    try {
      writeField(wrapper, wrapper.getClassStruct(), fd, fieldBuffer, indent + 1);
    } finally {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, outerStruct);
    }
    // An instance initializer's offsets belong to whichever constructor it was lifted out of; the
    // key names the field so the line aligner can recover that constructor from the table alone.
    String initializer = fd.hasModifier(CodeConstants.ACC_STATIC)
      ? "<clinit> ()V" : "<field-init " + fd.getName() + ">";
    buffer.append(fieldBuffer, wrapper.getClassStruct().qualifiedName, initializer);
  }

  public void writeField(ClassWrapper wrapper, StructClass cl, StructField fd, TextBuffer buffer, int indent) {
    if (RecordHelper.isHiddenRecordField(cl.getRecordComponents(), fd)) {
      return;
    }

    boolean isInterface = cl.hasModifier(CodeConstants.ACC_INTERFACE);
    boolean isDeprecated = fd.hasAttribute(StructGeneralAttribute.ATTRIBUTE_DEPRECATED);
    boolean isEnum = fd.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);

    if (isDeprecated) {
      if (!containsDeprecatedAnnotation(fd)) {
        appendDeprecation(buffer, indent);
      }
    }

    String name = fd.getName();
    if (interceptor != null) {
      String newName = interceptor.getName(cl.qualifiedName + " " + fd.getName() + " " + fd.getDescriptor());

      if (newName != null) {
        name = newName.split(" ")[1];
      }
    }

    if (interceptor != null) {
      String oldName = interceptor.getOldName(cl.qualifiedName + " " + name + " " + fd.getDescriptor());
      appendRenameComment(buffer, oldName, MType.FIELD, indent);
    }

    if (fd.isSynthetic()) {
      appendComment(buffer, "synthetic field", indent);
    }

    if (javadocProvider != null) {
      appendJavadoc(buffer, javadocProvider.getFieldJavadocStyle(cl, fd), javadocProvider.getFieldDoc(cl, fd), indent);
    }
    Set<String> writtenAnnotations = appendAnnotations(buffer, indent, fd, TypeAnnotation.FIELD);

    buffer.appendIndent(indent);

    if (!isEnum) {
      appendModifiers(buffer, fd.getAccessFlags(), FIELD_ALLOWED, isInterface, FIELD_EXCLUDED);
    }

    Map.Entry<VarType, GenericFieldDescriptor> fieldTypeData = getFieldTypeData(fd);
    VarType fieldType = fieldTypeData.getKey();
    GenericFieldDescriptor descriptor = fieldTypeData.getValue();
    if (descriptor != null) {
      descriptor.verifyType(cl.getSignature(), fieldType);
    }

    if (!isEnum) {
      var annos = getTypeAnnotations(fd, TypeAnnotation.FIELD, -1);
      if (!annos.isEmpty()) {
        buffer.appendCastTypeName(descriptor == null ? fieldType : descriptor.type, annos, writtenAnnotations);
      } else {
        buffer.appendCastTypeName(descriptor == null ? fieldType : descriptor.type);
      }

      buffer.append(' ');
    }

    buffer.appendField(name, true, cl.qualifiedName, name, fd.getDescriptor());

    Exprent initializer;
    if (fd.hasModifier(CodeConstants.ACC_STATIC)) {
      initializer = wrapper.getStaticFieldInitializers().getWithKey(InterpreterUtil.makeUniqueKey(fd.getName(), fd.getDescriptor()));
    }
    else {
      initializer = wrapper.getDynamicFieldInitializers().getWithKey(InterpreterUtil.makeUniqueKey(fd.getName(), fd.getDescriptor()));
    }

    if (initializer != null) {
      if (isEnum && initializer instanceof NewExprent) {
        NewExprent expr = (NewExprent)initializer;
        expr.setEnumConst(true);
        // The constant's construction runs in <clinit> but belongs to the constant's own line;
        // the synthetic values()/$values() methods are anchored to that same first line.
        if (expr.bytecode != null) {
          buffer.addBytecodeMapping(expr.bytecode);
        }
        buffer.append(expr.toJava(indent));
      }
      else {
        // A lifted initializer keeps the offsets of the method it came from; its instructions
        // belong to this declaration's line, both in a constructor and in <clinit>.
        if (initializer.bytecode != null) {
          buffer.addBytecodeMapping(initializer.bytecode);
        }
        // A chained initializer's creation prologue (the `new`) is the receiver chain's root,
        // and the target attributes it to the declaration's line; the top-level set omits it,
        // so the declaration would have no anchor. Creations inside arguments belong to their
        // own chain lines and must not be claimed here.
        Exprent root = initializer;
        while (root instanceof InvocationExprent invocation && invocation.getInstance() != null) {
          root = invocation.getInstance();
        }
        if (root instanceof NewExprent created && created.bytecode != null) {
          buffer.addBytecodeMapping(created.bytecode);
        }
        buffer.append(" = ");

        if (initializer instanceof ConstExprent) {
          ((ConstExprent) initializer).adjustConstType(fieldType);
        }

        ExprProcessor.getCastedExprent(initializer, descriptor == null ? fieldType : descriptor.type, buffer, indent, false);
      }
    }
    else if (fd.hasModifier(CodeConstants.ACC_FINAL) && fd.hasModifier(CodeConstants.ACC_STATIC)) {
      StructConstantValueAttribute attr = fd.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
      if (attr != null) {
        PrimitiveConstant constant = cl.getPool().getPrimitiveConstant(attr.getIndex());
        buffer.append(" = ");
        buffer.append(new ConstExprent(fieldType, constant.value, null).toJava(indent));
      }
    }

    if (!isEnum) {
      buffer.append(";").appendLineSeparator();
    }
  }

  private static void methodLambdaToJava(ClassNode lambdaNode,
                                         ClassWrapper classWrapper,
                                         StructMethod mt,
                                         TextBuffer buffer,
                                         int indent,
                                         boolean codeOnly) {
    MethodWrapper methodWrapper = classWrapper.getMethodWrapper(mt.getName(), mt.getDescriptor());

    MethodWrapper outerWrapper = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, methodWrapper);
    StructMethod outerStruct = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, methodWrapper.methodStruct);

    try {
      String method_name = lambdaNode.lambdaInformation.method_name;
      MethodDescriptor md_content = MethodDescriptor.parseDescriptor(lambdaNode.lambdaInformation.content_method_descriptor);
      MethodDescriptor md_lambda = MethodDescriptor.parseDescriptor(lambdaNode.lambdaInformation.method_descriptor);

      if (!codeOnly) {
        buffer.appendIndent(indent);
        buffer.append("public ");
        buffer.append(method_name);
        buffer.append("(");

        boolean firstParameter = true;
        int index = lambdaNode.lambdaInformation.is_content_method_static ? 0 : 1;
        int start_index = md_content.params.length - md_lambda.params.length;

        for (int i = 0; i < md_content.params.length; i++) {
          if (i >= start_index) {
            if (!firstParameter) {
              buffer.append(", ");
            }

            VarType type = md_content.params[i];
            String typeName = ExprProcessor.getCastTypeName(type);
            if (ExprProcessor.UNDEFINED_TYPE_STRING.equals(typeName) &&
                DecompilerContext.getOption(IFernflowerPreferences.UNDEFINED_PARAM_TYPE_OBJECT)) {
              typeName = ExprProcessor.getCastTypeName(VarType.VARTYPE_OBJECT);
            }

            buffer.appendCastTypeName(typeName, type);
            buffer.append(" ");

            String parameterName = methodWrapper.varproc.getVarName(new VarVersionPair(index, 0));
            if (parameterName == null) {
              parameterName = "param" + index; // null iff decompiled with errors
            }
            parameterName = methodWrapper.methodStruct.getVariableNamer().renameParameter(mt.getAccessFlags(), type, parameterName, index);
            buffer.appendVariable(parameterName, true, true, classWrapper.getClassStruct().qualifiedName, method_name, md_content, index, parameterName);

            firstParameter = false;
          }

          index += md_content.params[i].stackSize;
        }

        buffer.append(") {").appendLineSeparator();

        indent += 1;
      }

      RootStatement root = classWrapper.getMethodWrapper(mt.getName(), mt.getDescriptor()).root;
      if (methodWrapper.decompileError == null) {
        if (root != null) { // check for existence
          try {
            TryReturnFold.fold(root);
            ReturnedVariable.restore(root);
            // A lambda body is a method of its own in the class file: its local table proves the
            // declaration order the same way, and the context is the lambda's own method here.
            LocalDeclarationOrder.reorder(root);
            TextBuffer childBuf = root.toJava(indent);
            childBuf.addBytecodeMapping(root.getDummyExit().bytecode);
            buffer.append(childBuf, classWrapper.getClassStruct().qualifiedName, InterpreterUtil.makeUniqueKey(mt.getName(), mt.getDescriptor()));
          }
          catch (CancelationManager.CanceledException e) {
            throw e;
          }
          catch (Throwable t) {
            String message = "Method " + mt.getName() + " " + mt.getDescriptor() + " in class " + lambdaNode.classStruct.qualifiedName + " couldn't be written.";
            DecompilerContext.getLogger().writeMessage(message, IFernflowerLogger.Severity.WARN, t);
            methodWrapper.decompileError = t;
          }
        }
      }

      if (methodWrapper.decompileError != null) {
        dumpError(buffer, methodWrapper, indent);
      }

      if (!codeOnly) {
        indent -= 1;
        buffer.appendIndent(indent).append('}').appendLineSeparator();
      }
    }
    finally {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, outerWrapper);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, outerStruct);
    }
  }

  public static String toValidJavaIdentifier(String name) {
    if (name == null || name.isEmpty()) return name;

    boolean changed = false;
    StringBuilder res = new StringBuilder(name.length());
    for (int i = 0; i < name.length(); i++) {
      char c = name.charAt(i);
      if ((i == 0 && !Character.isJavaIdentifierStart(c))
          || (i > 0 && !Character.isJavaIdentifierPart(c))) {
        changed = true;
        res.append("_");
      }
      else {
        res.append(c);
      }
    }
    if (!changed) {
      return name;
    }
    return res.toString();
  }

  public boolean writeMethod(ClassNode node, StructMethod mt, int methodIndex, TextBuffer buffer, int indent) {
    ClassWrapper wrapper = node.getWrapper();
    StructClass cl = wrapper.getClassStruct();
    // Get method by index, this keeps duplicate methods (with the same key) separate
    MethodWrapper methodWrapper = wrapper.getMethodWrapper(methodIndex);

    boolean hideMethod = false;

    MethodWrapper outerWrapper = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, methodWrapper);
    StructMethod outerStruct = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, methodWrapper.methodStruct);

    try {
      boolean isInterface = cl.hasModifier(CodeConstants.ACC_INTERFACE);
      boolean isAnnotation = cl.hasModifier(CodeConstants.ACC_ANNOTATION);
      boolean isEnum = cl.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);
      boolean isDeprecated = mt.hasAttribute(StructGeneralAttribute.ATTRIBUTE_DEPRECATED);
      boolean clInit = false, init = false, dInit = false;
      int declStart = -1;

      MethodDescriptor md = MethodDescriptor.parseDescriptor(mt, node);

      int flags = mt.getAccessFlags();
      if ((flags & CodeConstants.ACC_NATIVE) != 0) {
        flags &= ~CodeConstants.ACC_STRICT; // compiler bug: a strictfp class sets all methods to strictfp
      }
      if (CodeConstants.CLINIT_NAME.equals(mt.getName())) {
        flags &= CodeConstants.ACC_STATIC; // ignore all modifiers except 'static' in a static initializer
      }

      if (isDeprecated) {
        if (!containsDeprecatedAnnotation(mt)) {
          appendDeprecation(buffer, indent);
        }
      }

      String name = mt.getName();
      if (interceptor != null) {
        String newName = interceptor.getName(cl.qualifiedName + " " + mt.getName() + " " + mt.getDescriptor());

        if (newName != null) {
          name = newName.split(" ")[1];
        }
      }

      if (interceptor != null) {
        String oldName = interceptor.getOldName(cl.qualifiedName + " " + name + " " + mt.getDescriptor());
        appendRenameComment(buffer, oldName, MType.METHOD, indent);
      }

      boolean isSynthetic = (flags & CodeConstants.ACC_SYNTHETIC) != 0 || mt.hasAttribute(StructGeneralAttribute.ATTRIBUTE_SYNTHETIC);
      boolean isBridge = (flags & CodeConstants.ACC_BRIDGE) != 0;
      if (isSynthetic) {
        appendComment(buffer, "synthetic method", indent);
      }
      if (isBridge) {
        appendComment(buffer, "bridge method", indent);
      }

      if (DecompilerContext.getOption(IFernflowerPreferences.DECOMPILER_COMMENTS) && methodWrapper.addErrorComment || methodWrapper.commentLines != null) {
        if (methodWrapper.addErrorComment) {
          for (String s : ClassWriter.getErrorComment()) {
            methodWrapper.addComment(s);
          }
        }

        for (String s : methodWrapper.commentLines) {
          buffer.appendIndent(indent).append("// " + s).appendLineSeparator();
        }
      }

      if (javadocProvider != null) {
        appendJavadoc(buffer, javadocProvider.getMethodJavadocStyle(cl, mt), javadocProvider.getMethodDoc(cl, mt), indent);
      }

      Set<String> writtenAnnotations = appendAnnotations(buffer, indent, mt, TypeAnnotation.METHOD_RETURN_TYPE);

      StructAnnotationAttribute annotationAttribute = mt.getAttribute(StructGeneralAttribute.ATTRIBUTE_RUNTIME_VISIBLE_ANNOTATIONS);
      boolean shouldApplyOverride = DecompilerContext.getOption(IFernflowerPreferences.OVERRIDE_ANNOTATION)
          && mt.getBytecodeVersion().hasOverride()
          && !CodeConstants.INIT_NAME.equals(mt.getName())
          && !CodeConstants.CLINIT_NAME.equals(mt.getName())
          && !mt.hasModifier(CodeConstants.ACC_STATIC)
          && !mt.hasModifier(CodeConstants.ACC_PRIVATE);

      // Try append @Override after all other annotations
      if (shouldApplyOverride) {
        // Search superclasses for methods that match the name and descriptor of this one.
        // Make sure not to search the current class otherwise it will return the current method itself!
        // TODO: record overrides
        boolean isOverride = searchForMethod(cl, mt.getName(), md, false);
        boolean alreadyHasOverride = annotationAttribute != null && annotationAttribute.getAnnotations()
                .stream().anyMatch(annotation -> "java/lang/Override".equals(annotation.getClassName()));

        if (isOverride && !alreadyHasOverride) {
          buffer.appendIndent(indent);
          buffer.append("@Override");
          buffer.appendLineSeparator();
        }
      }

      buffer.appendIndent(indent);

      if (CodeConstants.INIT_NAME.equals(name)) {
        declStart = buffer.length();
        // Enum constructors are implicitly private
        if (isEnum) {
          flags &= ~CodeConstants.ACC_PRIVATE;
        }

        if (node.type == ClassNode.Type.ANONYMOUS) {
          name = "";
          dInit = true;
        } else {
          name = node.simpleName;
          init = true;
        }
      } else if (CodeConstants.CLINIT_NAME.equals(name)) {
        name = "";
        clInit = true;
      }

      if (!dInit) {
        appendModifiers(buffer, flags, METHOD_ALLOWED, isInterface, METHOD_EXCLUDED);
      }

      if (isInterface && !mt.hasModifier(CodeConstants.ACC_STATIC) && mt.containsCode() && (flags & CodeConstants.ACC_PRIVATE) == 0) {
        // 'default' modifier (Java 8)
        buffer.append("default ");
      }

      GenericMethodDescriptor descriptor = md.genericInfo;
      if (descriptor != null) {
        List<VarType> params = new ArrayList<>(Arrays.asList(md.params));

        if (init && node.classStruct.hasModifier(CodeConstants.ACC_ENUM)) {
          // Enum name and ordinal parameters need to be explicitly excluded
          params.remove(0);
          params.remove(0);
        }

        if (params.size() != descriptor.parameterTypes.size()) {
          // Exclude any parameters that the signature itself won't contain
          List<VarVersionPair> mask = methodWrapper.synthParameters;
          if (mask != null) {
            for (int i = 0, j = 0; i < mask.size(); i++, j++) {
              if (mask.get(i) != null) {
                params.remove(j--);
              }
            }
          }
        }

        StructExceptionsAttribute attr = mt.getAttribute(StructGeneralAttribute.ATTRIBUTE_EXCEPTIONS);
        List<VarType> exceptions = new ArrayList<>();
        if (attr != null) {
          for (int i = 0; i < attr.getThrowsExceptions().size(); i++) {
            exceptions.add(new VarType(attr.getExcClassname(i, node.classStruct.getPool()), true));
          }
        }

        GenericsChecker checker = new GenericsChecker();

        ClassNode currentNode = node;
        loop: while (currentNode != null) {
          if (currentNode.enclosingMethod != null && currentNode.parent != null) {
            StructMethod enclosingMethod = currentNode.parent.classStruct.getMethod(currentNode.enclosingMethod);
            if (enclosingMethod != null) {
              if (enclosingMethod.getSignature() != null) {
                checker = checker.copy(enclosingMethod.getSignature().typeParameters, enclosingMethod.getSignature().typeParameterBounds);
              }

              if (currentNode.parent != null) {
                for (ClassNode child : currentNode.parent.nested) {
                  if (child.type != ClassNode.Type.LAMBDA) {
                    continue;
                  }

                  // Lambdas lose context because anonymous classes within them are children of the lambda's parent,
                  // instead of the fake lambda ClassNode generated by Vineflower.
                  // Add the best-guess-lambda to the permitted generics tree by visiting it before parents.

                  if (!currentNode.enclosingMethod.equals(child.lambdaInformation.content_method_key)) {
                    continue;
                  }

                  if (child.lambdaInformation.content_method_invocation_type == CodeConstants.CONSTANT_MethodHandle_REF_newInvokeSpecial) {
                    // for ::new references, require the class to also be the same
                    if (!currentNode.parent.classStruct.qualifiedName.equals(child.lambdaInformation.content_class_name)) {
                      continue;
                    }
                  }

                  currentNode = child;
                  continue loop;
                }
              }
            }
          }

          GenericClassDescriptor parentSignature = currentNode.classStruct.getSignature();
          if (parentSignature != null) {
            checker = checker.copy(parentSignature.getChecker());
          }

          currentNode = currentNode.parent;
        }

        descriptor.verifyTypes(checker, params, mt.methodDescriptor().ret, exceptions);
      }

      boolean throwsExceptions = false;
      int paramCount = 0;

      if (!clInit && !dInit) {
        boolean thisVar = !mt.hasModifier(CodeConstants.ACC_STATIC);

        if (descriptor != null && !descriptor.typeParameters.isEmpty()) {
          appendTypeParameters(buffer, descriptor.typeParameters, descriptor.typeParameterBounds);
          buffer.append(' ');
        }

        if (!init) {
          var annos = getTypeAnnotations(mt, TypeAnnotation.METHOD_RETURN_TYPE, -1);
          if (!annos.isEmpty()) {
            buffer.appendCastTypeName(descriptor == null ? md.ret : descriptor.returnType, annos, writtenAnnotations);
          } else {
            buffer.appendCastTypeName(descriptor == null ? md.ret : descriptor.returnType);
          }
          buffer.append(' ');
        }

        String validName = toValidJavaIdentifier(name);
        buffer.appendMethod(validName, true, cl.qualifiedName, mt.getName(), md);
        if (!validName.equals(name)) {
          buffer.append("/* $VF was: ").append(name).append(" */");
        }

        if (!methodWrapper.isCompactRecordConstructor) {
          paramCount = writeMethodParameterHeader(mt, buffer, indent, methodWrapper, md, isEnum, init, thisVar, descriptor, paramCount, isInterface, flags, cl);
        }

        StructExceptionsAttribute attr = mt.getAttribute(StructGeneralAttribute.ATTRIBUTE_EXCEPTIONS);
        if ((descriptor != null && !descriptor.exceptionTypes.isEmpty()) || attr != null) {
          throwsExceptions = true;
          buffer.append(" throws ");

          boolean useDescriptor = descriptor != null && !descriptor.exceptionTypes.isEmpty();
          for (int i = 0; i < (attr == null ? descriptor.exceptionTypes.size() : attr.getThrowsExceptions().size()); i++) {
            if (i > 0) {
              buffer.append(", ");
            }
            VarType type = useDescriptor ? descriptor.exceptionTypes.get(i) : new VarType(attr.getExcClassname(i, cl.getPool()), true);
            buffer.appendCastTypeName(type);
          }
        }
      }

      if ((flags & (CodeConstants.ACC_ABSTRACT | CodeConstants.ACC_NATIVE)) != 0) { // native or abstract method (explicit or interface)
        if (isAnnotation) {
          StructAnnDefaultAttribute attr = mt.getAttribute(StructGeneralAttribute.ATTRIBUTE_ANNOTATION_DEFAULT);
          if (attr != null) {
            buffer.append(" default ");
            buffer.append(attr.getDefaultValue().toJava(0));
          }
        }

        buffer.append(';');
        buffer.appendLineSeparator();
      }
      else {
        if (!clInit && !dInit) {
          buffer.append(' ');
        }

        // We do not have line information for method start, lets have it here for now
        buffer.append('{').appendLineSeparator();

        RootStatement root = methodWrapper.root;

        if (root != null && methodWrapper.decompileError == null) { // check for existence
          try {
            // Avoid generating imports for ObjectMethods during root.toJava(...)
            if (RecordHelper.isHiddenRecordMethod(cl, mt, root)) {
              hideMethod = true;
            } else {
              if (System.getenv("NEUROFLOWER_TREE_DEBUG") != null
                  && (System.getenv("NEUROFLOWER_TREE_DEBUG").isEmpty()
                      || System.getenv("NEUROFLOWER_TREE_DEBUG").equals(mt.getName()))) {
                System.err.println("TREE " + mt.getName() + mt.getDescriptor());
                dumpStat(root, 0);
              }
              TryReturnFold.fold(root);
              ReturnedVariable.restore(root);
              LocalDeclarationOrder.reorder(root);
              TextBuffer code = root.toJava(indent + 1);
              appendUndeclaredLocals(buffer, mt, md, cl, indent + 1);
              ClassNode orphan = node.orphanLambdas.get(InterpreterUtil.makeUniqueKey(mt.getName(), mt.getDescriptor()));
              if (orphan != null) {
                writeOrphanLambda(wrapper, methodWrapper, orphan, buffer, indent + 1);
              }
              if (!clInit || !endsWithLiftedInitializer(methodWrapper, wrapper)) {
                code.addBytecodeMapping(root.getDummyExit().bytecode);
              }
              hideMethod = code.length() == 0 && (clInit || dInit || hideConstructor(node, init, throwsExceptions, paramCount, flags, mt));
              // javac puts a constructor's pc0 on its declaration line unless the body opens with
              // an explicit this(...)/super(...) call, which makes the call's line pc0's instead.
              if (init && declStart >= 0 && !startsWithDelegation(root)) {
                buffer.addBytecodeMappingAt(declStart, 0, cl.qualifiedName,
                  InterpreterUtil.makeUniqueKey(mt.getName(), mt.getDescriptor()));
              }
              buffer.append(code, cl.qualifiedName, InterpreterUtil.makeUniqueKey(mt.getName(), mt.getDescriptor()));
            }
          }
          catch (CancelationManager.CanceledException e) {
            throw e;
          }
          catch (Throwable t) {
            String message = "Method " + mt.getName() + " " + mt.getDescriptor() + " in class " + node.classStruct.qualifiedName + " couldn't be written.";
            DecompilerContext.getLogger().writeMessage(message, IFernflowerLogger.Severity.WARN, t);
            methodWrapper.decompileError = t;
          }
        }

        if (methodWrapper.decompileError != null) {
          dumpError(buffer, methodWrapper, indent + 1);
        }
        buffer.appendIndent(indent).append('}').appendLineSeparator();
      }
    }
    finally {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, outerWrapper);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, outerStruct);
    }

    // save total lines
    // TODO: optimize
    //tracer.setCurrentSourceLine(buffer.countLines(start_index_method));

    return !hideMethod;
  }

  /**
   * Prints a lambda whose content method the class file keeps but whose creation site Lower
   * removed — javac desugars every lambda before it prunes a branch whose condition is constant
   * false, so the method survives with nothing referring to it. The dead block is printed at the
   * head of the owning method under that same constant condition, which emits no bytecode; the
   * lambda in it is lowered back into the method the class file records.
   *
   * <p>The body goes through the ordinary lambda path, so its instructions carry the orphan's own
   * method key and LineAlign places them on the orphan's line table. The functional parameter's
   * name is the one the method's local table records, because that name is written into the
   * recompiled method's table. The declared local and the interface name are not recorded
   * anywhere in the class file: the block is dead, so its shape is what a compiler checks and
   * never emits.
   */
  private void writeOrphanLambda(ClassWrapper wrapper, MethodWrapper owner, ClassNode orphan,
                                 TextBuffer buffer, int indent) {
    StructClass cl = wrapper.getClassStruct();
    StructMethod mt = cl.getMethod(orphan.lambdaInformation.content_method_key);
    if (mt == null) {
      return;
    }
    MethodWrapper methodWrapper = wrapper.getMethodWrapper(mt.getName(), mt.getDescriptor());
    if (methodWrapper == null || methodWrapper.root == null || methodWrapper.decompileError != null) {
      return;
    }

    MethodDescriptor mdContent = MethodDescriptor.parseDescriptor(orphan.lambdaInformation.content_method_descriptor);
    int samIndex = mdContent.params.length - 1;
    VarType samType = mdContent.params[samIndex];
    int slot = 0;
    for (int i = 0; i < samIndex; i++) {
      slot += mdContent.params[i].stackSize;
    }
    String parameter = methodWrapper.varproc.getVarName(new VarVersionPair(slot, 0));
    if (parameter == null || parameter.isEmpty()) {
      return;
    }

    VarType sam = new GenericType(CodeType.OBJECT, 0, "java/util/function/Consumer", null,
      List.of(samType), GenericType.WILDCARD_NO);

    buffer.appendIndent(indent).append("if (false) {").appendLineSeparator();
    buffer.appendIndent(indent + 1).appendCastTypeName(sam).append(' ')
      .append(orphanLocalName(owner, methodWrapper, parameter)).append(" = ")
      .append(parameter).append(" -> {").appendLineSeparator();
    methodLambdaToJava(orphan, wrapper, mt, buffer, indent + 2, true);
    buffer.appendIndent(indent + 1).append("};").appendLineSeparator();
    buffer.appendIndent(indent).append("}").appendLineSeparator();
  }

  /** A local name for the dead block that no name in either method can collide with. */
  private static String orphanLocalName(MethodWrapper owner, MethodWrapper orphan, String parameter) {
    Set<String> used = new HashSet<>();
    used.add(parameter);
    used.addAll(owner.varproc.getVarNames());
    used.addAll(orphan.varproc.getVarNames());
    String name = "visitor";
    while (used.contains(name)) {
      name += "_";
    }
    return name;
  }

  /**
   * A local the target declared but never used leaves exactly one trace: the class's max_locals
   * is larger than every slot the parameters, the code and the local table reference. javac
   * allocates a slot when it reaches a declaration, and a variable that is never assigned writes
   * no instruction, no table entry and no line; the declaration is the only source form that
   * produces such a slot. Print it back, or the recompiled method reports fewer locals than the
   * target and the code attribute differs. Only a plain (non-generic) first parameter type is
   * printed: a generic signature would make the erased name a raw type, which changes lint.
   */
  private static void appendUndeclaredLocals(TextBuffer buffer, StructMethod mt, MethodDescriptor md,
                                             StructClass cl, int indent) {
    int maxLocals = mt.getLocalVariables();
    if (maxLocals <= 0 || !mt.containsCode()
        || CodeConstants.INIT_NAME.equals(mt.getName()) || CodeConstants.CLINIT_NAME.equals(mt.getName())) {
      return;
    }
    int used = mt.hasModifier(CodeConstants.ACC_STATIC) ? 0 : 1;
    for (VarType param : md.params) {
      used += param.stackSize;
    }
    StructLocalVariableTableAttribute table = mt.getLocalVariableAttr();
    if (table != null) {
      for (StructLocalVariableTableAttribute.LocalVariable var : table.getVariables().toList()) {
        used = Math.max(used, var.getIndex() + var.getVarType().stackSize);
      }
    }
    if (used >= maxLocals) {
      return;
    }
    // The gap so far may be a compiler temporary (an exception handler's store, a switch's
    // selector); only a slot no instruction ever references is a declaration's.
    FullInstructionSequence seq = mt.getInstructionSequence();
    if (seq == null) {
      try {
        mt.expandData(cl);
      } catch (IOException e) {
        return;
      }
      seq = mt.getInstructionSequence();
    }
    if (seq == null) {
      return;
    }
    for (int i = 0; i < seq.length(); i++) {
      Instruction instr = seq.getInstr(i);
      int slot = variableSlot(instr);
      if (slot >= 0) {
        used = Math.max(used, slot + variableWidth(instr));
      }
    }
    if (used >= maxLocals) {
      return;
    }
    if (md.params.length == 0 || md.genericInfo != null || md.params[0].stackSize != 1
        || md.params[0].arrayDim > 0) {
      return;
    }
    String typeName = ExprProcessor.getCastTypeName(md.params[0]);
    if (ExprProcessor.isInvalidTypeName(typeName)) {
      return;
    }
    if (table != null && table.containsName("var" + used)) {
      return;
    }
    for (int slot = used; slot < maxLocals; slot++) {
      buffer.appendIndent(indent).append(typeName).append(" var").append(slot).append(";").appendLineSeparator();
    }
  }

  /** The slot a load, store, iinc or ret reads or writes, or -1 when the instruction is not one. */
  private static int variableSlot(Instruction instr) {
    int opcode = instr.opcode;
    if ((opcode >= CodeConstants.opc_iload && opcode <= CodeConstants.opc_aload)
        || (opcode >= CodeConstants.opc_istore && opcode <= CodeConstants.opc_astore)
        || opcode == CodeConstants.opc_iinc || opcode == CodeConstants.opc_ret) {
      return instr.operandsCount() > 0 ? instr.operand(0) : -1;
    }
    return -1;
  }

  /** The number of slots a variable instruction occupies. */
  private static int variableWidth(Instruction instr) {
    int opcode = instr.opcode;
    return opcode == CodeConstants.opc_lload || opcode == CodeConstants.opc_dload
      || opcode == CodeConstants.opc_lstore || opcode == CodeConstants.opc_dstore ? 2 : 1;
  }

  /** Developer aid: NEUROFLOWER_TREE_DEBUG=<method name> prints the statement tree before printing. */
  private static void dumpStat(Statement stat, int depth) {
    StringBuilder line = new StringBuilder();
    for (int i = 0; i < depth; i++) {
      line.append("  ");
    }
    line.append(stat).append(" first=").append(RoundTrip.firstOffset(stat))
      .append(" lastEnd=").append(RoundTrip.lastEnd(stat))
      .append(" defs=").append(stat.getVarDefinitions().size());
    System.err.println(line);
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        StringBuilder entry = new StringBuilder();
        for (int i = 0; i <= depth; i++) {
          entry.append("  ");
        }
        String bits;
        try {
          bits = String.valueOf(exprent.bytecode);
        } catch (RuntimeException e) {
          bits = "?";
        }
        if (bits.length() > 60) {
          bits = bits.substring(0, 60) + "...";
        }
        String text;
        try (var v = DecompilerContext.getImportCollector().lock()) {
          text = exprent.toJava(0).convertToStringAndAllowDataDiscard();
        } catch (RuntimeException e) {
          text = "<" + e + ">";
        }
        if (text.length() > 120) {
          text = text.substring(0, 120);
        }
        entry.append(exprent.getClass().getSimpleName()).append(' ').append(bits).append(" :: ").append(text);
        System.err.println(entry);
      }
    }
    for (Statement child : stat.getStats()) {
      dumpStat(child, depth + 1);
    }
    for (org.jetbrains.java.decompiler.modules.decompiler.StatEdge edge : stat.getAllSuccessorEdges()) {
      StringBuilder entry = new StringBuilder();
      for (int i = 0; i <= depth; i++) {
        entry.append("  ");
      }
      entry.append("-> ").append(edge.getType()).append(' ').append(edge.getDestination());
      System.err.println(entry);
    }
  }

  private static int writeMethodParameterHeader(StructMethod mt, TextBuffer buffer, int indent, MethodWrapper methodWrapper, MethodDescriptor md, boolean isEnum, boolean init, boolean thisVar, GenericMethodDescriptor descriptor, int paramCount, boolean isInterface, int flags, StructClass cl) {
    buffer.append('(');

    List<VarVersionPair> mask = methodWrapper.synthParameters;

    int lastVisibleParameterIndex = -1;
    for (int i = 0; i < md.params.length; i++) {
      if (mask == null || mask.get(i) == null) {
        lastVisibleParameterIndex = i;
      }
    }
    if (lastVisibleParameterIndex != -1) {
      buffer.pushNewlineGroup(indent, 1);
      buffer.appendPossibleNewline();
    }

    List<StructMethodParametersAttribute.Entry> methodParameters = null;
    if (DecompilerContext.getOption(IFernflowerPreferences.USE_METHOD_PARAMETERS)) {
      StructMethodParametersAttribute attr = mt.getAttribute(StructGeneralAttribute.ATTRIBUTE_METHOD_PARAMETERS);
      if (attr != null) {
        methodParameters = attr.getEntries();
      }
    }

    int index = isEnum && init ? 3 : thisVar ? 1 : 0;
    int start = isEnum && init ? 2 : 0;
    boolean hasDescriptor = descriptor != null;
    //mask should now have the Outer.this in it... so this *shouldn't* be nessasary.
    //if (init && !isEnum && ((node.access & CodeConstants.ACC_STATIC) == 0) && node.type == ClassNode.CLASS_MEMBER)
    //    index++;

    buffer.pushNewlineGroup(indent, 0);
    for (int i = start; i < md.params.length; i++) {
      boolean real = mask == null || mask.get(i) == null;
      VarType parameterType = real && hasDescriptor && paramCount < descriptor.parameterTypes.size() ? descriptor.parameterTypes.get(paramCount) : md.params[i];
      if (real) {
        if (paramCount > 0) {
          buffer.append(",");
          buffer.appendPossibleNewline(" ");
        }

        Set<String> writtenAnnotations = appendParameterAnnotations(buffer, mt, paramCount);

        if (methodParameters != null && i < methodParameters.size()) {
          appendModifiers(buffer, methodParameters.get(i).myAccessFlags, CodeConstants.ACC_FINAL, isInterface, 0);
        }
        else if (methodWrapper.varproc.getVarFinal(new VarVersionPair(index, 0)) == VarTypeProcessor.FinalType.EXPLICIT_FINAL) {
          buffer.append("final ");
        }

        String typeName;
        boolean isVarArg = i == lastVisibleParameterIndex && mt.hasModifier(CodeConstants.ACC_VARARGS) && parameterType.arrayDim > 0;
        if (isVarArg) {
            parameterType = parameterType.decreaseArrayDim();
        }
        typeName = ExprProcessor.getCastTypeName(parameterType);

        if (ExprProcessor.UNDEFINED_TYPE_STRING.equals(typeName) &&
            DecompilerContext.getOption(IFernflowerPreferences.UNDEFINED_PARAM_TYPE_OBJECT)) {
          typeName = ExprProcessor.getCastTypeName(VarType.VARTYPE_OBJECT);
        }
        var annos = getTypeAnnotations(mt, TypeAnnotation.METHOD_PARAMETER, paramCount);
        if (!annos.isEmpty()) {
          VarType tempParam = parameterType;
          // Undo varargs change
          if (isVarArg) {
            tempParam = tempParam.resizeArrayDim(tempParam.arrayDim + 1);
          }
          // TODO: does this need typeName?
          buffer.appendCastTypeName(tempParam, annos, writtenAnnotations, isVarArg, true);
          isVarArg = false; // already handled
        } else {
          buffer.appendCastTypeName(typeName, parameterType);
        }

        if (isVarArg) {
          buffer.append("...");
        }

        buffer.append(' ');

        String parameterName;
        String clashingName = methodWrapper.varproc.getClashingName(new VarVersionPair(index, 0));
        if (clashingName != null) {
          parameterName = clashingName;
        } else if (methodParameters != null && i < methodParameters.size() && methodParameters.get(i).myName != null) {
          parameterName = methodParameters.get(i).myName;
        } else {
          parameterName = methodWrapper.varproc.getVarName(new VarVersionPair(index, 0));
        }

        String newParameterName = methodWrapper.methodStruct.getVariableNamer().renameParameter(flags, parameterType, parameterName, index);
        if ((flags & (CodeConstants.ACC_ABSTRACT | CodeConstants.ACC_NATIVE)) != 0 && Objects.equals(newParameterName, parameterName)) {
          newParameterName = DecompilerContext.getStructContext().renameAbstractParameter(methodWrapper.methodStruct.getClassQualifiedName(), mt.getName(), mt.getDescriptor(), index - (((flags & CodeConstants.ACC_STATIC) == 0) ? 1 : 0), parameterName);
        }
        parameterName = newParameterName;

        buffer.appendVariable(parameterName == null ? "param" + index : parameterName, // null iff decompiled with errors
          true, true, cl.qualifiedName, mt.getName(), md, index, parameterName);

        paramCount++;
      }

      index += parameterType.stackSize;
    }
    buffer.popNewlineGroup();

    if (lastVisibleParameterIndex != -1) {
      buffer.appendPossibleNewline("", true);
      buffer.popNewlineGroup();
    }
    buffer.append(')');
    return paramCount;
  }

  private static void dumpError(TextBuffer buffer, MethodWrapper wrapper, int indent) {
    List<String> lines = new ArrayList<>();
    lines.add("$VF: Couldn't be decompiled");
    boolean exceptions = DecompilerContext.getOption(IFernflowerPreferences.DUMP_EXCEPTION_ON_ERROR);
    boolean bytecode = DecompilerContext.getOption(IFernflowerPreferences.DUMP_BYTECODE_ON_ERROR);
    if (exceptions) {
      lines.addAll(ClassWriter.getErrorComment());
      collectErrorLines(wrapper.decompileError, lines);
      if (bytecode) {
        lines.add("");
      }
    }
    if (bytecode) {
      try {
        lines.add("Bytecode:");
        collectBytecode(wrapper, lines);
      } catch (Exception e) {
        lines.add("Error collecting bytecode:");
        collectErrorLines(e, lines);
      } finally {
        wrapper.methodStruct.releaseResources();
      }
    }
    for (String line : lines) {
      buffer.appendIndent(indent);
      buffer.append("//");
      if (!line.isEmpty()) buffer.append(' ').append(line);
      buffer.appendLineSeparator();
    }
  }

  public static void collectErrorLines(Throwable error, List<String> lines) {
    StackTraceElement[] stack = error.getStackTrace();
    List<StackTraceElement> filteredStack = new ArrayList<>();
    boolean hasSeenOwnClass = false;
    for (StackTraceElement e : stack) {
      String className = e.getClassName();
      boolean isOwnClass = className.startsWith("org.jetbrains.java.decompiler");
      if (isOwnClass) {
        hasSeenOwnClass = true;
      } else if (hasSeenOwnClass) {
        break;
      }
      filteredStack.add(e);
      if (isOwnClass) {
        String simpleName = className.substring(className.lastIndexOf('.') + 1);
        if (ERROR_DUMP_STOP_POINTS.contains(simpleName + "." + e.getMethodName())) {
          break;
        }
      }
    }
    if (filteredStack.isEmpty()) return;
    lines.add(error.toString());
    for (StackTraceElement e : filteredStack) {
      lines.add("  at " + e);
    }
    Throwable cause = error.getCause();
    if (cause != null) {
      List<String> causeLines = new ArrayList<>();
      collectErrorLines(cause, causeLines);
      if (!causeLines.isEmpty()) {
        lines.add("Caused by: " + causeLines.get(0));
        lines.addAll(causeLines.subList(1, causeLines.size()));
      }
    }
  }

  private static void collectBytecode(MethodWrapper wrapper, List<String> lines) throws IOException {
    ClassNode classNode = (ClassNode)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    StructMethod method = wrapper.methodStruct;
    FullInstructionSequence instructions = method.getInstructionSequence();
    if (instructions == null) {
      method.expandData(classNode.classStruct);
      instructions = method.getInstructionSequence();
    }
    int lastOffset = instructions.getLast().startOffset;
    int digits = 8 - Integer.numberOfLeadingZeros(lastOffset) / 4;
    ConstantPool pool = classNode.classStruct.getPool();
    StructBootstrapMethodsAttribute bootstrap = classNode.classStruct.getAttribute(StructGeneralAttribute.ATTRIBUTE_BOOTSTRAP_METHODS);

    for (var instr : instructions) {
      StringBuilder sb = new StringBuilder();
      String offHex = Integer.toHexString(instr.startOffset);
      for (int i = offHex.length(); i < digits; i++) sb.append('0');
      sb.append(offHex).append(": ");
      if (instr.wide) {
        sb.append("wide ");
      }
      sb.append(TextUtil.getInstructionName(instr.opcode));
      switch (instr.group) {
        case CodeConstants.GROUP_INVOCATION: {
          sb.append(' ');
          if (instr.opcode == CodeConstants.opc_invokedynamic && bootstrap != null) {
            appendBootstrapCall(sb, pool.getLinkConstant(instr.operand(0)), bootstrap);
          } else {
            appendConstant(sb, pool.getConstant(instr.operand(0)));
          }
          for (int i = 1; i < instr.operandsCount(); i++) {
            sb.append(' ').append(instr.operand(i));
          }
          break;
        }
        case CodeConstants.GROUP_FIELDACCESS: {
          sb.append(' ');
          appendConstant(sb, pool.getConstant(instr.operand(0)));
          break;
        }
        case CodeConstants.GROUP_JUMP: {
          sb.append(' ');
          int dest = instr.startOffset + instr.operand(0);
          String destHex = Integer.toHexString(dest);
          for (int i = destHex.length(); i < digits; i++) sb.append('0');
          sb.append(destHex);
          break;
        }
        default: {
          switch (instr.opcode) {
            case CodeConstants.opc_new:
            case CodeConstants.opc_checkcast:
            case CodeConstants.opc_instanceof:
            case CodeConstants.opc_ldc:
            case CodeConstants.opc_ldc_w:
            case CodeConstants.opc_ldc2_w: {
              sb.append(' ');
              PooledConstant constant = pool.getConstant(instr.operand(0));
              if (constant.type == CodeConstants.CONSTANT_Dynamic && bootstrap != null) {
                appendBootstrapCall(sb, (LinkConstant) constant, bootstrap);
              } else {
                appendConstant(sb, constant);
              }
              break;
            }
            default: {
              for (int i = 0; i < instr.operandsCount(); i++) {
                sb.append(' ').append(instr.operand(i));
              }
            }
          }
        }
      }
      lines.add(sb.toString());
    }

    for (ExceptionHandler handler : instructions.exceptionTable().getHandlers()) {
      lines.add("try (" + handler.from() + " -> " + handler.to() + "): " + handler.handler() + " " + handler.exceptionClass());
    }
  }

  private static void appendBootstrapCall(StringBuilder sb, LinkConstant target, StructBootstrapMethodsAttribute bootstrap) {
    sb.append(target.elementname).append(' ').append(target.descriptor);

    LinkConstant bsm = bootstrap.getMethodReference(target.index1);
    List<PooledConstant> bsmArgs = bootstrap.getMethodArguments(target.index1);

    sb.append(" bsm=");
    appendConstant(sb, bsm);
    sb.append(" args=[ ");
    boolean first = true;
    for (PooledConstant arg : bsmArgs) {
      if (!first) sb.append(", ");
      first = false;
      appendConstant(sb, arg);
    }
    sb.append(" ]");
  }

  private static void appendConstant(StringBuilder sb, PooledConstant constant) {
    if (constant == null) {
      sb.append("<null constant>");
      return;
    }
    if (constant instanceof PrimitiveConstant) {
      PrimitiveConstant prim = ((PrimitiveConstant) constant);
      Object value = prim.value;
      String stringValue = String.valueOf(value);
      if (prim.type == CodeConstants.CONSTANT_Class) {
        sb.append(stringValue);
      } else if (prim.type == CodeConstants.CONSTANT_String) {
        sb.append('"').append(ConstExprent.convertStringToJava(stringValue, false)).append('"');
      } else {
        sb.append(stringValue);
      }
    } else if (constant instanceof LinkConstant) {
      LinkConstant linkConstant = (LinkConstant) constant;
      sb.append(linkConstant.classname).append('.').append(linkConstant.elementname).append(' ').append(linkConstant.descriptor);
    }
  }

  private static boolean hideConstructor(ClassNode node, boolean init, boolean throwsExceptions, int paramCount, int methodAccessFlags, StructMethod structMethod) {
    if (!init || throwsExceptions || paramCount > 0 || !DecompilerContext.getOption(IFernflowerPreferences.HIDE_DEFAULT_CONSTRUCTOR)) {
      return false;
    }

    ClassWrapper wrapper = node.getWrapper();
    StructClass cl = wrapper.getClassStruct();

    int classAccessFlags = node.type == ClassNode.Type.ROOT ? cl.getAccessFlags() : node.access;
    boolean isEnum = cl.hasModifier(CodeConstants.ACC_ENUM) && DecompilerContext.getOption(IFernflowerPreferences.DECOMPILE_ENUM);
    boolean isRecord = cl.getRecordComponents() != null;

    // default constructor requires same accessibility flags. Exception: enum constructor which is always private
    // Another exception: record classes can sometimes be generated with a private constructor
    if(!isEnum && !isRecord && ((classAccessFlags & ACCESSIBILITY_FLAGS) != (methodAccessFlags & ACCESSIBILITY_FLAGS))) {
      return false;
    }

    // Constructor with an annotation, we dont want to hide this.
    if (RecordHelper.hasAnnotations(structMethod)) {
      return false;
    }

    // We should not run this check in records
    if (!isRecord) {
      int count = 0;
      for (StructMethod mt : cl.getMethods()) {
        if (CodeConstants.INIT_NAME.equals(mt.getName())) {
          if (++count > 1) {
            return false;
          }
        }
      }
    }

    // An explicit empty constructor is indistinguishable from a hidden default one except in the
    // line table: javac gives its implicit `return` an entry of its own, on the closing brace's
    // line. A default constructor's last entry always starts a field initializer.
    return !explicitEmptyConstructor(structMethod, wrapper);
  }

  /** Whether the constructor body opens with this(...) or super(...). */
  private static boolean startsWithDelegation(RootStatement root) {
    Statement first = root == null ? null : root.getFirst();
    if (!(first instanceof BasicBlockStatement) || first.getExprents() == null
        || first.getExprents().isEmpty()) {
      return false;
    }
    Exprent exprent = first.getExprents().get(0);
    return exprent instanceof InvocationExprent
      && ((InvocationExprent)exprent).getFunctype() == InvocationExprent.Type.INIT;
  }

  private static boolean explicitEmptyConstructor(StructMethod method, ClassWrapper wrapper) {
    StructLineNumberTableAttribute lines =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (lines == null) {
      return false;
    }
    int[] raw = lines.getRawData();
    if (raw.length < 4) {
      return false;
    }
    int lastPc = raw[raw.length - 2];
    int lastLine = raw[raw.length - 1];
    java.util.Set<Integer> fieldLines = new java.util.HashSet<>();
    for (Exprent initializer : wrapper.getDynamicFieldInitializers()) {
      if (initializer.bytecode == null) {
        continue;
      }
      for (int offset = initializer.bytecode.nextSetBit(0); offset >= 0;
           offset = initializer.bytecode.nextSetBit(offset + 1)) {
        if (offset == lastPc) {
          return false; // the last entry starts an initializer instruction
        }
      }
      // The declaration line is the line the initializer's text starts on, which is its
      // earliest instruction's: the stored expression's own bits can begin with a later link
      // of a chain.
      int first = -1;
      for (Exprent part : initializer.getAllExprents(true, true)) {
        if (part.bytecode == null || part.bytecode.isEmpty()) {
          continue;
        }
        int start = part.bytecode.nextSetBit(0);
        if (first < 0 || start < first) {
          first = start;
        }
      }
      int line = first < 0 ? -1 : lines.findLineNumber(first);
      if (line >= 0) {
        fieldLines.add(line);
      }
    }
    boolean explicit = !fieldLines.contains(lastLine);
    if (System.getenv("NEUROFLOWER_CTOR_DEBUG") != null) {
      System.err.println("ctor " + method.getClassQualifiedName() + method.getDescriptor()
        + " lastPc " + lastPc + " lastLine " + lastLine + " fieldLines " + fieldLines
        + " explicit " + explicit);
    }
    return explicit;
  }

  private static Map.Entry<VarType, GenericFieldDescriptor> getFieldTypeData(StructField fd) {
    VarType fieldType = new VarType(fd.getDescriptor(), false);

    GenericFieldDescriptor descriptor = fd.getSignature();
    return new AbstractMap.SimpleImmutableEntry<>(fieldType, descriptor);
  }

  private static boolean containsDeprecatedAnnotation(StructMember mb) {
    for (Key<?> key : ANNOTATION_ATTRIBUTES) {
      StructAnnotationAttribute attribute = mb.getAttribute((Key<StructAnnotationAttribute>) key);
      if (attribute != null) {
        for (AnnotationExprent annotation : attribute.getAnnotations()) {
          if (annotation.getClassName().equals("java/lang/Deprecated")) {
            return true;
          }
        }
      }
    }

    return false;
  }

  private static void appendDeprecation(TextBuffer buffer, int indent) {
    buffer.appendIndent(indent).append("/** @deprecated */").appendLineSeparator();
  }

  private enum MType {CLASS, FIELD, METHOD}

  private static void appendRenameComment(TextBuffer buffer, String oldName, MType type, int indent) {
    if (oldName == null) return;

    buffer.appendIndent(indent);
    buffer.append("// $VF: renamed from: ");

    switch (type) {
      case CLASS:
        buffer.append(ExprProcessor.buildJavaClassName(oldName));
        break;

      case FIELD:
        String[] fParts = oldName.split(" ");
        FieldDescriptor fd = FieldDescriptor.parseDescriptor(fParts[2]);
        buffer.append(fParts[1]);
        buffer.append(' ');
        buffer.append(getTypePrintOut(fd.type));
        break;

      default:
        String[] mParts = oldName.split(" ");
        MethodDescriptor md = MethodDescriptor.parseDescriptor(mParts[2]);
        buffer.append(mParts[1]);
        buffer.append(" (");
        boolean first = true;
        for (VarType paramType : md.params) {
          if (!first) {
            buffer.append(", ");
          }
          first = false;
          buffer.append(getTypePrintOut(paramType));
        }
        buffer.append(") ");
        buffer.append(getTypePrintOut(md.ret));
    }

    buffer.appendLineSeparator();
  }

  private static String getTypePrintOut(VarType type) {
    String typeText = ExprProcessor.getCastTypeName(type, false);
    if (ExprProcessor.UNDEFINED_TYPE_STRING.equals(typeText) &&
        DecompilerContext.getOption(IFernflowerPreferences.UNDEFINED_PARAM_TYPE_OBJECT)) {
      typeText = ExprProcessor.getCastTypeName(VarType.VARTYPE_OBJECT, false);
    }
    return typeText;
  }

  public static List<String> getErrorComment() {
    return Arrays.stream(((String) DecompilerContext.getProperty(IFernflowerPreferences.ERROR_MESSAGE)).split("\n")).filter(s -> !s.isEmpty()).collect(Collectors.toList());
  }

  private static void appendComment(TextBuffer buffer, String comment, int indent) {
    buffer.appendIndent(indent).append("// $VF: ").append(comment).appendLineSeparator();
  }

  private static void appendJavadoc(TextBuffer buffer, FabricJavadocStyle javadocStyle, String javaDoc, int indent) {
    if (javaDoc == null) return;
    switch (javadocStyle) {
      case HTML -> {
        buffer.appendIndent(indent).append("/**").appendLineSeparator();
        for (String s : javaDoc.split("\n")) {
          buffer.appendIndent(indent).append(" * ").append(s).appendLineSeparator();
        }
        buffer.appendIndent(indent).append(" */").appendLineSeparator();
      }
      case MARKDOWN -> {
        for (String s : javaDoc.split("\n")) {
          buffer.appendIndent(indent).append("/// ").append(s).appendLineSeparator();
        }
      }
    }
  }

  public static void appendSyntheticClassComment(StructClass cl, TextBuffer buffer) {
    String className = cl.qualifiedName.substring(cl.qualifiedName.lastIndexOf("/") + 1);
    buffer.append(" /* ").appendClass(className, true, cl.qualifiedName).append(" */");
  }

  public static final Key<?>[] ANNOTATION_ATTRIBUTES = {
    StructGeneralAttribute.ATTRIBUTE_RUNTIME_VISIBLE_ANNOTATIONS, StructGeneralAttribute.ATTRIBUTE_RUNTIME_INVISIBLE_ANNOTATIONS};
  public static final Key<?>[] PARAMETER_ANNOTATION_ATTRIBUTES = {
    StructGeneralAttribute.ATTRIBUTE_RUNTIME_VISIBLE_PARAMETER_ANNOTATIONS, StructGeneralAttribute.ATTRIBUTE_RUNTIME_INVISIBLE_PARAMETER_ANNOTATIONS};
  public static final Key<?>[] TYPE_ANNOTATION_ATTRIBUTES = {
    StructGeneralAttribute.ATTRIBUTE_RUNTIME_VISIBLE_TYPE_ANNOTATIONS, StructGeneralAttribute.ATTRIBUTE_RUNTIME_INVISIBLE_TYPE_ANNOTATIONS};

  static Set<String> appendAnnotations(TextBuffer buffer, int indent, StructMember mb, int targetType) {
    Set<String> filter = new HashSet<>();

    for (Key<?> key : ANNOTATION_ATTRIBUTES) {
      StructAnnotationAttribute attribute = mb.getAttribute((Key<StructAnnotationAttribute>)key);
      if (attribute != null) {
        for (AnnotationExprent annotation : attribute.getAnnotations()) {
          annotation.setDidWriteAlready(true);
          buffer.appendIndent(indent);
          filter.add(annotation.toJava(-1).convertToStringAndAllowDataDiscard());
          buffer.append(annotation.toJava(indent));
          if (indent < 0) {
            buffer.append(' ');
          }
          else {
            buffer.appendLineSeparator();
          }
        }
      }
    }

    // Implemented already
    if (targetType == TypeAnnotation.FIELD || targetType == TypeAnnotation.METHOD_RETURN_TYPE) {
      return filter;
    }
    // Fallback case... must be removed eventually
    appendTopLevelTypeAnnotations(buffer, indent, mb, targetType, -1, filter);

    return filter;
  }

  // Returns true if a method with the given name and descriptor matches in the inheritance tree of the superclass.
  private static boolean searchForMethod(StructClass cl, String name, MethodDescriptor md, boolean search) {
    // Didn't find the class or the library containing the class wasn't loaded, can't search
    if (cl == null) {
      return false;
    }

    VBStyleCollection<StructMethod, String> methods = cl.getMethods();

    if (search) {
      // If we're allowed to search, iterate through the methods and try to find matches
      for (StructMethod method : methods) {
        // Match against name, descriptor, and whether or not the found method is static.
        // TODO: We are not handling generics or superclass parameters and return types
        if (md.equals(MethodDescriptor.parseDescriptor(method.getDescriptor())) && name.equals(method.getName()) && !method.hasModifier(CodeConstants.ACC_STATIC)) {
          return true;
        }
      }
    }

    // If we have a superclass that's not Object, search that as well
    if (cl.superClass != null) {
      StructClass superClass = DecompilerContext.getStructContext().getClass((String)cl.superClass.value);

      boolean foundInSuperClass = searchForMethod(superClass, name, md, true);

      if (foundInSuperClass) {
        return true;
      }
    }

    // Search all of the interfaces implemented by this class for the method
    for (String ifaceName : cl.getInterfaceNames()) {
      StructClass iface = DecompilerContext.getStructContext().getClass(ifaceName);

      boolean foundInIface = searchForMethod(iface, name, md, true);

      if (foundInIface) {
        return true;
      }
    }

    // We didn't manage to find anything, return
    return false;
  }

  private static Set<String> appendParameterAnnotations(TextBuffer buffer, StructMethod mt, int param) {
    Set<String> filter = new HashSet<>();

    for (Key<?> key : PARAMETER_ANNOTATION_ATTRIBUTES) {
      StructAnnotationParameterAttribute attribute = mt.getAttribute((Key<StructAnnotationParameterAttribute>) key);
      if (attribute != null) {
        List<List<AnnotationExprent>> annotations = attribute.getParamAnnotations();
        if (param < annotations.size()) {
          for (AnnotationExprent annotation : annotations.get(param)) {
            filter.add(annotation.toJava(-1).convertToStringAndAllowDataDiscard());
            buffer.append(annotation.toJava(-1)).append(' ');
          }
        }
      }
    }

    return filter;
  }

  private static void appendTopLevelTypeAnnotations(TextBuffer buffer, int indent, StructMember mb, int targetType, int index, Set<String> filter) {
    for (Key<?> key : TYPE_ANNOTATION_ATTRIBUTES) {
      StructTypeAnnotationAttribute attribute = mb.getAttribute((Key<StructTypeAnnotationAttribute>) key);
      if (attribute != null) {
        for (TypeAnnotation annotation : attribute.getAnnotations()) {
          if (annotation.isTopLevel() && annotation.getTargetType() == targetType && (index < 0 || annotation.getIndex() == index)) {
            if (!filter.contains(annotation.getAnnotation().toJava(-1).convertToStringAndAllowDataDiscard())) {
              buffer.appendIndent(indent);
              buffer.append(annotation.getAnnotation().toJava(indent));
              if (indent < 0) {
                buffer.append(' ');
              }
              else {
                buffer.appendLineSeparator();
              }
            }
          }
        }
      }
    }
  }

  /**
   * Javac numbers lambdas class-wide in source order, but always emits {@code <clinit>} last in the
   * class file. Its source position is recoverable from the target lambda names: print the static
   * initializer before the first method whose lambdas are numbered after its own.
   */
  /** The original source line a method starts on, from its own line table. */
  /** Whether a member is a constructor or static block. */
  private static boolean isCtorMember(int[] member, VBStyleCollection<StructMethod, String> methods) {
    if (member[0] != 1) {
      return false;
    }
    String name = methods.get(member[1]).getName();
    return CodeConstants.INIT_NAME.equals(name) || CodeConstants.CLINIT_NAME.equals(name);
  }

  private static int methodLine(StructMethod method) {
    return lineAt(method, 0);
  }

  /** Whether an expression carries a lambda argument anywhere inside it. */
  /**
   * The line a block-printed lambda's closing brace sits on, or -1 when the body prints inline.
   * A block lambda records a line entry at its implicit return: that entry is the closing brace's
   * line, and an expression lambda's return has no entry of its own.
   */
  public static int blockLambdaClosingLine(MethodWrapper wrapper) {
    if (wrapper == null || wrapper.root == null) {
      return -1;
    }
    Statement firstStat = wrapper.root.getFirst();
    if (!(firstStat instanceof BasicBlockStatement) || firstStat.getExprents() == null
        || firstStat.getExprents().size() != 1) {
      return -1;
    }
    Exprent firstExpr = firstStat.getExprents().get(0);
    if (firstExpr instanceof AssignmentExprent assign && assign.getLeft() instanceof VarExprent left
        && left.isDefinition()
        || firstExpr instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.THROW) {
      return -1;
    }
    StructMethod struct = wrapper.methodStruct;
    var dummy = wrapper.root.getDummyExit();
    int retOffset = dummy == null || dummy.bytecode == null
      ? -1 : dummy.bytecode.previousSetBit(Integer.MAX_VALUE);
    int closingLine = retOffset < 0 ? -1 : RoundTrip.lineAt(struct, retOffset);
    boolean closingEntry = retOffset >= 0 && closingLine >= 0
      && closingLine != RoundTrip.lineAt(struct, retOffset - 1);
    int bodyLine = firstExpr.bytecode == null || firstExpr.bytecode.isEmpty()
      ? -1 : RoundTrip.lineAt(struct, firstExpr.bytecode.nextSetBit(0));
    int bodyEnd = firstExpr.bytecode == null || firstExpr.bytecode.isEmpty()
      ? -1 : RoundTrip.lineAt(struct, firstExpr.bytecode.previousSetBit(Integer.MAX_VALUE));
    return closingEntry && bodyLine >= 0 && closingLine > bodyLine && bodyEnd < closingLine
      ? closingLine : -1;
  }

  /**
   * A lambda compiled as an instance method whose body never reads {@code this} was written
   * against an instance member the class file does not record: a read of a final instance field
   * with a constant initializer leaves no instruction behind, because javac folds the constant
   * while the reference still makes the body instance. Print the field back where its value
   * stands, or the recompiled lambda is static and captures one value fewer than the target.
   */
  private static void restoreFoldedInstanceField(ClassNode node, MethodWrapper methodWrapper, RootStatement root) {
    if (node.lambdaInformation.is_content_method_static || node.parent == null
        || methodWrapper.varproc == null || !RoundTrip.selector("lambdathis")) {
      return;
    }
    if (usesThis(root)) {
      return;
    }
    ClassNode content = node.parent;
    for (ClassNode scope = content; scope != null; scope = scope.parent) {
      ClassWrapper scopeWrapper = scope.getWrapper();
      if (scopeWrapper == null || scope.classStruct == null) {
        continue;
      }
      for (StructField field : scope.classStruct.getFields()) {
        if (field.hasModifier(CodeConstants.ACC_STATIC) || !field.hasModifier(CodeConstants.ACC_FINAL)) {
          continue;
        }
        Exprent initializer = scopeWrapper.getDynamicFieldInitializers()
          .getWithKey(InterpreterUtil.makeUniqueKey(field.getName(), field.getDescriptor()));
        if (!(initializer instanceof ConstExprent constant) || constant.isNull()) {
          continue;
        }
        ConstExprent literal = findConstant(root, constant);
        if (literal == null) {
          continue;
        }
        if (shadowedFrom(content, scope, field.getName())) {
          continue;
        }
        Exprent qualifier = enclosingInstance(scope, methodWrapper);
        Exprent replacement = new FieldExprent(field.getName(), scope.classStruct.qualifiedName, false,
          qualifier, FieldDescriptor.parseDescriptor(field.getDescriptor()), literal.bytecode);
        if (replaceInStatement(root, literal, replacement)) {
          return;
        }
      }
    }
  }

  /** The expressions a statement owns directly: its blocks' and its own loop/if header's. */
  private static List<Exprent> ownedExprents(Statement stat) {
    List<Exprent> exprents = new ArrayList<>();
    if (stat instanceof BasicBlockStatement basic && basic.getExprents() != null) {
      exprents.addAll(basic.getExprents());
    }
    for (Exprent header : stat.getStatExprents()) {
      if (header != null) {
        exprents.add(header);
      }
    }
    return exprents;
  }

  /** True when the statement's own expressions read the method's {@code this}. */
  private static boolean usesThis(Statement stat) {
    for (Exprent exprent : ownedExprents(stat)) {
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof VarExprent var && var.getIndex() == 0 && !var.isStack()) {
          return true;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (usesThis(child)) {
        return true;
      }
    }
    return false;
  }

  /** The first literal in the statement equal to the reference, in print order. */
  private static ConstExprent findConstant(Statement stat, ConstExprent reference) {
    for (Exprent exprent : ownedExprents(stat)) {
      for (Exprent inner : exprent.getAllExprents(true, true)) {
        if (inner instanceof ConstExprent constant && constant.getValue() != null
            && !constant.isNull() && constant.getValue().equals(reference.getValue())) {
          return constant;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      ConstExprent found = findConstant(child, reference);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  private static boolean replaceInStatement(Statement stat, Exprent target, Exprent replacement) {
    if (stat instanceof BasicBlockStatement basic && basic.getExprents() != null) {
      List<Exprent> exprents = basic.getExprents();
      for (int i = 0; i < exprents.size(); i++) {
        Exprent exprent = exprents.get(i);
        if (exprent == target) {
          exprents.set(i, replacement);
          return true;
        }
        if (replaceInExprent(exprent, target, replacement)) {
          return true;
        }
      }
    }
    for (Exprent header : stat.getStatExprents()) {
      if (header == null) {
        continue;
      }
      if (header == target) {
        stat.replaceExprent(target, replacement);
        return true;
      }
      if (replaceInExprent(header, target, replacement)) {
        return true;
      }
    }
    for (Statement child : stat.getStats()) {
      if (replaceInStatement(child, target, replacement)) {
        return true;
      }
    }
    return false;
  }

  private static boolean replaceInExprent(Exprent parent, Exprent target, Exprent replacement) {
    for (Exprent child : parent.getAllExprents()) {
      if (child == target) {
        parent.replaceExprent(target, replacement);
        return true;
      }
      if (replaceInExprent(child, target, replacement)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The expression that qualifies a field of an enclosing class. It must print as nothing: an
   * unqualified {@code radius} is a simple name and therefore a constant expression javac folds,
   * where {@code Outer.this.radius} is a field access that compiles to a real read and forces a
   * {@code this$0} field the target does not have. The nameless-enclosure spelling is the same
   * form the tree already uses for an anonymous enclosing class.
   */
  private static Exprent enclosingInstance(ClassNode scope, MethodWrapper method) {
    int index = method.counter.getCounterAndIncrement(org.jetbrains.java.decompiler.main.collectors.CounterContainer.VAR_COUNTER);
    VarVersionPair pair = new VarVersionPair(index, 0);
    method.varproc.setVarName(pair, VarExprent.VAR_NAMELESS_ENCLOSURE);
    return new VarExprent(index, new VarType(CodeType.OBJECT, 0, scope.classStruct.qualifiedName), method.varproc);
  }

  /** True when an inner class between the content and the field's class declares that name. */
  private static boolean shadowedFrom(ClassNode content, ClassNode scope, String name) {
    for (ClassNode between = content; between != null && between != scope; between = between.parent) {
      for (StructField field : between.classStruct.getFields()) {
        if (field.getName().equals(name)) {
          return true;
        }
      }
    }
    return false;
  }

  public static boolean containsLambda(Exprent exprent) {
    if (exprent instanceof NewExprent created && created.isLambda()) {
      return true;
    }
    for (Exprent inner : exprent.getAllExprents(true)) {
      if (inner instanceof NewExprent created && created.isLambda()) {
        return true;
      }
    }
    return false;
  }

  private static int maxLine(StructLineNumberTableAttribute table) {
    int[] raw = table.getRawData();
    int max = -1;
    for (int i = 1; i < raw.length; i += 2) {
      max = Math.max(max, raw[i]);
    }
    return max;
  }

  private static int lineAt(StructMethod method, int offset) {
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    return table == null ? -1 : table.findLineNumber(offset);
  }

  /**
   * The line an enum's static block starts on, or -1. The compiler puts every enum constant's
   * construction at the head of {@code <clinit>}, so pc0 is the enum header, not the block; the
   * block is the first line table entry after the constants that still precedes the fields.
   */
  private static int staticBlockLine(ClassWrapper wrapper, StructClass cl) {
    if ((cl.getAccessFlags() & CodeConstants.ACC_ENUM) == 0) {
      return -1;
    }
    StructMethod clinit = cl.getMethod(CodeConstants.CLINIT_NAME, "()V");
    StructLineNumberTableAttribute table = clinit == null ? null
      : clinit.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return -1;
    }
    // The constants are constructed in declaration order, then the constant array is assembled
    // and attributed to the enum declaration line — the one step back in the table. The entry
    // after it is the first statement outside the header. It is a static block only when it
    // precedes every field initializer; a field line there would be an illegal forward move.
    int[] raw = table.getRawData();
    for (int i = 2; i + 3 < raw.length; i += 2) {
      if (raw[i + 1] < raw[i - 1]) {
        return raw[i + 3];
      }
    }
    return -1;
  }

  /**
   * The line a plain class's static block starts on: the first {@code <clinit>} line table entry
   * whose line is not one of the static field initializers' declaration lines. The initializers
   * are inlined at the head of {@code <clinit>}, each attributed to its own field's line; the
   * block's first statement is the first entry left over.
   */
  private static int staticBlockOwnLine(ClassWrapper wrapper, StructClass cl) {
    StructMethod clinit = cl.getMethod(CodeConstants.CLINIT_NAME, "()V");
    StructLineNumberTableAttribute table = clinit == null ? null
      : clinit.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return -1;
    }
    java.util.Set<Integer> fieldLines = new java.util.HashSet<>();
    for (StructField fd : cl.getFields()) {
      if (fd.hasModifier(CodeConstants.ACC_STATIC)) {
        int fieldLine = fieldLine(wrapper, cl, fd);
        if (fieldLine >= 0) {
          fieldLines.add(fieldLine);
        }
      }
    }
    int[] raw = table.getRawData();
    for (int i = 1; i < raw.length; i += 2) {
      if (!fieldLines.contains(raw[i])) {
        return raw[i];
      }
    }
    return -1;
  }

  /**
   * True when a static field initializer lifted out of the tail of {@code <clinit>} holds code
   * beyond everything the root still prints. The method's implicit return has no line table entry,
   * so the dummy exit anchor resolves to the floored line of the last entry - which is that lifted
   * initializer, printed far below the block's closing brace. Constraining the brace to it drags
   * the whole tail one line past its target; the brace's own line is not in the table and follows
   * the last printed statement when unanchored.
   */
  private static boolean endsWithLiftedInitializer(MethodWrapper method, ClassWrapper wrapper) {
    if (method == null || method.root == null) {
      return false;
    }
    java.util.BitSet remaining = new java.util.BitSet();
    method.root.getFirst().getOffset(remaining);
    int lastPrinted = remaining.length() - 1;
    for (Exprent initializer : wrapper.getStaticFieldInitializers()) {
      if (initializer.bytecode != null && initializer.bytecode.length() - 1 > lastPrinted) {
        return true;
      }
    }
    return false;
  }

  /**
   * The original source line a field is declared on. Only a lifted initializer knows it: the
   * initializer's offsets live in a constructor (or {@code <clinit>}), and in the constructor that
   * owns them every offset carries the field's line.
   */
  private static int fieldLine(ClassWrapper wrapper, StructClass cl, StructField fd) {
    String key = InterpreterUtil.makeUniqueKey(fd.getName(), fd.getDescriptor());
    boolean isStatic = fd.hasModifier(CodeConstants.ACC_STATIC);
    Exprent initializer = isStatic
      ? wrapper.getStaticFieldInitializers().getWithKey(key)
      : wrapper.getDynamicFieldInitializers().getWithKey(key);
    if (initializer == null || initializer.bytecode == null || initializer.bytecode.isEmpty()) {
      return -1;
    }
    if (isStatic) {
      StructMethod clinit = cl.getMethod(CodeConstants.CLINIT_NAME, "()V");
      if (clinit == null) {
        return -1;
      }
      int line = lineAt(clinit, initializer.bytecode.nextSetBit(0));
      // The initializer's offset set can carry offsets of an anonymous class's methods, which
      // land outside <clinit>'s own line range; such a line would drag every constructor with it.
      StructLineNumberTableAttribute table =
        clinit.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (line >= 0 && table != null && line > maxLine(table)) {
        return -1;
      }
      return line;
    }
    int found = -1;
    for (StructMethod method : cl.getMethods()) {
      if (!CodeConstants.INIT_NAME.equals(method.getName())) {
        continue;
      }
      int line = -1;
      boolean consistent = true;
      for (int offset = initializer.bytecode.nextSetBit(0); offset >= 0;
           offset = initializer.bytecode.nextSetBit(offset + 1)) {
        int candidate = lineAt(method, offset);
        if (candidate < 0) {
          continue;
        }
        if (line < 0) {
          line = candidate;
        } else if (line != candidate) {
          consistent = false;
          break;
        }
      }
      if (consistent && line >= 0) {
        if (found >= 0 && found != line) {
          return -1;
        }
        found = line;
      }
    }
    return found;
  }

  /** The first line any of a member class's methods starts on. */
  private static int classLine(ClassNode node) {
    int line = -1;
    for (StructMethod method : node.classStruct.getMethods()) {
      int candidate = methodLine(method);
      if (candidate >= 0 && (line < 0 || candidate < line)) {
        line = candidate;
      }
    }
    return line;
  }

  private static List<Integer> methodWriteOrder(ClassNode node, VBStyleCollection<StructMethod, String> methods) {
    List<Integer> order = new ArrayList<>(methods.size());
    for (int i = 0; i < methods.size(); i++) {
      order.add(i);
    }
    if (!RoundTrip.selector("memberorder")) {
      return order;
    }
    int clinit = -1;
    for (int i = 0; i < methods.size(); i++) {
      if (CodeConstants.CLINIT_NAME.equals(methods.get(i).getName())) {
        clinit = i;
      }
    }
    if (clinit < 0) {
      return order;
    }
    Map<Integer, Integer> minimum = new HashMap<>();
    int clinitMin = Integer.MAX_VALUE;
    for (ClassNode nested : node.nested) {
      ClassNode.LambdaInformation lambda = nested.lambdaInformation;
      if (lambda == null || lambda.is_method_reference || !node.classStruct.qualifiedName.equals(lambda.content_class_name)) {
        continue;
      }
      int index = lambdaIndex(lambda.content_method_name);
      if (index < 0) {
        continue;
      }
      String enclosing = lambda.content_method_name.substring("lambda$".length(), lambda.content_method_name.lastIndexOf('$'));
      int owner = -1;
      if ("static".equals(enclosing) || CodeConstants.CLINIT_NAME.equals(enclosing)) {
        owner = clinit;
      }
      for (int i = 0; owner < 0 && i < methods.size(); i++) {
        if (methods.get(i).getName().equals(enclosing)) {
          owner = i;
          break;
        }
      }
      if (owner < 0) {
        continue;
      }
      if (owner == clinit) {
        clinitMin = Math.min(clinitMin, index);
      } else {
        minimum.merge(owner, index, Math::min);
      }
    }
    if (clinitMin == Integer.MAX_VALUE) {
      return order;
    }
    int before = -1;
    for (int i = 0; i < methods.size(); i++) {
      Integer index = minimum.get(i);
      if (i != clinit && index != null && index > clinitMin) {
        before = i;
        break;
      }
    }
    if (before < 0) {
      return order;
    }
    order.remove(Integer.valueOf(clinit));
    order.add(order.indexOf(before), clinit);
    return order;
  }

  private static int lambdaIndex(String methodName) {
    int dollar = methodName.lastIndexOf('$');
    if (dollar < 0) {
      return -1;
    }
    try {
      return Integer.parseInt(methodName.substring(dollar + 1));
    } catch (NumberFormatException e) {
      return -1;
    }
  }

  public static List<Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> getTypeAnnotations(StructMember mb, int targetType, int index) {
    List<Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> list = new ArrayList<>();
    for (Key<?> key : TYPE_ANNOTATION_ATTRIBUTES) {
      StructTypeAnnotationAttribute attribute = mb.getAttribute((Key<StructTypeAnnotationAttribute>) key);
      if (attribute != null) {
        for (TypeAnnotation annotation : attribute.getAnnotations()) {
          if (annotation.getTargetType() == targetType && (index < 0 || annotation.getIndex() == index)) {
            Queue<TypeAnnotation.PathValue> q = annotation.asQueue();
            list.add(Pair.of(q, annotation.getAnnotation()));
          }
        }
      }
    }

    return list;
  }

  private static final Map<Integer, String> MODIFIERS;
  static {
    MODIFIERS = new LinkedHashMap<>();
    MODIFIERS.put(CodeConstants.ACC_PUBLIC, "public");
    MODIFIERS.put(CodeConstants.ACC_PROTECTED, "protected");
    MODIFIERS.put(CodeConstants.ACC_PRIVATE, "private");
    MODIFIERS.put(CodeConstants.ACC_ABSTRACT, "abstract");
    MODIFIERS.put(CodeConstants.ACC_STATIC, "static");
    MODIFIERS.put(CodeConstants.ACC_FINAL, "final");
    MODIFIERS.put(CodeConstants.ACC_STRICT, "strictfp");
    MODIFIERS.put(CodeConstants.ACC_TRANSIENT, "transient");
    MODIFIERS.put(CodeConstants.ACC_VOLATILE, "volatile");
    MODIFIERS.put(CodeConstants.ACC_SYNCHRONIZED, "synchronized");
    MODIFIERS.put(CodeConstants.ACC_NATIVE, "native");
  }

  private static final int CLASS_ALLOWED =
    CodeConstants.ACC_PUBLIC | CodeConstants.ACC_PROTECTED | CodeConstants.ACC_PRIVATE | CodeConstants.ACC_ABSTRACT |
    CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL | CodeConstants.ACC_STRICT;
  private static final int FIELD_ALLOWED =
    CodeConstants.ACC_PUBLIC | CodeConstants.ACC_PROTECTED | CodeConstants.ACC_PRIVATE | CodeConstants.ACC_STATIC |
    CodeConstants.ACC_FINAL | CodeConstants.ACC_TRANSIENT | CodeConstants.ACC_VOLATILE;
  private static final int METHOD_ALLOWED =
    CodeConstants.ACC_PUBLIC | CodeConstants.ACC_PROTECTED | CodeConstants.ACC_PRIVATE | CodeConstants.ACC_ABSTRACT |
    CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL | CodeConstants.ACC_SYNCHRONIZED | CodeConstants.ACC_NATIVE |
    CodeConstants.ACC_STRICT;

  private static final int CLASS_EXCLUDED = CodeConstants.ACC_ABSTRACT | CodeConstants.ACC_STATIC;
  private static final int FIELD_EXCLUDED = CodeConstants.ACC_PUBLIC | CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL;
  private static final int METHOD_EXCLUDED = CodeConstants.ACC_PUBLIC | CodeConstants.ACC_ABSTRACT;

  private static final int ACCESSIBILITY_FLAGS = CodeConstants.ACC_PUBLIC | CodeConstants.ACC_PROTECTED | CodeConstants.ACC_PRIVATE;

  private static void appendModifiers(TextBuffer buffer, int flags, int allowed, boolean isInterface, int excluded) {
    flags &= allowed;
    if (!isInterface) excluded = 0;
    for (int modifier : MODIFIERS.keySet()) {
      if ((flags & modifier) == modifier && (modifier & excluded) == 0) {
        buffer.append(MODIFIERS.get(modifier)).append(' ');
      }
    }
  }

  public static String getModifiers(int flags) {
    return MODIFIERS.entrySet().stream().filter(e -> (e.getKey() & flags) != 0).map(Map.Entry::getValue).collect(Collectors.joining(" "));
  }

  public static void appendTypeParameters(TextBuffer buffer, List<String> parameters, List<List<VarType>> bounds) {
    buffer.append('<');

    for (int i = 0; i < parameters.size(); i++) {
      if (i > 0) {
        buffer.append(", ");
      }

      buffer.append(parameters.get(i));

      List<VarType> parameterBounds = bounds.get(i);
      if (parameterBounds.size() > 1 || !"java/lang/Object".equals(parameterBounds.get(0).value)) {
        buffer.append(" extends ");
        buffer.appendCastTypeName(parameterBounds.get(0));
        for (int j = 1; j < parameterBounds.size(); j++) {
          buffer.append(" & ");
          buffer.appendCastTypeName(parameterBounds.get(j));
        }
      }
    }

    buffer.append('>');
  }

  private static void appendFQClassNames(TextBuffer buffer, List<String> names) {
    for (int i = 0; i < names.size(); i++) {
      String name = names.get(i);
      buffer.appendIndent(2).append(name);
      if (i < names.size() - 1) {
        buffer.append(',').appendLineSeparator();
      }
    }
  }
}

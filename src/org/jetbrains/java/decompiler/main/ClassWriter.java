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
            if (IfHelper.prettifyIfs(method.root)) {
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
                                int creationLine) {
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
          // reference to a static method
          buffer.appendCastTypeName(new VarType(node.lambdaInformation.content_class_name, true));
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

        boolean simpleLambda = false;
        boolean written = false;

        if (!lambdaToAnonymous) {
          RootStatement root = wrapper.getMethodWrapper(mt.getName(), mt.getDescriptor()).root;
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
                      if (sizeVar.getIndex() == (node.lambdaInformation.is_content_method_static ? 0 : 1)) {
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
                    TextBuffer codeBuffer = firstExpr.toJava(indent);

                    // The target's lambda body may start on a later line than the expression
                    // that creates the lambda; an expression lambda prints inline otherwise.
                    boolean breakBody = creationLine >= 0
                      && RoundTrip.methodLine(methodWrapper.methodStruct) > creationLine;

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
                buffer.append(" {}");
                simpleLambda = true;
              }
            }
          }
        }

        if ((!simpleLambda && !written) || lambdaToAnonymous) {
          buffer.append(" {").appendLineSeparator();

          methodLambdaToJava(node, wrapper, mt, buffer, indent + 1, !lambdaToAnonymous);

          buffer.appendIndent(indent).append("}");
        }
      }
    }
    finally {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, outerNode);
    }

    DecompilerContext.getLogger().endWriteClass();
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
      boolean ordered = DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_MEMBER_ORDER);
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
        // Members with no line of their own stay next to the neighbour that has one.
        int carried = -1;
        for (int[] member : plan) {
          if (member[2] < 0) {
            member[2] = carried;
          } else {
            carried = member[2];
          }
        }
        carried = Integer.MAX_VALUE;
        for (int i = plan.size() - 1; i >= 0; i--) {
          int[] member = plan.get(i);
          if (member[2] < 0) {
            member[2] = carried;
          } else {
            carried = member[2];
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
    // A static field's initializer, and every enum constant, lives in <clinit>; printing it needs
    // that method's line table for its argument and chain breaks. Fields are written outside any
    // method's context, where the previous method would otherwise supply the wrong lines.
    StructMethod outerStruct = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    StructMethod clinit = fd.hasModifier(CodeConstants.ACC_STATIC)
      ? wrapper.getClassStruct().getMethod(CodeConstants.CLINIT_NAME, "()V") : null;
    if (clinit != null) {
      DecompilerContext.setProperty(DecompilerContext.CURRENT_STRUCT_METHOD, clinit);
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
              TextBuffer code = root.toJava(indent + 1);
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
        int line = lines.findLineNumber(offset);
        if (line >= 0) {
          fieldLines.add(line);
        }
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
  private static int methodLine(StructMethod method) {
    return lineAt(method, 0);
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

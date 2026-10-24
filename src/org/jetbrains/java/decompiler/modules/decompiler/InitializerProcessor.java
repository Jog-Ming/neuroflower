// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.decompiler.CancelationManager;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statements;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLineNumberTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructMethodParametersAttribute;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;

import java.util.*;

public final class InitializerProcessor {
  public static void extractInitializers(ClassWrapper wrapper) {
    MethodWrapper method = wrapper.getMethodWrapper(CodeConstants.CLINIT_NAME, "()V");
    try {
      if (method != null && method.root != null) {  // successfully decompiled static constructor
        extractStaticInitializers(wrapper, method);
      }
    } catch (CancelationManager.CanceledException e) {
      throw e;
    } catch (Throwable t) {
      StructMethod mt = method.methodStruct;
      String message = "Method " + mt.getName() + " " + mt.getDescriptor() + " in class " + wrapper.getClassStruct().qualifiedName + " couldn't be written.";
      DecompilerContext.getLogger().writeMessage(message, IFernflowerLogger.Severity.WARN, t);

      method.decompileError = t;
    }

    extractDynamicInitializers(wrapper);

    // required e.g. if anonymous class is being decompiled as a standard one.
    // This can happen if InnerClasses attributes are erased
    liftConstructor(wrapper);

    if (DecompilerContext.getOption(IFernflowerPreferences.HIDE_EMPTY_SUPER)) {
      hideEmptySuper(wrapper);
    }
  }

  private static void liftConstructor(ClassWrapper wrapper) {
    for (MethodWrapper method : wrapper.getMethods()) {
      if (CodeConstants.INIT_NAME.equals(method.methodStruct.getName()) && method.root != null) {
        Statement firstData = Statements.findFirstData(method.root);
        if (firstData == null) {
          return;
        }

        int index = 0;
        List<Exprent> lstExprents = firstData.getExprents();

        for (Exprent exprent : lstExprents) {
          int action = 0;

          if (exprent instanceof AssignmentExprent) {
            AssignmentExprent assignExpr = (AssignmentExprent)exprent;
            if (assignExpr.getLeft() instanceof FieldExprent && assignExpr.getRight() instanceof VarExprent) {
              FieldExprent fExpr = (FieldExprent)assignExpr.getLeft();
              if (fExpr.getClassname().equals(wrapper.getClassStruct().qualifiedName)) {
                StructField structField = wrapper.getClassStruct().getField(fExpr.getName(), fExpr.getDescriptor().descriptorString);
                if (structField != null && structField.hasModifier(CodeConstants.ACC_FINAL)) {
                  action = 1;
                }
              }
            }
          }
          else if (index > 0 && exprent instanceof InvocationExprent &&
                   Statements.isInvocationInitConstructor((InvocationExprent)exprent, method, wrapper, true)) {
            // this() or super()
            lstExprents.add(0, lstExprents.remove(index));
            action = 2;
          }

          if (action != 1) {
            break;
          }

          index++;
        }
      }
    }
  }

  private static void hideEmptySuper(ClassWrapper wrapper) {
    for (MethodWrapper method : wrapper.getMethods()) {
      if (CodeConstants.INIT_NAME.equals(method.methodStruct.getName()) && method.root != null) {
        Statement firstData = method.root.getBasichead();
        if (firstData == null || firstData.getExprents().isEmpty()) {
          return;
        }

        Exprent exprent = firstData.getExprents().get(0);
        if (exprent instanceof InvocationExprent) {
          InvocationExprent invExpr = (InvocationExprent)exprent;
          if (Statements.isInvocationInitConstructor(invExpr, method, wrapper, false)) {
            List<VarVersionPair> mask = ExprUtil.getSyntheticParametersMask(invExpr.getClassname(), invExpr.getStringDescriptor(), invExpr.getLstParameters().size());
            boolean hideSuper = true;

            //searching for non-synthetic params
            for (int i = 0; i < invExpr.getDescriptor().params.length; ++i) {
              if (mask != null && mask.get(i) != null) {
                continue;
              }
              VarType type = invExpr.getDescriptor().params[i];
              if (type.type == CodeType.OBJECT) {
                ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(type.value);
                if (node != null && (node.type == ClassNode.Type.ANONYMOUS || (node.access & CodeConstants.ACC_SYNTHETIC) != 0)) {
                  break; // Should be last
                }
              }
              hideSuper = false; // found non-synthetic param so we keep the call
              break;
            }

            if (hideSuper) {
              firstData.getExprents().remove(0);
            }
          }
        }
      }
    }
  }

  public static void hideInitalizers(ClassWrapper wrapper) {
    // hide initializers with anon class arguments
    for (MethodWrapper method : wrapper.getMethods()) {
      StructMethod mt = method.methodStruct;
      String name = mt.getName();
      String desc = mt.getDescriptor();

      if (mt.isSynthetic() && CodeConstants.INIT_NAME.equals(name)) {
        MethodDescriptor md = MethodDescriptor.parseDescriptor(desc);
        if (md.params.length > 0) {
          VarType type = md.params[md.params.length - 1];
          if (type.type == CodeType.OBJECT) {
            ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(type.value);
            if (node != null && ((node.type == ClassNode.Type.ANONYMOUS) || (node.access & CodeConstants.ACC_SYNTHETIC) != 0)) {
              //TODO: Verify that the body is JUST a this([args]) call?
              wrapper.getHiddenMembers().add(InterpreterUtil.makeUniqueKey(name, desc));
            }
          }
        }
      }
    }
  }

  private static void extractStaticInitializers(ClassWrapper wrapper, MethodWrapper method) {
    RootStatement root = method.root;
    StructClass cl = wrapper.getClassStruct();
    Set<String> whitelist = new HashSet<String>();

    Statement firstData = Statements.findFirstData(root);
    if (firstData != null) {
      boolean inlineInitializers = cl.hasModifier(CodeConstants.ACC_INTERFACE) || cl.hasModifier(CodeConstants.ACC_ENUM);
      List<AssignmentExprent> exprentsToRemove = new LinkedList<>();//when we loop back through the list, stores ones we need to remove outside iterator loop
      Map<Integer, AssignmentExprent> nonFieldAssigns = new HashMap<>();

      // Store fields that have been assigned to more than once. These aren't safe to inline.
      List<String> seen = new ArrayList<>();
      List<String> multiAssign = new ArrayList<>();

      for (Exprent exprent : firstData.getExprents()) {
        if (exprent instanceof AssignmentExprent) {
          AssignmentExprent assignExpr = (AssignmentExprent) exprent;
          if (assignExpr.getLeft() instanceof FieldExprent) {
            FieldExprent fExpr = (FieldExprent) assignExpr.getLeft();

            // If the field has been seen already, add it to the list of multi-assigned fields
            String name = fExpr.getName();
            if (seen.contains(name)) {
              if (!multiAssign.contains(name)) {
                // If this hasn't been seen, add to list of multi assigned variables
                multiAssign.add(name);
              }
            } else {
              // If it hasn't been seen, store it for later to check
              seen.add(name);
            }
          }
        }
      }

      List<FieldExprent> notInlined = new ArrayList<>();

      Iterator<Exprent> itr = firstData.getExprents().iterator();
      while (itr.hasNext()) {
        Exprent exprent = itr.next();

        if (exprent instanceof AssignmentExprent) {
          AssignmentExprent assignExpr = (AssignmentExprent)exprent;
          if (assignExpr.getLeft() instanceof FieldExprent) {
            FieldExprent fExpr = (FieldExprent)assignExpr.getLeft();
            if (fExpr.isStatic() && fExpr.getClassname().equals(cl.qualifiedName) &&
                cl.hasField(fExpr.getName(), fExpr.getDescriptor().descriptorString)) {

              // interfaces fields should always be initialized inline
              String keyField = InterpreterUtil.makeUniqueKey(fExpr.getName(), fExpr.getDescriptor().descriptorString);
              boolean exprentIndependent = isExprentIndependent(fExpr, assignExpr.getRight(), method, cl, whitelist, multiAssign, notInlined, cl.getFields().getIndexByKey(keyField), true);
              if (inlineInitializers || exprentIndependent) {
                if (!wrapper.getStaticFieldInitializers().containsKey(keyField)) {
                  if (exprentIndependent) {
                    wrapper.getStaticFieldInitializers().addWithKey(assignExpr.getRight(), keyField);
                    whitelist.add(keyField);
                    itr.remove();
                  } else { //inlineInitializers
                    if (assignExpr.getRight() instanceof NewExprent){
                      NewExprent newExprent = (NewExprent) assignExpr.getRight();
                      if (newExprent.getConstructor() == null) {
                        continue;
                      }

                      Exprent instance = newExprent.getConstructor().getInstance();
                      if (instance instanceof VarExprent && nonFieldAssigns.containsKey(((VarExprent) instance).getIndex())){
                        AssignmentExprent nonFieldAssignment = nonFieldAssigns.remove(((VarExprent) instance).getIndex());
                        newExprent.getConstructor().setInstance(nonFieldAssignment.getRight());
                        exprentsToRemove.add(nonFieldAssignment);
                        wrapper.getStaticFieldInitializers().addWithKey(assignExpr.getRight(), keyField);
                        whitelist.add(keyField);
                        itr.remove();
                      } else {
//                        DecompilerContext.getLogger().writeMessage("Don't know how to handle non independent "+assignExpr.getRight().getClass().getName(), IFernflowerLogger.Severity.ERROR);
                      }
                    } else {
//                      DecompilerContext.getLogger().writeMessage("Don't know how to handle non independent "+assignExpr.getRight().getClass().getName(), IFernflowerLogger.Severity.ERROR);
                    }
                  }
                }
              } else {
                notInlined.add(fExpr);
              }
            }
          } else if (inlineInitializers) {
//            DecompilerContext.getLogger().writeMessage("Found non field assignment when needing to force inline: "+assignExpr.toString(), IFernflowerLogger.Severity.TRACE);
            if (assignExpr.getLeft() instanceof VarExprent) {
              nonFieldAssigns.put(((VarExprent) assignExpr.getLeft()).getIndex(), assignExpr);
            } else {
//              DecompilerContext.getLogger().writeMessage("Left is not VarExprent!", IFernflowerLogger.Severity.ERROR);
            }
          }
        } else if (inlineInitializers && cl.hasModifier(CodeConstants.ACC_INTERFACE)) {
//          DecompilerContext.getLogger().writeMessage("Non assignment found in initializer when we're needing to inline all", IFernflowerLogger.Severity.ERROR);
        }
      }
      if (exprentsToRemove.size() > 0){
        firstData.getExprents().removeAll(exprentsToRemove);
      }
    }

    liftAssignmentsAfterStaticBlocks(wrapper, method, cl, firstData, whitelist);

    // Ensure enum fields have been inlined
    if (cl.hasModifier(CodeConstants.ACC_ENUM)) {
      for (StructField fd : cl.getFields()) {
        if (fd.hasModifier(CodeConstants.ACC_ENUM)) {
          if (wrapper.getStaticFieldInitializers().getWithKey(InterpreterUtil.makeUniqueKey(fd.getName(), fd.getDescriptor())) == null) {
            method.addComment("$VF: Failed to inline enum fields");
            method.addErrorComment = true;
            break;
          }
        }
      }
    }
  }

  /**
   * javac gives a static block's local variables a scope that ends at the block's closing brace,
   * not at the last use. An assignment to a static field of this class that trails {@code <clinit>}
   * and whose store lies at or after that end was therefore written outside the block, as the
   * field's initializer: the block closed before it. Lifting it reproduces the original - the
   * regenerated static block ends at the same offset, and the field prints on its own line after
   * it. Only the LVT length carries that evidence, and attribute scoring ignores it.
   *
   * <p>Only the tail of the straight-line path is lifted. The whole method prints as one static
   * block at its first line, so an initializer between two blocks would be printed after both,
   * reordering the code; a trailing run keeps the printed order.
   */
  private static void liftAssignmentsAfterStaticBlocks(ClassWrapper wrapper, MethodWrapper method,
                                                       StructClass cl, Statement firstData,
                                                       Set<String> whitelist) {
    StructLocalVariableTableAttribute scope = method.methodStruct.getLocalVariableAttr();
    StructLineNumberTableAttribute lines =
      method.methodStruct.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (scope == null || lines == null) {
      return;
    }
    int scopeEnd = -1;
    for (Iterator<StructLocalVariableTableAttribute.LocalVariable> vars = scope.getVariables().iterator(); vars.hasNext(); ) {
      scopeEnd = Math.max(scopeEnd, vars.next().getEnd());
    }
    if (scopeEnd <= 0) {
      return;
    }

    // Fields assigned more than once on the straight-line path are not safe to inline.
    List<String> seen = new ArrayList<>();
    List<String> multiAssign = new ArrayList<>();
    for (Statement stat : straightLineBlocks(method.root.getFirst())) {
      for (Exprent exprent : stat.getExprents()) {
        if (exprent instanceof AssignmentExprent && ((AssignmentExprent)exprent).getLeft() instanceof FieldExprent) {
          String name = ((FieldExprent)((AssignmentExprent)exprent).getLeft()).getName();
          if (seen.contains(name)) {
            if (!multiAssign.contains(name)) {
              multiAssign.add(name);
            }
          } else {
            seen.add(name);
          }
        }
      }
    }

    Statement tail = lastStraightLineBlock(method.root.getFirst());
    if (tail == null || tail == firstData || tail.getExprents().isEmpty()) {
      return;
    }
    int blockLine = lines.findLineNumber(0);
    List<FieldExprent> notInlined = new ArrayList<>();
    List<Exprent> exprents = tail.getExprents();
    int first = exprents.size();
    // Walk back over the trailing run; the first exprent that does not qualify ends it.
    while (first > 0) {
      Exprent exprent = exprents.get(first - 1);
      if (!(exprent instanceof AssignmentExprent) || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
        break;
      }
      int offset = exprent.bytecode.nextSetBit(0);
      if (offset < scopeEnd || lines.findLineNumber(offset) <= blockLine) {
        break;
      }
      AssignmentExprent assignExpr = (AssignmentExprent)exprent;
      if (!(assignExpr.getLeft() instanceof FieldExprent)) {
        break;
      }
      FieldExprent fExpr = (FieldExprent)assignExpr.getLeft();
      if (!fExpr.isStatic() || !fExpr.getClassname().equals(cl.qualifiedName) ||
          !cl.hasField(fExpr.getName(), fExpr.getDescriptor().descriptorString)) {
        break;
      }
      String keyField = InterpreterUtil.makeUniqueKey(fExpr.getName(), fExpr.getDescriptor().descriptorString);
      if (wrapper.getStaticFieldInitializers().containsKey(keyField)) {
        break;
      }
      if (!isExprentIndependent(fExpr, assignExpr.getRight(), method, cl, whitelist, multiAssign,
                                notInlined, cl.getFields().getIndexByKey(keyField), true)) {
        break;
      }
      wrapper.getStaticFieldInitializers().addWithKey(assignExpr.getRight(), keyField);
      whitelist.add(keyField);
      first--;
    }
    if (first < exprents.size()) {
      exprents.subList(first, exprents.size()).clear();
    }
  }

  /** Every basic block that executes unconditionally, in generation order. */
  private static List<Statement> straightLineBlocks(Statement stat) {
    List<Statement> out = new ArrayList<>();
    collectStraightLineBlocks(stat, out);
    return out;
  }

  private static void collectStraightLineBlocks(Statement stat, List<Statement> out) {
    if (stat.type == Statement.StatementType.SEQUENCE) {
      for (Statement child : stat.getStats()) {
        collectStraightLineBlocks(child, out);
      }
    } else if (stat.type == Statement.StatementType.BASIC_BLOCK && stat.getExprents() != null) {
      out.add(stat);
    }
  }

  /**
   * The basic block that ends {@code <clinit>}, or null when the last statement is not a plain
   * block (then lifting would move its code past a later control structure).
   */
  private static Statement lastStraightLineBlock(Statement stat) {
    while (stat.type == Statement.StatementType.SEQUENCE) {
      if (stat.getStats().isEmpty()) {
        return null;
      }
      stat = stat.getStats().get(stat.getStats().size() - 1);
    }
    return stat.type == Statement.StatementType.BASIC_BLOCK && stat.getExprents() != null ? stat : null;
  }

  private static void extractDynamicInitializers(ClassWrapper wrapper) {
    StructClass cl = wrapper.getClassStruct();

    boolean isAnonymous = DecompilerContext.getClassProcessor().getMapRootClasses().get(cl.qualifiedName).type == ClassNode.Type.ANONYMOUS;

    List<List<Exprent>> lstFirst = new ArrayList<>();
    List<MethodWrapper> lstMethodWrappers = new ArrayList<>();

    for (MethodWrapper method : wrapper.getMethods()) {
      if (CodeConstants.INIT_NAME.equals(method.methodStruct.getName()) && method.root != null) { // successfully decompiled constructor
        Statement firstData = Statements.findFirstData(method.root);
        if (firstData == null || firstData.getExprents().isEmpty()) {
          continue;
        }

        Exprent exprent = firstData.getExprents().get(0);
        if (!isAnonymous) { // FIXME: doesn't make sense
          if (!(exprent instanceof InvocationExprent) ||
              !Statements.isInvocationInitConstructor((InvocationExprent)exprent, method, wrapper, false)) {
            continue;
          }
        }
        lstFirst.add(firstData.getExprents());
        lstMethodWrappers.add(method);
      }
    }

    if (lstFirst.isEmpty()) {
      return;
    }

    // The value stored below is the first constructor's own expression, so its bytecode offsets
    // are offsets into that constructor. The printer must read the target's lines for them from
    // the same method: no other table describes where the initializer's text sat.
    wrapper.setDynamicInitializerOwner(lstMethodWrappers.get(0).methodStruct);

    Set<String> whitelist = new HashSet<String>(wrapper.getStaticFieldInitializers().getLstKeys());
    int prev_fidx = 0;

    while (true) {
      String fieldWithDescr = null;
      Exprent value = null;

      for (int i = 0; i < lstFirst.size(); i++) {
        List<Exprent> lst = lstFirst.get(i);

        if (lst.size() < (isAnonymous ? 1 : 2)) {
          return;
        }

        Exprent exprent = lst.get(isAnonymous ? 0 : 1);

        boolean found = false;

        if (exprent instanceof AssignmentExprent) {
          AssignmentExprent assignExpr = (AssignmentExprent)exprent;
          if (assignExpr.getLeft() instanceof FieldExprent) {
            FieldExprent fExpr = (FieldExprent)assignExpr.getLeft();
            if (!fExpr.isStatic() && fExpr.getClassname().equals(cl.qualifiedName) &&
                cl.hasField(fExpr.getName(), fExpr.getDescriptor().descriptorString)) { // check for the physical existence of the field. Could be defined in a superclass.

              String fieldKey = InterpreterUtil.makeUniqueKey(fExpr.getName(), fExpr.getDescriptor().descriptorString);
              int fidx = cl.getFields().getIndexByKey(fieldKey);
              if (prev_fidx <= fidx && isExprentIndependent(fExpr, assignExpr.getRight(), lstMethodWrappers.get(i), cl, whitelist, new ArrayList<>() /* TODO */, new ArrayList<>(),  fidx, false)
                && declaredBeforeConstructor(cl, lstMethodWrappers.get(i).methodStruct, exprent, isAnonymous)) {
                prev_fidx = fidx;
                if (fieldWithDescr == null) {
                  fieldWithDescr = fieldKey;
                  value = assignExpr.getRight();
                }
                else {
                  if (!fieldWithDescr.equals(fieldKey) ||
                      !value.equals(assignExpr.getRight())) {
                    return;
                  }
                }
                found = true;
              }
            }
          }
        }

        if (!found) {
          return;
        }
      }

      if (!wrapper.getDynamicFieldInitializers().containsKey(fieldWithDescr)) {
        // Some very last minute things to catch bugs with initializing and inlining
        value = processDynamicInitializer(value);
        wrapper.getDynamicFieldInitializers().addWithKey(value, fieldWithDescr);
        whitelist.add(fieldWithDescr);

        for (List<Exprent> lst : lstFirst) {
          lst.remove(isAnonymous ? 0 : 1);
        }
      }
      else {
        return;
      }
    }
  }

  /**
   * A field initializer's recorded line is its declaration, which can sit anywhere in the class;
   * a constructor statement's line always lies between the declaration's line and the closing
   * brace the return instruction carries. Only a line outside that span proves the code was
   * lifted out of the constructor; inside it, the source wrote the assignment in the body and
   * lifting it would print the code after the constructor.
   * <p>
   * A constructor the source did not write has no span of its own: javac names the class
   * declaration (or the first enum constant) at offset 0, and every true initializer's line is
   * necessarily greater. Such a constructor is recognized by its parameters, all synthetic or
   * mandated: only a written declaration lists a name without either flag. A default no-arg
   * constructor has no parameter attribute at all and is treated the same way. An anonymous
   * class cannot declare one at all, and its synthetic constructor forwards the superclass's
   * parameters, so it is never treated as written.
   */
  private static boolean declaredBeforeConstructor(StructClass cl, StructMethod method, Exprent exprent, boolean isAnonymous) {
    if (isAnonymous || !writtenConstructor(method, cl)) {
      return true;
    }
    if (exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return true;
    }
    int line = RoundTrip.lineAt(method, exprent.bytecode.nextSetBit(0));
    int ctorStart = RoundTrip.lineAt(method, 0);
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    int[] raw = table == null ? null : table.getRawData();
    int ctorEnd = raw == null || raw.length < 2 ? -1 : raw[raw.length - 1];
    return line < 0 || ctorStart < 0 || ctorEnd < 0 || line < ctorStart || line > ctorEnd;
  }

  private static boolean writtenConstructor(StructMethod method, StructClass cl) {
    StructMethodParametersAttribute parameters =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_METHOD_PARAMETERS);
    if (parameters != null) {
      for (StructMethodParametersAttribute.Entry entry : parameters.getEntries()) {
        if ((entry.myAccessFlags & (CodeConstants.ACC_SYNTHETIC | CodeConstants.ACC_MANDATED)) == 0) {
          return true;
        }
      }
    }
    // A no-arg constructor lists no parameters either way. One the source wrote ends at a
    // closing brace that javac records as a position of its own, so the return instruction
    // starts a line entry; the synthesized one ends on its last initializer's line with none.
    // The expansion says elsewhere whether a method's body has been processed, so it is
    // released again and the state is left as it was found.
    boolean expanded = method.getInstructionSequence() != null;
    try {
      if (!expanded) {
        method.expandData(cl);
      }
      FullInstructionSequence code = method.getInstructionSequence();
      StructLineNumberTableAttribute table =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (code == null || table == null) {
        return false;
      }
      int last = -1;
      for (Instruction instruction : code) {
        last = instruction.startOffset;
      }
      int[] raw = table.getRawData();
      for (int i = 0; i + 1 < raw.length; i += 2) {
        if (raw[i] == last) {
          return true;
        }
      }
      return false;
    }
    catch (Exception e) {
      return false;
    }
    finally {
      if (!expanded) {
        method.releaseResources();
      }
    }
  }

  private static Exprent processDynamicInitializer(Exprent expr) {

    if (expr instanceof FunctionExprent) {
      Exprent temp = expr;
      // Find function inside casts
      while (temp instanceof FunctionExprent && (((FunctionExprent) temp).getFuncType().castType != null || ((FunctionExprent) temp).getFuncType() == FunctionType.CAST)) {
        temp = ((FunctionExprent) temp).getLstOperands().get(0);
      }

      if (temp instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent) temp;

        // Force unwrap boxing in function
        func.unwrapBox();

        expr = func;
      }
    } else {
      // boolean b = obj; -> boolean b = (Boolean)obj;
      expr = processBoxingCast(expr);
    }

    return expr;
  }

  private static Exprent processBoxingCast(Exprent expr) {
    if (expr instanceof InvocationExprent) {
      if (((InvocationExprent) expr).isUnboxingCall()) {
        Exprent inner = ((InvocationExprent) expr).getInstance();
        if (inner instanceof FunctionExprent && ((FunctionExprent)inner).getFuncType() == FunctionType.CAST) {
          inner.addBytecodeOffsets(expr.bytecode);
          expr = inner;
        }
      }
    }

    return expr;
  }

  private static boolean isExprentIndependent(FieldExprent field, Exprent exprent, MethodWrapper method, StructClass cl, Set<String> whitelist, List<String> multiAssign, List<FieldExprent> notInlined, int fidx, boolean isStatic) {
    String keyField = InterpreterUtil.makeUniqueKey(field.getName(), field.getDescriptor().descriptorString);
    List<Exprent> lst = exprent.getAllExprents(true, true);

    for (Exprent expr : lst) {
      switch (expr.type) {
        case VAR:
          VarVersionPair varPair = new VarVersionPair((VarExprent)expr);
          if (!method.varproc.getExternalVars().contains(varPair)) {
            String varName = method.varproc.getVarName(varPair);
            if (varName == null || !varName.equals("this") && !varName.endsWith(".this")) { // FIXME: remove direct comparison with strings
              return false;
            }
          }
          break;
        case FIELD:
          FieldExprent fexpr = (FieldExprent)expr;
          if (notInlined.contains(fexpr)) {
            return false;
          }

          if (cl.hasField(fexpr.getName(), fexpr.getDescriptor().descriptorString)) {
            String key = InterpreterUtil.makeUniqueKey(fexpr.getName(), fexpr.getDescriptor().descriptorString);
            if (isStatic) {
              // If this field has been assigned to more than once, we can't assume it's safe to inline
              if (multiAssign.contains(fexpr.getName())) {
                return false;
              }

              if (!fexpr.isStatic()) {
                return false;
              } else if (cl.getFields().getIndexByKey(key) >= fidx) {
                fexpr.forceQualified(true);
              }
            } else {
              if (!whitelist.contains(key)) {
                return false;
              } else if (cl.getFields().getIndexByKey(key) > fidx) {
                return false;
              }
            }
          }
          else if (!fexpr.isStatic() && fexpr.getInstance() == null) {
            return false;
          }
          break;
        case NEW:
          qualifyFieldReferences((NewExprent)expr, cl, fidx);
          break;
      }
    }

    return true;
  }

  // Qualifies field references to future static fields in lambdas
  private static void qualifyFieldReferences(NewExprent nexpr, StructClass cl, int fidx) {
    boolean isStatic = cl.getFields().get(fidx).hasModifier(CodeConstants.ACC_STATIC);
    if (isStatic && nexpr.isLambda() && !nexpr.isMethodReference()) {
      ClassNode child = DecompilerContext.getClassProcessor().getMapRootClasses().get(nexpr.getNewType().value);
      MethodWrapper wrapper = child.parent.getWrapper().getMethods().getWithKey(child.lambdaInformation.content_method_key);

      Set<Exprent> s = new HashSet<>();
      wrapper.getOrBuildGraph().iterateExprentsDeep(e -> {
        if (e instanceof FieldExprent || e instanceof NewExprent)
          s.add(e);
        return 0;
      });
      for (Exprent e : s) {
        switch (e.type) {
          case FIELD:
            FieldExprent fe = (FieldExprent)e;
            if (cl.qualifiedName.equals(fe.getClassname()) && fe.isStatic() && cl.hasField(fe.getName(), fe.getDescriptor().descriptorString)) {
              String key = InterpreterUtil.makeUniqueKey(fe.getName(), fe.getDescriptor().descriptorString);
              if (fe.getInstance() == null && cl.getFields().getIndexByKey(key) > fidx) {
                fe.forceQualified(true);
              }
            }
            break;
          case NEW:
            qualifyFieldReferences((NewExprent)e, cl, fidx);
            break;
        }
      }
    }

  }
}

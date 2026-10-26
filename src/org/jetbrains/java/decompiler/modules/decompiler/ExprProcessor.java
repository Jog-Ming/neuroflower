// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.api.Decompiler;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.api.plugin.StatementWriter;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.code.MethodProperties;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectEdgeType;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.FieldDescriptor;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectNode;
import org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructContext;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructBootstrapMethodsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructConstantValueAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructNestHostAttribute;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.TextUtil;

import java.util.*;

public class ExprProcessor implements CodeConstants {
  public static final String UNDEFINED_TYPE_STRING = "<undefinedtype>";
  public static final String UNREPRESENTABLE_TYPE_STRING = "<unrepresentable>";
  public static final String UNKNOWN_TYPE_STRING = "<unknown>";
  public static final String NULL_TYPE_STRING = "<null>";

  private static final Map<Integer, FunctionType> mapConsts = new HashMap<>();
  static {
    mapConsts.put(opc_arraylength, FunctionType.ARRAY_LENGTH);
    mapConsts.put(opc_checkcast, FunctionType.CAST);
    mapConsts.put(opc_instanceof, FunctionType.INSTANCEOF);
  }

  private static final VarType[] consts = {
    VarType.VARTYPE_INT, VarType.VARTYPE_FLOAT, VarType.VARTYPE_LONG, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_CLASS, VarType.VARTYPE_STRING,
    VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID,
    VarType.VARTYPE_VOID, VarType.VARTYPE_METHODTYPE
  };

  private static final VarType[] varTypes = {
    VarType.VARTYPE_INT, VarType.VARTYPE_LONG, VarType.VARTYPE_FLOAT, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_OBJECT
  };

  private static final VarType[] arrTypes = {
    VarType.VARTYPE_INT, VarType.VARTYPE_LONG, VarType.VARTYPE_FLOAT, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_OBJECT,
    VarType.VARTYPE_BOOLEAN, VarType.VARTYPE_CHAR, VarType.VARTYPE_SHORT
  };

  private static final FunctionType[] func1 = {
    FunctionType.ADD, FunctionType.SUB, FunctionType.MUL, FunctionType.DIV,
    FunctionType.REM
  };
  private static final FunctionType[] func2 = {
    FunctionType.SHL, FunctionType.SHR, FunctionType.USHR, FunctionType.AND,
    FunctionType.OR, FunctionType.XOR
  };
  private static final FunctionType[] func3 = {
    FunctionType.I2L, FunctionType.I2F, FunctionType.I2D, FunctionType.L2I,
    FunctionType.L2F, FunctionType.L2D, FunctionType.F2I, FunctionType.F2L,
    FunctionType.F2D, FunctionType.D2I, FunctionType.D2L, FunctionType.D2F,
    FunctionType.I2B, FunctionType.I2C, FunctionType.I2S
  };
  private static final FunctionType[] func4 = {
    FunctionType.LCMP, FunctionType.FCMPL, FunctionType.FCMPG, FunctionType.DCMPL,
    FunctionType.DCMPG
  };
  private static final IfExprent.Type[] func5 = {
    IfExprent.Type.EQ, IfExprent.Type.NE, IfExprent.Type.LT, IfExprent.Type.GE, IfExprent.Type.GT, IfExprent.Type.LE
  };
  private static final IfExprent.Type[] func6 = {
    IfExprent.Type.ICMPEQ, IfExprent.Type.ICMPNE, IfExprent.Type.ICMPLT, IfExprent.Type.ICMPGE, IfExprent.Type.ICMPGT, IfExprent.Type.ICMPLE,
    IfExprent.Type.ACMPEQ, IfExprent.Type.ACMPNE
  };
  private static final IfExprent.Type[] func7 = {IfExprent.Type.NULL, IfExprent.Type.NONNULL};
  private static final MonitorExprent.Type[] func8 = {MonitorExprent.Type.ENTER, MonitorExprent.Type.EXIT};

  private static final CodeType[] arrTypeIds = {
    CodeType.BOOLEAN, CodeType.CHAR, CodeType.FLOAT, CodeType.DOUBLE,
    CodeType.BYTE, CodeType.SHORT, CodeType.INT, CodeType.LONG
  };

  private static final String[] typeNames = {"byte", "char", "double", "float", "int", "long", "short", "boolean"};

  private final MethodDescriptor methodDescriptor;
  private final VarProcessor varProcessor;

  public ExprProcessor(MethodDescriptor md, VarProcessor varProc) {
    methodDescriptor = md;
    varProcessor = varProc;
  }

  public void processStatement(RootStatement root, StructClass cl) {
    FlattenStatementsHelper flatHelper = new FlattenStatementsHelper();
    DirectGraph dgraph = flatHelper.buildDirectGraph(root);

    ValidationHelper.validateDGraph(dgraph, root);

    // TODO: use DirectNode instead DirectNode.id
    Map<String, VarExprent> mapCatch = new HashMap<>();
    collectCatchVars(root, flatHelper, mapCatch);

    Map<DirectNode, PrimitiveExprsList> mapData = new HashMap<>();

    ListStack<DirectNode> stack = new ListStack<>();

    stack.push(dgraph.first);
    mapData.put(dgraph.first, new PrimitiveExprsList());

    while (!stack.isEmpty()) {

      DirectNode node = stack.pop();

      PrimitiveExprsList data;
      if (mapCatch.containsKey(node.id)) {
        data = getExpressionData(mapCatch.get(node.id));
      } else {
        data = mapData.get(node);
      }

      BasicBlockStatement block = node.block;
      if (block != null) {
        processBlock(block, data, cl);
        block.setExprents(data.getLstExprents());
      }

      // TODO: is this copying the stack into catch and finally blocks? It shouldn't do that.
      for (var cd : node.getSuccessors(DirectEdgeType.REGULAR)) {
        DirectNode nd = cd.getDestination();
        if (!mapData.containsKey(nd)) {
          mapData.put(nd, copyVarExprents(data.copyStack()));
          stack.add(nd);
        }
      }
    }

    initStatementExprents(root);
  }

  private static PrimitiveExprsList copyVarExprents(PrimitiveExprsList data) {
    ListStack<Exprent> stack = data.getStack();
    copyEntries(stack);
    return data;
  }

  public static void copyEntries(List<Exprent> stack) {
    for (int i = 0; i < stack.size(); i++) {
      stack.set(i, stack.get(i).copy());
    }
  }

  private static void collectCatchVars(Statement stat, FlattenStatementsHelper flatthelper, Map<String, VarExprent> map) {

    List<VarExprent> lst = null;

    if (stat instanceof CatchAllStatement) {
      CatchAllStatement catchall = (CatchAllStatement)stat;
      if (!catchall.isFinally()) {
        lst = catchall.getVars();
      }
    }
    else if (stat instanceof CatchStatement) {
      lst = ((CatchStatement)stat).getVars();
    }

    if (lst != null) {
      for (int i = 1; i < stat.getStats().size(); i++) {
        map.put(flatthelper.getDirectNode(stat.getStats().get(i)).id, lst.get(i - 1));
      }
    }

    for (Statement st : stat.getStats()) {
      collectCatchVars(st, flatthelper, map);
    }
  }

  private static void initStatementExprents(Statement stat) {
    stat.initExprents();

    for (Statement st : stat.getStats()) {
      initStatementExprents(st);
    }
  }

  public void processBlock(BasicBlockStatement stat, PrimitiveExprsList data, StructClass cl) {

    ConstantPool pool = cl.getPool();
    StructBootstrapMethodsAttribute bootstrap = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_BOOTSTRAP_METHODS);

    BasicBlock block = stat.getBlock();

    ListStack<Exprent> stack = data.getStack();
    List<Exprent> exprlist = data.getLstExprents();

    InstructionSequence seq = block.getSeq();

    // A constant variable read through a qualifying expression leaves only the qualifier's null
    // check in the class file: javac inlines the value at the access site. The constant push right
    // after the check is replaced by the field access it stands for.
    Exprent pendingFieldAccess = null;
    int pendingFieldIndex = -1;

    for (int i = 0; i < seq.length(); i++) {

      Instruction instr = seq.getInstr(i);
      int bytecode_offset = instr.startOffset;
      BitSet bytecode_offsets = null;
      if (bytecode_offset >= 0) {
        bytecode_offsets = new BitSet();
        bytecode_offsets.set(bytecode_offset, bytecode_offset + instr.length);
      }

      if (i == pendingFieldIndex) {
        pendingFieldAccess.addBytecodeOffsets(bytecode_offsets);
        pushEx(stack, exprlist, pendingFieldAccess);
        pendingFieldAccess = null;
        pendingFieldIndex = -1;
        continue;
      }

      switch (instr.opcode) {
        case opc_aconst_null:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_NULL, null, bytecode_offsets));
          break;
        case opc_bipush:
        case opc_sipush:
          pushEx(stack, exprlist, new ConstExprent(instr.operand(0), true, bytecode_offsets));
          break;
        case opc_lconst_0:
        case opc_lconst_1:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_LONG, (long)(instr.opcode - opc_lconst_0), bytecode_offsets));
          break;
        case opc_fconst_0:
        case opc_fconst_1:
        case opc_fconst_2:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_FLOAT, (float)(instr.opcode - opc_fconst_0), bytecode_offsets));
          break;
        case opc_dconst_0:
        case opc_dconst_1:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_DOUBLE, (double)(instr.opcode - opc_dconst_0), bytecode_offsets));
          break;
        case opc_ldc:
        case opc_ldc_w:
        case opc_ldc2_w:
          PooledConstant cn = pool.getConstant(instr.operand(0));
          if (cn instanceof PrimitiveConstant) {
            pushEx(stack, exprlist, new ConstExprent(consts[cn.type - CONSTANT_Integer], ((PrimitiveConstant)cn).value, bytecode_offsets));
          }
          else if (cn instanceof LinkConstant && cn.type == CodeConstants.CONSTANT_Dynamic) {
            LinkConstant invoke_constant = (LinkConstant) cn;

            LinkConstant bootstrapMethod = null;
            List<PooledConstant> bootstrap_arguments = null;
            if (bootstrap != null) {
              bootstrapMethod = bootstrap.getMethodReference(invoke_constant.index1);
              bootstrap_arguments = bootstrap.getMethodArguments(invoke_constant.index1);
            }

            InvocationExprent exprinv = new InvocationExprent(instr.opcode, invoke_constant, bootstrapMethod, bootstrap_arguments, stack, bytecode_offsets);
            if (exprinv.getDescriptor().ret.type == CodeType.VOID) {
              exprlist.add(exprinv);
            }
            else {
              pushEx(stack, exprlist, CondyHelper.simplifyCondy(exprinv));
            }
          }
          else if (cn instanceof LinkConstant) {
            //TODO: for now treat Links as Strings
            pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_STRING, ((LinkConstant)cn).elementname, bytecode_offsets));
          }
          break;
        case opc_iload:
        case opc_lload:
        case opc_fload:
        case opc_dload:
        case opc_aload:
          VarExprent varExprent = new VarExprent(instr.operand(0), varTypes[instr.opcode - opc_iload], varProcessor, bytecode_offsets);
          varExprent.setBackingInstr(instr);
          varProcessor.findLVT(varExprent, bytecode_offset + instr.length);
          pushEx(stack, exprlist, varExprent);
          break;
        case opc_iaload:
        case opc_laload:
        case opc_faload:
        case opc_daload:
        case opc_aaload:
        case opc_baload:
        case opc_caload:
        case opc_saload:
          Exprent index = stack.pop();
          Exprent arr = stack.pop();

          VarType vartype = null;
          switch (instr.opcode) {
            case opc_laload:
              vartype = VarType.VARTYPE_LONG;
              break;
            case opc_daload:
              vartype = VarType.VARTYPE_DOUBLE;
          }
          pushEx(stack, exprlist, new ArrayExprent(arr, index, arrTypes[instr.opcode - opc_iaload], bytecode_offsets), vartype);
          break;
        case opc_istore:
        case opc_lstore:
        case opc_fstore:
        case opc_dstore:
        case opc_astore:
          Exprent expr = stack.pop();
          int varindex = instr.operand(0);
          if (bytecode_offsets != null) { //TODO: Figure out why this nulls in some cases
            bytecode_offsets.set(bytecode_offset, bytecode_offset + instr.length);
          }
          varExprent = new VarExprent(varindex, varTypes[instr.opcode - opc_istore], varProcessor, bytecode_offsets);
          varExprent.setBackingInstr(instr);
          varProcessor.findLVT(varExprent, bytecode_offset + instr.length);
          AssignmentExprent assign = new AssignmentExprent(varExprent, expr, bytecode_offsets);
          exprlist.add(assign);
          break;
        case opc_iastore:
        case opc_lastore:
        case opc_fastore:
        case opc_dastore:
        case opc_aastore:
        case opc_bastore:
        case opc_castore:
        case opc_sastore:
          Exprent value = stack.pop();
          Exprent index_store = stack.pop();
          Exprent arr_store = stack.pop();
          AssignmentExprent arrassign =
            new AssignmentExprent(new ArrayExprent(arr_store, index_store, arrTypes[instr.opcode - opc_iastore], bytecode_offsets), value,
                                  bytecode_offsets);
          exprlist.add(arrassign);
          break;
        case opc_iadd:
        case opc_ladd:
        case opc_fadd:
        case opc_dadd:
        case opc_isub:
        case opc_lsub:
        case opc_fsub:
        case opc_dsub:
        case opc_imul:
        case opc_lmul:
        case opc_fmul:
        case opc_dmul:
        case opc_idiv:
        case opc_ldiv:
        case opc_fdiv:
        case opc_ddiv:
        case opc_irem:
        case opc_lrem:
        case opc_frem:
        case opc_drem:
          pushEx(stack, exprlist, new FunctionExprent(func1[(instr.opcode - opc_iadd) / 4], stack, bytecode_offsets));
          break;
        case opc_ishl:
        case opc_lshl:
        case opc_ishr:
        case opc_lshr:
        case opc_iushr:
        case opc_lushr:
        case opc_iand:
        case opc_land:
        case opc_ior:
        case opc_lor:
        case opc_ixor:
        case opc_lxor:
          pushEx(stack, exprlist, new FunctionExprent(func2[(instr.opcode - opc_ishl) / 2], stack, bytecode_offsets));
          break;
        case opc_ineg:
        case opc_lneg:
        case opc_fneg:
        case opc_dneg:
          pushEx(stack, exprlist, new FunctionExprent(FunctionType.NEG, stack, bytecode_offsets));
          break;
        case opc_iinc:
          VarExprent vevar = new VarExprent(instr.operand(0), VarType.VARTYPE_INT, varProcessor, bytecode_offsets);
          vevar.setBackingInstr(instr);
          varProcessor.findLVT(vevar, bytecode_offset + instr.length);
          exprlist.add(new AssignmentExprent(vevar, new FunctionExprent(
            instr.operand(1) < 0 ? FunctionType.SUB : FunctionType.ADD, Arrays
            .asList(vevar.copy(), new ConstExprent(VarType.VARTYPE_INT, Math.abs(instr.operand(1)), null)),
            bytecode_offsets), bytecode_offsets));
          break;
        case opc_i2l:
        case opc_i2f:
        case opc_i2d:
        case opc_l2i:
        case opc_l2f:
        case opc_l2d:
        case opc_f2i:
        case opc_f2l:
        case opc_f2d:
        case opc_d2i:
        case opc_d2l:
        case opc_d2f:
        case opc_i2b:
        case opc_i2c:
        case opc_i2s:
          pushEx(stack, exprlist, new FunctionExprent(func3[instr.opcode - opc_i2l], stack, bytecode_offsets));
          break;
        case opc_lcmp:
        case opc_fcmpl:
        case opc_fcmpg:
        case opc_dcmpl:
        case opc_dcmpg:
          pushEx(stack, exprlist, new FunctionExprent(func4[instr.opcode - opc_lcmp], stack, bytecode_offsets));
          break;
        case opc_ifeq:
        case opc_ifne:
        case opc_iflt:
        case opc_ifge:
        case opc_ifgt:
        case opc_ifle:
          exprlist.add(new IfExprent(func5[instr.opcode - opc_ifeq].getNegative(), stack, bytecode_offsets));
          break;
        case opc_if_icmpeq:
        case opc_if_icmpne:
        case opc_if_icmplt:
        case opc_if_icmpge:
        case opc_if_icmpgt:
        case opc_if_icmple:
        case opc_if_acmpeq:
        case opc_if_acmpne:
          exprlist.add(new IfExprent(func6[instr.opcode - opc_if_icmpeq].getNegative(), stack, bytecode_offsets));
          break;
        case opc_ifnull:
        case opc_ifnonnull:
          exprlist.add(new IfExprent(func7[instr.opcode - opc_ifnull].getNegative(), stack, bytecode_offsets));
          break;
        case opc_tableswitch:
        case opc_lookupswitch:
          exprlist.add(new SwitchHeadExprent(stack.pop(), bytecode_offsets));
          break;
        case opc_ireturn:
        case opc_lreturn:
        case opc_freturn:
        case opc_dreturn:
        case opc_areturn:
        case opc_return:
        case opc_athrow:
          exprlist.add(new ExitExprent(instr.opcode == opc_athrow ? ExitExprent.Type.THROW : ExitExprent.Type.RETURN,
                                       instr.opcode == opc_return ? null : stack.pop(),
                                       instr.opcode == opc_athrow ? null : methodDescriptor.ret,
                                       bytecode_offsets, methodDescriptor));
          break;
        case opc_monitorenter:
        case opc_monitorexit:
          MonitorExprent monitor = new MonitorExprent(func8[instr.opcode - opc_monitorenter], stack.pop(), bytecode_offsets);

          if (instr.opcode == opc_monitorexit && stat.isRemovableMonitorexit()) {
            monitor.setRemove(true);
          }

          exprlist.add(monitor);
          break;
        case opc_checkcast:
        case opc_instanceof:
          stack.push(new ConstExprent(new VarType(pool.getPrimitiveConstant(instr.operand(0)).getString(), true), null, null));
        case opc_arraylength:
          FunctionExprent recorded = new FunctionExprent(mapConsts.get(instr.opcode), stack, bytecode_offsets);
          if (instr.opcode == opc_checkcast) {
            recorded.setRecordedCheckcast();
          }
          pushEx(stack, exprlist, recorded);
          break;
        case opc_getstatic:
        case opc_getfield:
          pushEx(stack, exprlist,
                 new FieldExprent(pool.getLinkConstant(instr.operand(0)), instr.opcode == opc_getstatic ? null : stack.pop(),
                                  bytecode_offsets));
          break;
        case opc_putstatic:
        case opc_putfield:
          Exprent valfield = stack.pop();
          Exprent exprfield =
            new FieldExprent(pool.getLinkConstant(instr.operand(0)), instr.opcode == opc_putstatic ? null : stack.pop(),
                             bytecode_offsets);
          exprlist.add(new AssignmentExprent(exprfield, valfield, bytecode_offsets));
          break;
        case opc_invokevirtual:
        case opc_invokespecial:
        case opc_invokestatic:
        case opc_invokeinterface:
        case opc_invokedynamic:
          if (instr.opcode != opc_invokedynamic || instr.bytecodeVersion.hasInvokeDynamic()) {
            LinkConstant invoke_constant = pool.getLinkConstant(instr.operand(0));

            LinkConstant bootstrapMethod = null;
            List<PooledConstant> bootstrap_arguments = null;
            if (instr.opcode == opc_invokedynamic && bootstrap != null) {
              bootstrapMethod = bootstrap.getMethodReference(invoke_constant.index1);
              bootstrap_arguments = bootstrap.getMethodArguments(invoke_constant.index1);
            }

            InvocationExprent exprinv = new InvocationExprent(instr.opcode, invoke_constant, bootstrapMethod, bootstrap_arguments, stack, bytecode_offsets);
            if (exprinv.getDescriptor().ret.type == CodeType.VOID) {
              exprlist.add(exprinv);
            }
            else {
              pushEx(stack, exprlist, exprinv);
            }
          }
          break;
        case opc_new:
        case opc_anewarray:
        case opc_multianewarray:
          int dimensions = (instr.opcode == opc_new) ? 0 : (instr.opcode == opc_anewarray) ? 1 : instr.operand(1);
          VarType arrType = new VarType(pool.getPrimitiveConstant(instr.operand(0)).getString(), true);
          if (instr.opcode != opc_multianewarray) {
            arrType = arrType.resizeArrayDim(arrType.arrayDim + dimensions);
          }
          pushEx(stack, exprlist, new NewExprent(arrType, stack, dimensions, bytecode_offsets));
          break;
        case opc_newarray:
          pushEx(stack, exprlist, new NewExprent(new VarType(arrTypeIds[instr.operand(0) - 4], 1), stack, 1, bytecode_offsets));
          break;
        case opc_dup:
          pushEx(stack, exprlist, stack.getByOffset(-1).copy());
          break;
        case opc_dup_x1:
          insertByOffsetEx(-2, stack, exprlist, -1);
          break;
        case opc_dup_x2:
          if (stack.getByOffset(-2).getExprType().stackSize == 2) {
            insertByOffsetEx(-2, stack, exprlist, -1);
          }
          else {
            insertByOffsetEx(-3, stack, exprlist, -1);
          }
          break;
        case opc_dup2:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            pushEx(stack, exprlist, stack.getByOffset(-1).copy());
          }
          else {
            pushEx(stack, exprlist, stack.getByOffset(-2).copy());
            pushEx(stack, exprlist, stack.getByOffset(-2).copy());
          }
          break;
        case opc_dup2_x1:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            insertByOffsetEx(-2, stack, exprlist, -1);
          }
          else {
            insertByOffsetEx(-3, stack, exprlist, -2);
            insertByOffsetEx(-3, stack, exprlist, -1);
          }
          break;
        case opc_dup2_x2:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            if (stack.getByOffset(-2).getExprType().stackSize == 2) {
              insertByOffsetEx(-2, stack, exprlist, -1);
            }
            else {
              insertByOffsetEx(-3, stack, exprlist, -1);
            }
          }
          else {
            if (stack.getByOffset(-3).getExprType().stackSize == 2) {
              insertByOffsetEx(-3, stack, exprlist, -2);
              insertByOffsetEx(-3, stack, exprlist, -1);
            }
            else {
              insertByOffsetEx(-4, stack, exprlist, -2);
              insertByOffsetEx(-4, stack, exprlist, -1);
            }
          }
          break;
        case opc_swap:
          insertByOffsetEx(-2, stack, exprlist, -1);
          stack.pop();
          break;
        case opc_pop:
          stack.pop();
          // check for synthetic getClass and requireNonNull calls added by the compiler
          // see https://stackoverflow.com/a/20130641
          if (!exprlist.isEmpty()) {
            Exprent last = exprlist.get(exprlist.size() - 1);
            // Our heuristic is checking for an assignment and the type of the assignment is an invocation.
            // This roughly corresponds to a pattern of DUP [nullcheck] POP.
            if (last instanceof AssignmentExprent && ((AssignmentExprent)last).getRight() instanceof InvocationExprent) {
              InvocationExprent invocation = (InvocationExprent) ((AssignmentExprent) last).getRight();

              // Check to make sure there's still more opcodes after this one
              if (i + 1 < seq.length()) {
                // Match either this.getClass() or Objects.requireNonNull([value]);
                if ((!invocation.isStatic() && invocation.getName().equals("getClass") && invocation.getStringDescriptor().equals("()Ljava/lang/Class;")) // J8
                  || (invocation.isStatic() && invocation.getClassname().equals("java/util/Objects") && invocation.getName().equals("requireNonNull") && invocation.getStringDescriptor().equals("(Ljava/lang/Object;)Ljava/lang/Object;"))) { // J9+

                  // Ensure that these null checks are constant loads, LDC opcodes, null loads, bi/sipushes, or astores.
                  int nextOpc = seq.getInstr(i + 1).opcode;
                  if ((nextOpc >= opc_aconst_null && nextOpc <= opc_ldc2_w) || (nextOpc == opc_astore || (nextOpc >= opc_astore_0 && nextOpc <= opc_astore_3))) {
                    invocation.setSyntheticNullCheck();

                    // Objects.requireNonNull(qualifier); pop; <constant> is how javac reads an
                    // instance constant variable through a qualifying expression: the qualifier is
                    // null-checked, the value is inlined. The pushed constant is the field access.
                    if (nextOpc >= opc_aconst_null && nextOpc <= opc_ldc2_w) {
                      FieldExprent access = constantVariableAccess(invocation, exprlist, seq.getInstr(i + 1), pool, cl,
                        methodDescriptor, varProcessor.getMethod().hasModifier(CodeConstants.ACC_STATIC),
                        varProcessor, seq.getInstr(i + 1).startOffset);
                      if (access != null) {
                        // The check itself is not printed: javac re-emits it from the field access.
                        // Dropping the assignment here also keeps the qualified value's copy from
                        // resolving to the check's result, which shares its stack slot.
                        exprlist.remove(exprlist.size() - 1);
                        pendingFieldAccess = access;
                        pendingFieldIndex = i + 1;
                      }
                    }
                  }
                }
              }
            }
          }
          break;
        case opc_pop2:
          if (stack.getByOffset(-1).getExprType().stackSize == 1) {
            // Since value at the top of the stack is a value of category 1 (JVMS9 2.11.1)
            // we should remove one more item from the stack.
            // See JVMS9 pop2 chapter.
            stack.pop();
          }
          stack.pop();
          break;
      }
    }
  }

  private void pushEx(ListStack<Exprent> stack, List<Exprent> exprlist, Exprent exprent) {
    pushEx(stack, exprlist, exprent, null);
  }

  private void pushEx(ListStack<Exprent> stack, List<Exprent> exprlist, Exprent exprent, VarType vartype) {
    ValidationHelper.notNull(exprent);

    int varindex = VarExprent.STACK_BASE + stack.size();
    VarExprent var = new VarExprent(varindex, vartype == null ? exprent.getExprType() : vartype, varProcessor);
    var.setStack(true);

    exprlist.add(new AssignmentExprent(var, exprent, null));
    stack.push(var.copy());
  }

  private void insertByOffsetEx(int offset, ListStack<Exprent> stack, List<Exprent> exprlist, int copyoffset) {

    int base = VarExprent.STACK_BASE + stack.size();

    LinkedList<VarExprent> lst = new LinkedList<>();

    for (int i = -1; i >= offset; i--) {
      Exprent varex = stack.pop();
      VarExprent varnew = new VarExprent(base + i + 1, varex.getExprType(), varProcessor);
      varnew.setStack(true);
      exprlist.add(new AssignmentExprent(varnew, varex, null));
      lst.add(0, (VarExprent)varnew.copy());
    }

    Exprent exprent = lst.get(lst.size() + copyoffset).copy();
    VarExprent var = new VarExprent(base + offset, exprent.getExprType(), varProcessor);
    var.setStack(true);
    exprlist.add(new AssignmentExprent(var, exprent, null));
    lst.add(0, (VarExprent)var.copy());

    for (VarExprent expr : lst) {
      stack.push(expr);
    }
  }

  private static final int CONSTANT_EXACT = 0;
  private static final int CONSTANT_WIDENED = 1;
  private static final int CONSTANT_NO_MATCH = -1;

  /**
   * The field access a constant-variable read stands for, or {@code null} when the null check is
   * not one.
   *
   * <p>javac reads a constant variable through a qualifying expression by evaluating the
   * qualifier, null-checking it ({@code Objects.requireNonNull(qualifier)} + {@code pop}) and
   * pushing the inlined value. The class file records exactly that shape, and its position is the
   * evidence: a constant push right after such a check is the value of an instance constant field
   * of the qualifier's static type. The declaring class and field name are absent from the
   * constant pool (the access was inlined), so the field is chosen from the qualifier's type and
   * superclasses by value, with the same conversions javac applies when it pushes the constant.
   */
  private static FieldExprent constantVariableAccess(InvocationExprent invocation, List<Exprent> exprlist,
                                                     Instruction next, ConstantPool pool, StructClass cl,
                                                     MethodDescriptor methodDescriptor, boolean isStatic,
                                                     VarProcessor varProcessor, int offset) {
    if (!invocation.isStatic()
      || !invocation.getClassname().equals("java/util/Objects")
      || !invocation.getName().equals("requireNonNull")
      || invocation.getLstParameters().size() != 1) {
      return null;
    }

    if (!(invocation.getLstParameters().get(0) instanceof VarExprent argument)) {
      return null;
    }

    // The value the null check guarded is the most recent assignment to the same stack variable.
    // A parameter or local read directly into the check has no such assignment: the loaded
    // variable itself is the qualifier.
    Exprent qualifier = null;
    for (int i = exprlist.size() - 2; i >= 0; i--) {
      Exprent exprent = exprlist.get(i);
      if (exprent instanceof AssignmentExprent assignment
        && assignment.getLeft() instanceof VarExprent left
        && left.equalsVersions(argument)) {
        qualifier = assignment.getRight();
        break;
      }
    }
    if (qualifier == null && !argument.isStack() && argument.getLVT() != null) {
      qualifier = argument.copy();
    }
    if (qualifier == null) {
      return null;
    }

    ConstExprent pushed = pushedConstant(next, pool);
    if (pushed == null || pushed.getValue() == null) {
      return null;
    }

    VarType qualifierType = qualifier.getExprType();
    if (qualifier instanceof VarExprent qualifierVar) {
      // A parameter carries no LocalVariableTable entry at parse time (its entry starts at pc 0,
      // not after a load); the enclosing descriptor gives its declared type. A local that the
      // table does cover uses its entry. The parse-time stack type is only the category.
      VarType declared = qualifierVar.getLVT() != null ? qualifierVar.getLVT().getVarType()
        : parameterType(qualifierVar, cl, methodDescriptor, isStatic);
      if ((declared == null || declared.type != CodeType.OBJECT) && varProcessor.hasLVT()) {
        // Only the load that opens a variable's scope carries its table entry while the
        // expression list is built; a later load still has the entry whose range covers this pc.
        LocalVariable covering = null;
        List<LocalVariable> candidates =
          varProcessor.getCandidates(qualifierVar.getIndex());
        if (candidates != null) {
          for (LocalVariable candidate : candidates) {
            if (candidate.getStart() <= offset && offset < candidate.getEnd()
              && (covering == null || candidate.getStart() > covering.getStart())) {
              covering = candidate;
            }
          }
        }
        if (covering != null) {
          declared = covering.getVarType();
        }
      }
      if (declared != null && declared.type == CodeType.OBJECT && declared.arrayDim == 0) {
        qualifierType = declared;
      }
    }
    if (qualifierType.type != CodeType.OBJECT || qualifierType.arrayDim != 0) {
      return null;
    }

    StructClass owner = DecompilerContext.getStructContext().getClass(qualifierType.value);    if (owner == null) {
      return null;
    }

    FieldExprent exact = null;
    FieldExprent widened = null;
    Set<String> hidden = new HashSet<>();
    while (owner != null) {
      Set<String> declaredHere = new HashSet<>();
      for (StructField field : owner.getFields()) {
        if (hidden.contains(field.getName())) {
          continue; // a class on the path from the qualifier's type declares this name
        }
        declaredHere.add(field.getName());

        int access = field.getAccessFlags();
        if ((access & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) != CodeConstants.ACC_FINAL) {
          continue; // an instance constant variable is final and has no ConstantValue otherwise
        }
        StructConstantValueAttribute value = field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
        if (value == null) {
          continue;
        }
        PrimitiveConstant constant = owner.getPool().getPrimitiveConstant(value.getIndex());
        if (constant == null || constant.value == null || !accessibleFrom(cl, owner, access)) {
          continue;
        }

        int rank = constantMatch(field.getDescriptor(), constant.value, pushed.getConstType(), pushed.getValue());
        if (rank == CONSTANT_NO_MATCH) {
          continue;
        }

        // The field is read off the checked value itself, not off a copy of its expression: the
        // check's assignment is dropped, so this use resolves to the qualifier's own definition.
        FieldExprent candidate = new FieldExprent(field.getName(), owner.qualifiedName, false, argument.copy(),
          FieldDescriptor.parseDescriptor(field.getDescriptor()), null);
        if (rank == CONSTANT_EXACT) {
          if (exact == null) {
            exact = candidate;
          }
        }
        else if (widened == null) {
          widened = candidate;
        }
      }
      hidden.addAll(declaredHere);
      owner = owner.superClass == null ? null : DecompilerContext.getStructContext().getClass(owner.superClass.getString());
    }

    return exact != null ? exact : widened;
  }

  /** The declared type of a parameter slot in the method being decompiled. */
  private static VarType parameterType(VarExprent var, StructClass cl, MethodDescriptor descriptor, boolean isStatic) {
    int slot = var.getIndex();
    int position = 0;
    if (!isStatic) {
      if (slot == 0) {
        return new VarType("L" + cl.qualifiedName + ";");
      }
      position = 1;
    }
    for (VarType param : descriptor.params) {
      if (position == slot) {
        return param;
      }
      position += param.stackSize;
      if (position > slot) {
        return null;
      }
    }
    return null;
  }

  /** The pushed constant of a constant instruction, built as the main switch builds it. */
  private static ConstExprent pushedConstant(Instruction instr, ConstantPool pool) {
    switch (instr.opcode) {
      case opc_bipush:
      case opc_sipush:
        return new ConstExprent(instr.operand(0), true, null);
      case opc_lconst_0:
      case opc_lconst_1:
        return new ConstExprent(VarType.VARTYPE_LONG, (long)(instr.opcode - opc_lconst_0), null);
      case opc_fconst_0:
      case opc_fconst_1:
      case opc_fconst_2:
        return new ConstExprent(VarType.VARTYPE_FLOAT, (float)(instr.opcode - opc_fconst_0), null);
      case opc_dconst_0:
      case opc_dconst_1:
        return new ConstExprent(VarType.VARTYPE_DOUBLE, (double)(instr.opcode - opc_dconst_0), null);
      case opc_ldc:
      case opc_ldc_w:
      case opc_ldc2_w:
        PooledConstant constant = pool.getConstant(instr.operand(0));
        if (constant instanceof PrimitiveConstant) {
          return new ConstExprent(consts[constant.type - CONSTANT_Integer], ((PrimitiveConstant)constant).value, null);
        }
        return null;
      default:
        return null;
    }
  }

  /**
   * How a field's constant fits the pushed literal: exactly its declared type, or through a
   * conversion javac performs while pushing the constant (widening), which reproduces the same
   * pushed constant. Narrowing conversions are not implicit and never match.
   */
  private static int constantMatch(String descriptor, Object fieldValue, VarType pushedType, Object pushed) {
    if (pushedType.type == CodeType.BOOLEAN) {
      return descriptor.equals("Z") && fieldValue instanceof Integer flag && pushed instanceof Integer bit
        ? ((flag != 0) == (bit != 0) ? CONSTANT_EXACT : CONSTANT_NO_MATCH) : CONSTANT_NO_MATCH;
    }

    switch (descriptor) {
      case "I":
        if (!(fieldValue instanceof Integer number)) {
          return CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Integer target) {
          return number.intValue() == target.intValue() ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Long target) {
          return number.longValue() == target ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Float target) {
          return Float.compare(number.floatValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Double target) {
          return Double.compare(number.doubleValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        return CONSTANT_NO_MATCH;
      case "J":
        if (!(fieldValue instanceof Long number)) {
          return CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Long target) {
          return number.longValue() == target ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Float target) {
          return Float.compare(number.floatValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Double target) {
          return Double.compare(number.doubleValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        return CONSTANT_NO_MATCH;
      case "F":
        if (!(fieldValue instanceof Float number)) {
          return CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Float target) {
          return Float.compare(number, target) == 0 ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Double target) {
          return Double.compare(number.doubleValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        return CONSTANT_NO_MATCH;
      case "D":
        if (!(fieldValue instanceof Double number)) {
          return CONSTANT_NO_MATCH;
        }
        return pushed instanceof Double target && Double.compare(number, target) == 0 ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
      case "Ljava/lang/String;":
        return pushed instanceof String target && fieldValue instanceof String text && text.equals(target)
          ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
      default:
        return CONSTANT_NO_MATCH;
    }
  }

  private static boolean accessibleFrom(StructClass current, StructClass owner, int access) {
    if ((access & CodeConstants.ACC_PUBLIC) != 0) {
      return true;
    }
    if ((access & CodeConstants.ACC_PRIVATE) != 0) {
      return nestHost(current).equals(nestHost(owner));
    }
    return packageOf(current.qualifiedName).equals(packageOf(owner.qualifiedName));
  }

  private static String nestHost(StructClass cls) {
    StructNestHostAttribute host = cls.getAttribute(StructGeneralAttribute.ATTRIBUTE_NEST_HOST);
    return host == null ? cls.qualifiedName : host.getHostClass(cls.getPool());
  }

  private static String packageOf(String internal) {
    int slash = internal.lastIndexOf('/');
    return slash < 0 ? "" : internal.substring(0, slash);
  }

  public static boolean canonicalizeCasts(RootStatement stat) {
    boolean res = false;
    while (canonicalizeCasts((Statement) stat)) {
      res = true;
    }

    return res;
  }

  private static boolean canonicalizeCasts(Statement stat) {
    boolean res = false;
    for (Statement st : stat.getStats()) {
      res |= canonicalizeCasts(st);
    }

    if (stat instanceof BasicBlockStatement) {
      for (Exprent exprent : stat.getExprents()) {
        for (Exprent ex : exprent.getAllExprents(true, true)) {

          // Remove Checkcast(Type, Checkcast(Type, ...)) and turn it just into Checkcast(Type, ...) where both have the same type
          // The extra checkcast causes issues with generic type decompilation
          if (ex instanceof FunctionExprent && ((FunctionExprent)ex).getFuncType() == FunctionExprent.FunctionType.CAST) {
            FunctionExprent func = (FunctionExprent)ex;
            Exprent inner = func.getLstOperands().get(0);
            Exprent cast = func.getLstOperands().get(1);

            if (inner instanceof FunctionExprent && ((FunctionExprent)inner).getFuncType() == FunctionExprent.FunctionType.CAST) {
              FunctionExprent func2 = (FunctionExprent)inner;
              Exprent inner2 = func2.getLstOperands().get(0);
              Exprent cast2 = func2.getLstOperands().get(1);

              if (cast.getExprType().equals(cast2.getExprType())) {
                ex.replaceExprent(inner, inner2);
                ex.addBytecodeOffsets(inner2.bytecode);
                ex.addBytecodeOffsets(inner.bytecode);
                res = true;
              }
            }
          }
        }
      }
    }

    return res;
  }

  public static void markExprOddities(RootStatement root) {
    // We shouldn't have to do this, but turns out getting cast names is not pure. Sigh.
    try (var lock = DecompilerContext.getImportCollector().lock()) {
      markExprOddities(root, root);
    }
  }

  private static void markExprOddities(RootStatement root, Statement stat) {
    for (Statement st : stat.getStats()) {
      markExprOddities(root, st);
    }

    for (Exprent ex : stat.getVarDefinitions()) {
      markExprOddity(root, ex, true);
    }

    if (stat instanceof BasicBlockStatement) {
      if (stat.isLabeled()) {
        root.addComment("$VF: Made invalid labels!", true);
      }

      for (Exprent ex : stat.getExprents()) {
        markExprOddity(root, ex, true);
      }
    }

    if (stat instanceof IfStatement ifSt) {
      markExprOddity(root, ifSt.getHeadexprent(), false);
    }
  }

  private static void markExprOddity(RootStatement root, Exprent ex, boolean block) {
    if (ex instanceof MonitorExprent) {
      root.addComment("$VF: Could not create synchronized statement, marking monitor enters and exits", true);
    }
    if (block && ex instanceof IfExprent) {
      root.addComment("$VF: Accidentally destroyed if statement, the decompiled code is not correct!", true);
    }

    ClassWrapper wrapper = AssertProcessor.getHoldingClass();
    MethodProperties prop = wrapper.getMethodProperties("<clinit>", "()V");

    for (Exprent e : ex.getAllExprents(true, true)) {
      if (e instanceof VarExprent) {
        VarExprent var = (VarExprent)e;
        if (var.isDefinition() && isInvalidTypeName(var.getDefinitionType()) || var.getExprType() == VarType.VARTYPE_UNKNOWN) {
          root.addComment("$VF: Could not properly define all variable types!", true);
        }
      } else if (e instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent)e;
        if (func.getFuncType() == FunctionType.CAST && func.doesCast()) {
          List<Exprent> operands = func.getLstOperands();
          if (isInvalidTypeName(operands.get(1).toString())) {
            root.addComment("$VF: Could not properly define all variable types!", true);
          }
        }
      } else if (e instanceof FieldExprent field) {
        if (prop != null && prop.assertField != null && root.mt != prop.mt) {
          if (field.getName().equals(prop.assertField.getName()) && field.getClassname().equals(wrapper.getClassStruct().qualifiedName)) {
            root.addComment("$VF: Could not resugar all assert statements!", true);
          }
        }
      }
    }
  }

  public static String getTypeName(VarType type) {
    return getTypeName(type, true);
  }

  public static String getTypeName(VarType type, boolean getShort) {
    CodeType tp = type.type;
    if (tp.ordinal() <= CodeType.BOOLEAN.ordinal()) {
      return typeNames[tp.ordinal()];
    }
    else if (tp == CodeType.UNKNOWN) {
      return UNKNOWN_TYPE_STRING; // INFO: should not occur
    }
    else if (tp == CodeType.NULL) {
      return NULL_TYPE_STRING; // INFO: should not occur
    }
    else if (tp == CodeType.VOID) {
      return "void";
    }
    else if (tp == CodeType.GENVAR && type.isGeneric()) {
      return type.value;
    }
    else if (tp == CodeType.OBJECT) {
      if (type.isGeneric()) {
        return ((GenericType)type).getCastName();
      }
      String ret = buildJavaClassName(type.value);
      if (getShort) {
        ret = DecompilerContext.getImportCollector().getShortName(ret);
      }

      if (ret == null) {
        ret = UNDEFINED_TYPE_STRING;
      }
      return ret;
    }

    // Unrepresentable: only for debugging
    if (tp == CodeType.BYTECHAR) {
      return "<bytechar>";
    }

    if (tp == CodeType.SHORTCHAR) {
      return "<shortchar>";
    }

    throw new RuntimeException("invalid type: " + tp);
  }

  public static boolean isInvalidTypeName(String name) {
    return UNDEFINED_TYPE_STRING.equals(name) || NULL_TYPE_STRING.equals(name) || UNKNOWN_TYPE_STRING.equals(name);
  }

  public static String getCastTypeName(VarType type) {
    return getCastTypeName(type, true);
  }

  public static String getCastTypeName(VarType type, boolean getShort) {
    StringBuilder s = new StringBuilder(getTypeName(type, getShort));
    TextUtil.append(s, "[]", type.arrayDim);
    return s.toString();
  }

  public static PrimitiveExprsList getExpressionData(VarExprent var) {
    PrimitiveExprsList prlst = new PrimitiveExprsList();
    VarExprent vartmp = new VarExprent(VarExprent.STACK_BASE, var.getExprType(), var.getProcessor());
    vartmp.setStack(true);

    VarExprent catchVar = (VarExprent) var.copy();
    catchVar.setCatchTempVar(true);
    prlst.getLstExprents().add(new AssignmentExprent(vartmp, catchVar, null));
    prlst.getStack().push(vartmp.copy());
    return prlst;
  }

  public static boolean endsWithSemicolon(Exprent expr) {
    return !(expr instanceof SwitchHeadExprent ||
             expr instanceof MonitorExprent ||
             expr instanceof IfExprent ||
             (expr instanceof VarExprent && ((VarExprent)expr).isClassDef()));
  }

  public static int addDeletedGotoInstructionMapping(Statement stat, TextBuffer buffer) {
    if (stat instanceof BasicBlockStatement) {
      BasicBlock block = ((BasicBlockStatement)stat).getBlock();
      List<Integer> offsets = block.getInstrOldOffsets();
      if (!offsets.isEmpty() &&
          offsets.size() > block.getSeq().length()) { // some instructions have been deleted, but we still have offsets
        int last = offsets.get(offsets.size() - 1);
        buffer.addBytecodeMapping(last); // add the last offset
        return last;
      }
    }
    return -1;
  }

  /** The block already left through a switch-expression yield; a jump print would be dead. */
  private static boolean yieldsFromBlock(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent instanceof YieldExprent) {
          return true;
        }
      }
    }
    return false;
  }

  public static TextBuffer jmpWrapper(Statement stat, int indent, boolean semicolon) {
    TextBuffer buf = stat.toJava(indent);

    List<StatEdge> lstSuccs = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (lstSuccs.size() == 1) {
      StatEdge edge = lstSuccs.get(0);
      if (edge.getType() != StatEdge.TYPE_REGULAR && edge.explicit && !(edge.getDestination() instanceof DummyExitStatement)
        && !yieldsFromBlock(stat)) {
        int jumpOffset = addDeletedGotoInstructionMapping(stat, buf);
        // The target starts no line at the jump when the source ended the previous statement with
        // `break;`/`continue;` on the same line; keep it there.
        boolean join = jumpOffset >= 0 && !RoundTrip.lineStartsAt(jumpOffset)
          && buf.length() >= DecompilerContext.getNewLineSeparator().length();
        if (join) {
          buf.setLength(buf.length() - DecompilerContext.getNewLineSeparator().length());
          buf.append(" ");
        } else {
          buf.appendIndent(indent);
        }

        switch (edge.getType()) {
          case StatEdge.TYPE_BREAK:
            // A break out of the loop body's last switch and a continue compile to different
            // jumps; the target's jump at this offset says which one the source wrote.
            boolean continues = !edge.labeled
              && (RoundTrip.breakJumpsToContinue(jumpOffset) || RoundTrip.emptyArmContinues(stat));
            buf.append(continues ? "continue" : "break");
            break;
          case StatEdge.TYPE_CONTINUE:
            buf.append("continue");
        }

        if (edge.labeled) {
          buf.append(" label").append(edge.closure.id);
        }
        buf.append(";").appendLineSeparator();
      }
    }

    if (buf.length() == 0 && semicolon) {
      buf.appendIndent(indent).append(";").appendLineSeparator();
    }

    return buf;
  }

  public static String buildJavaClassName(String name) {
    String res = name.replace('/', '.');

    if (res.contains("$")) { // attempt to invoke foreign member
      // classes correctly
      StructClass cl = DecompilerContext.getStructContext().getClass(name);
      if (cl == null || !cl.isOwn()) {
        res = res.replace('$', '.');
      }
    }

    return res;
  }

  public static TextBuffer listToJava(List<? extends Exprent> lst, int indent) {
    if (lst == null || lst.isEmpty()) {
      return new TextBuffer();
    }

    StructClass cl = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
    LanguageSpec spec = PluginContext.getCurrentContext().getLanguageSpec(cl);

    TextBuffer buf = new TextBuffer();
    lst = Exprent.sortIndexed(lst);

    for (Exprent expr : lst) {
      if (buf.length() > 0 && expr instanceof VarExprent && ((VarExprent)expr).isClassDef()) {
        // separates local class definition from previous statements
        buf.appendLineSeparator();
      }

      expr.getInferredExprType(null);

      TextBuffer content = expr.toJava(indent);

      if (content.length() > 0) {
        if (!(expr instanceof VarExprent) || !((VarExprent)expr).isClassDef()) {
          buf.appendIndent(indent);
        }
        buf.append(content);
        if (expr instanceof MonitorExprent && ((MonitorExprent)expr).getMonType() == MonitorExprent.Type.ENTER) {
          buf.append("{} // $VF: monitorenter "); // empty synchronized block
        }
        if (spec != null) {
          if (spec.writer.endsWithSemicolon(expr)) {
            buf.append(';');
          }
        } else {
          if (endsWithSemicolon(expr)) {
            buf.append(';');
          }
        }
        buf.appendLineSeparator();
      }
    }

    return buf;
  }

  public static ConstExprent getDefaultArrayValue(VarType arrType) {
    ConstExprent defaultVal;
    if (arrType.type == CodeType.OBJECT || arrType.arrayDim > 0) {
      defaultVal = new ConstExprent(VarType.VARTYPE_NULL, null, null);
    }
    else if (arrType.type == CodeType.FLOAT) {
      defaultVal = new ConstExprent(VarType.VARTYPE_FLOAT, 0f, null);
    }
    else if (arrType.type == CodeType.LONG) {
      defaultVal = new ConstExprent(VarType.VARTYPE_LONG, 0L, null);
    }
    else if (arrType.type == CodeType.DOUBLE) {
      defaultVal = new ConstExprent(VarType.VARTYPE_DOUBLE, 0d, null);
    }
    else { // integer types
      defaultVal = new ConstExprent(0, true, null);
    }
    return defaultVal;
  }

  public static boolean getCastedExprent(Exprent exprent,
                                         VarType leftType,
                                         TextBuffer buffer,
                                         int indent,
                                         boolean castNull) {
    return getCastedExprent(exprent, leftType, buffer, indent, castNull ? NullCastType.CAST : NullCastType.DONT_CAST, false, false, false);
  }

  public static boolean getCastedExprent(Exprent exprent,
                                         VarType leftType,
                                         TextBuffer buffer,
                                         int indent,
                                         NullCastType castNull,
                                         boolean castAlways,
                                         boolean castNarrowing,
                                         boolean unbox) {

    if (unbox) {
      // "unbox" invocation parameters, e.g. 'byteSet.add((byte)123)' or 'new ShortContainer((short)813)'
      if (exprent instanceof InvocationExprent) {
        InvocationExprent invocationExprent = (InvocationExprent) exprent;
        if (invocationExprent.isBoxingCall() && !invocationExprent.shouldForceBoxing()) {
          exprent = invocationExprent.getLstParameters().get(0);
          CodeType paramType = invocationExprent.getDescriptor().params[0].type;
          if (exprent instanceof ConstExprent && ((ConstExprent) exprent).getConstType().type != paramType) {
            leftType = new VarType(paramType);
          }
        }
      }
    }

    VarType rightType = exprent.getInferredExprType(leftType);
    if (exprent instanceof SwitchExprent switchExprent) {
      // The switch is poly in this context; the arms are printed against this target.
      switchExprent.setPrintTarget(leftType);
    }
    exprent = narrowGenericCastType(exprent, leftType);

    boolean doCast = (!leftType.higherEqualInLatticeThan(rightType) && (rightType.equals(VarType.VARTYPE_OBJECT) || leftType.type != CodeType.OBJECT));
    boolean doCastNull = (castNull.cast && rightType.type == CodeType.NULL && !UNDEFINED_TYPE_STRING.equals(getTypeName(leftType)));
    boolean doCastNarrowing = (castNarrowing && isIntConstant(exprent) && isNarrowedIntType(leftType));
    boolean doCastGenerics = !DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_NO_GENERIC_CAST)
      && doGenericTypesCast(exprent, leftType, rightType);
    // Inference substituted the upper bound into the call's type, so the wildcard the method
    // declared has vanished; the original source had to cast that capture away, and javac elides
    // the checkcast because the erasures match.
    if (!doCastGenerics
        && DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_CAPTURE_CAST)
        && exprent instanceof InvocationExprent invocation
        && needsCaptureCast(leftType, invocation.getDeclaredGenericReturnType())) {
      doCastGenerics = true;
    }
    // A target whose wildcard is a lower bound over a type variable of this scope (`? super S`)
    // accepts no captured argument: javac cannot prove the value's capture is a supertype of S,
    // whatever the value's own class is. The source cast the value to the declared target, and
    // javac elides that checkcast when the erasures already match.
    if (!doCastGenerics && !doCast && exprent instanceof InvocationExprent
        && lowerBoundedWildcardTarget(leftType) && castableToErasure(exprent, leftType)) {
      doCastGenerics = true;
    }
    // A cast whose own type arguments violate the target's bounds cannot appear in a source that
    // compiled. The inference that produced it is wrong; passing the expression on lets javac infer
    // again, which is what the original source did.
    if (doCastGenerics && !doCast && invalidGenericInstantiation(leftType)) {
      doCastGenerics = false;
    }
    // A target whose direct type argument is a type variable in scope, against a value whose same
    // position is a wildcard: a wildcard is never literally the variable, so the value does not
    // assign across an invariant position and the source cast it. Only this direction casts
    // (X<T> is an X<?>), only a value whose type the class file fixes without context is cast,
    // and an out-of-scope variable cannot be named in the cast.
    if (!doCastGenerics
      && !DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_NO_GENERIC_CAST)
      && contextIndependentValue(exprent)
      && invariantWildcardTarget(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }
    // The same mismatch one level up the hierarchy: the value's recorded type instantiates a
    // subclass, and the target instantiates its generic supertype with a type variable in scope
    // where the value has a wildcard. The subclass's own class signature gives that supertype
    // view; the wildcard is never literally the variable, so the instantiations are not in an
    // invariant assignment, and the source cast the value to the target. The cast's erasure is
    // the supertype the value already implements, so javac emits no checkcast for it.
    if (!doCastGenerics
      && !DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_NO_GENERIC_CAST)
      && contextIndependentValue(exprent)
      && wildcardSubtypeTarget(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }

    // A target of array type whose element is a type variable of the enclosing source, against a
    // value whose array element is a different type: no implicit conversion exists (arrays are
    // covariant only over reifiable element types), so a source that compiled cast the value to
    // that same array type. The call's recorded signature proves the target; the cast erases to
    // the variable's erasure, so javac either elides the checkcast or the target already has it.
    if (!doCastGenerics
      && !DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_NO_GENERIC_CAST)
      && typeVariableArrayTarget(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }

    // A cast whose type argument is a generic class written bare cannot come from a source that
    // compiled: every class file records generic types in full, so a bare argument here is the
    // printer's own inference losing arguments, and F<Bare> is not a conversion javac accepts from
    // the value's recorded F<?> or F<Concrete>. Dropping the cast lets javac infer the argument
    // again, which is what the original source did.
    if (doCastGenerics && hasRawTypeArgument(leftType)) {
      doCastGenerics = false;
    }

    // An instantiation of X cannot be cast to another instantiation of X whose arguments are
    // provably distinct: javac rejects the conversion outright, so no compiling source wrote it.
    // In an argument list the printer seeded a type variable from the call's own context and
    // javac infers it again from the value, which is what the original relied on; elsewhere the
    // value must be converted, and the source that compiled wrote the raw cast.
    boolean castRaw = false;
    if (doCastGenerics && !castAlways && !doCast && !doCastNull && !doCastNarrowing
      && provablyInconvertible(leftType, rightType)) {
      if (InvocationExprent.inArgument()) {
        doCastGenerics = false;
      } else {
        castRaw = true;
      }
    }

    // A functional argument whose inferred SAM return is a type variable neither side can name
    // produces a capture. When the target instantiates the same class with a type variable of
    // the caller, the call's own variable is constrained by the target to that named variable
    // and by the argument to the capture, so no instantiation satisfies both and javac rejects
    // the call; a source that compiled cast the result. The cast erases to the class the call
    // already returns, so it emits no checkcast. A target with a wildcard accepts the capture,
    // and a target with a concrete argument lets javac infer the variable from that target, so
    // neither needs a cast.
    if (!doCastGenerics
      && !DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_NO_GENERIC_CAST)
      && exprent instanceof InvocationExprent
      && leftType instanceof GenericType && leftType.type == CodeType.OBJECT && leftType.arrayDim == 0
      && !hasWildcard(leftType) && !hasRawTypeArgument(leftType)
      && rightType != null && rightType.isGeneric() && rightType.type == CodeType.OBJECT
      && rightType.value != null && rightType.value.equals(leftType.value)
      && hasInScopeTypeVariable(leftType, exprent.getNamedGenerics())
      && captureReturnedArgument(exprent)) {
      doCastGenerics = true;
    }

    // A target type that still names a type parameter of the callee which inference left unbound
    // has no nameable form at the call site, so a compiling source cannot have written a cast
    // built on it. Passing the expression on lets javac infer the callee's variable again. The
    // lattice conversion to a bare type variable is a cast like any other: the argument's own
    // recorded type is at or below the variable's erasure, and javac infers the callee's variable
    // from it.
    if ((doCastGenerics || doCast) && InvocationExprent.namesUnboundArgumentVariable(leftType)) {
      doCastGenerics = false;
      doCast = false;
      castRaw = false;
    }

    // A cast from an instantiation whose type argument is a wildcard capture to another
    // instantiation is illegal under JLS 5.5.1 unless the target's argument is the wildcard's
    // own bound (or below it): javac rejects the printed conversion outright. The source that
    // compiled wrote the raw erasure instead, which erases to the same class, so the class file
    // is unchanged.
    if (doCastGenerics && !castRaw && parameterizedCastIllegal(leftType, rightType)) {
      castRaw = true;
    }

    // An argument whose parameter is the raw class G but whose value is a parameterized subtype
    // of G: our solution for the callee's G<A> is the subtype's own argument, a capture javac
    // cannot use. The subtype's recorded supertype view names the parameterization the source
    // cast to (TaggedChoiceType<?> as Type<Pair<?,?>>); that view's instantiation is provably
    // distinct from the subtype's, so the source widened to the erased G first. Both steps erase
    // to the parameter's own class, so no checkcast can appear.
    boolean doubleCast = false;
    VarType doubleCastTarget = leftType;
    if (!doCastGenerics && !doCast && !castRaw && !doCastNull && !doCastNarrowing && !castAlways
      && leftType != null && leftType.type == CodeType.OBJECT && leftType.arrayDim == 0 && !leftType.isGeneric()
      && exprent instanceof InvocationExprent
      && rightType instanceof GenericType typedValue && typedValue.getWildcard() == GenericType.WILDCARD_NO
      && typedValue.type == CodeType.OBJECT && typedValue.value != null
      && !typedValue.value.equals(leftType.value)
      && DecompilerContext.getStructContext().instanceOf(typedValue.value, leftType.value)) {
      VarType view = GenericType.getGenericSuperType(typedValue, new VarType(CodeType.OBJECT, 0, leftType.value));
      boolean[] captured = new boolean[1];
      view = wildcardUnnameableInView(view, exprent.getNamedGenerics(), captured);
      if (captured[0] && view instanceof GenericType superView && leftType.value.equals(superView.value)
        && superView.getWildcard() == GenericType.WILDCARD_NO && !superView.equalsExact(typedValue)
        && !invalidGenericInstantiation(superView) && unboundedClassParameters(superView.value)) {
        doubleCastTarget = superView;
        doubleCast = true;
      }
    }

    // A generic call whose type variables our inference could only leave at their erasure (the
    // value's type is the raw class) against a parameterized target: javac re-infers the call
    // from the target and cannot solve the callee's own variables. The call's recorded return
    // Signature names the instantiation once its unnameable variables are wildcarded, and when
    // that instantiation is exactly the target, the source cast to the erased form first and
    // then to the target. Both erase to the target's class, so no checkcast can appear.
    if (!doubleCast && !doCastGenerics && !doCast && !castRaw && !doCastNull && !doCastNarrowing && !castAlways
      && leftType instanceof GenericType erasureTarget && erasureTarget.getWildcard() == GenericType.WILDCARD_NO
      && erasureTarget.arrayDim == 0 && !erasureTarget.getArguments().isEmpty()
      && !invalidGenericInstantiation(leftType) && unboundedClassParameters(erasureTarget.value)
      && exprent instanceof InvocationExprent erasureCall
      && rightType != null && rightType.type == CodeType.OBJECT && !rightType.isGeneric()
      && erasureTarget.value.equals(rightType.value)) {
      boolean[] wildcarded = new boolean[1];
      VarType named = wildcardUnnameableInView(erasureCall.getDeclaredGenericReturnType(),
        exprent.getNamedGenerics(), wildcarded);
      if (wildcarded[0] && named instanceof GenericType namedType
        && namedType.getWildcard() == GenericType.WILDCARD_NO
        && namedType.equalsExact(erasureTarget)) {
        doubleCastTarget = erasureTarget;
        doubleCast = true;
      }
    }

    // A field whose recorded type is a wildcard-ed generic (Codec<? extends Schema<?>>) passed
    // to a parameterized parameter: the value's argument is a capture, which the parameter's
    // variable cannot be inferred from, so the source cast the field to the wildcard's bound
    // instantiation (Codec<Schema<?>>). Both types are recorded - the field's Signature and the
    // parameter's - and the cast erases to the class the value already has.
    boolean fieldBoundCast = false;
    VarType fieldBoundTarget = null;
    if (!castAlways && !doCast && !doCastGenerics && !castRaw && !doCastNull && !doCastNarrowing && !doubleCast
      && exprent instanceof FieldExprent
      && rightType instanceof GenericType fieldType && fieldType.getWildcard() == GenericType.WILDCARD_NO
      && fieldType.type == CodeType.OBJECT && fieldType.arrayDim == 0 && fieldType.getArguments().size() == 1
      && fieldType.getArguments().get(0) instanceof GenericType boundWildcard
      && boundWildcard.getWildcard() == GenericType.WILDCARD_EXTENDS && boundWildcard.value != null
      && unboundedClassParameters(fieldType.value)) {
      VarType bound = GenericType.withWildcard(boundWildcard, GenericType.WILDCARD_NO);
      VarType target = new GenericType(CodeType.OBJECT, 0, fieldType.value, null,
        Collections.singletonList(bound), GenericType.WILDCARD_NO);
      if (!invalidGenericInstantiation(target)) {
        fieldBoundTarget = target;
        fieldBoundCast = true;
      }
    }

    boolean cast = castAlways || doCast || doCastNull || doCastNarrowing || doCastGenerics || doubleCast
      || fieldBoundCast;

    if (castNull == NullCastType.DONT_CAST_AT_ALL && rightType.type == CodeType.NULL) {
      cast = castAlways;
    }

    // A class type variable cannot be named from a static method, so the original source cannot
    // have had this cast; drop it and let the expression's own type stand.
    boolean castLambda = !cast && exprent instanceof NewExprent && !leftType.equals(rightType) &&
                          lambdaNeedsCast(leftType, (NewExprent)exprent);

    boolean quote = cast && exprent.getPrecedence() >= FunctionType.CAST.precedence;

    // cast instead to 'byte' / 'short' when int constant is used as a value for 'Byte' / 'Short'
    if (castNarrowing && exprent instanceof ConstExprent && !((ConstExprent) exprent).isNull()) {
      if (leftType.equals(VarType.VARTYPE_BYTE_OBJ)) {
        leftType = VarType.VARTYPE_BYTE;
      }
      else if (leftType.equals(VarType.VARTYPE_SHORT_OBJ)) {
        leftType = VarType.VARTYPE_SHORT;
      }
    }

    if (cast) {
      VarType castType = fieldBoundCast ? fieldBoundTarget
        : doubleCast ? doubleCastTarget
        : castRaw ? new VarType(leftType.type, leftType.arrayDim, leftType.value) : leftType;
      buffer.append('(').appendCastTypeName(castType).append(')');
      if (doubleCast) {
        // The first step widens the value to the strictest type the second cast accepts: the
        // target class with its one argument as an upper bound (`Type<? extends Pair<?, ?>>`).
        // When the target itself is the wildcarded erasure (`Dynamic<?>`), no first step exists
        // and printing it again would only repeat the same cast.
        VarType inner = strictDoubleCastInner(doubleCastTarget);
        if (inner == null) {
          inner = erasedWildcardForm(doubleCastTarget);
        }
        if (!getCastTypeName(inner).equals(getCastTypeName(castType))) {
          buffer.append('(').appendCastTypeName(inner).append(')');
        }
      }
    }

    if (castLambda) {
      buffer.append('(').appendCastTypeName(rightType).append(')');
    }

    if (quote) {
      buffer.append('(');
    }

    if (exprent instanceof ConstExprent) {
      ((ConstExprent) exprent).adjustConstType(leftType);
    }

    if (cast) {
      // Don't cast vararg array creation! Force regular array creation instead
      if (exprent instanceof NewExprent && ((NewExprent)exprent).isVarArgParam()) {
        ((NewExprent) exprent).setVarArgParam(false);
      }
    }

    buffer.append(exprent.toJava(indent));

    if (quote) {
      buffer.append(')');
    }

    return cast;
  }

  public enum NullCastType {
    CAST(true), // old boolean true
    DONT_CAST(false), // old boolean false
    DONT_CAST_AT_ALL(false); // old boolean false and don't cast

    private final boolean cast;

    NullCastType(boolean cast) {
      this.cast = cast;
    }
  }

  /**
   * Whether a cast from {@code right} to {@code left} is one javac rejects: both are the same
   * generic class and some pair of arguments is provably distinct, so neither instantiation is a
   * subtype of the other and the conversion is not an unchecked one either. Only the invariant
   * case is judged; wildcard targets, raw values and type variables keep the existing rules.
   */
  private static boolean provablyInconvertible(VarType left, VarType right) {
    if (!(left instanceof GenericType target) || !(right instanceof GenericType value)) {
      return false;
    }
    if (target.getWildcard() != GenericType.WILDCARD_NO || value.getWildcard() != GenericType.WILDCARD_NO
      || target.arrayDim != 0 || value.arrayDim != 0 || !target.value.equals(value.value)) {
      return false;
    }
    List<VarType> targetArgs = target.getArguments();
    List<VarType> valueArgs = value.getArguments();
    if (targetArgs.size() != valueArgs.size() || target.equalsExact(value)) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      if (argumentProvablyDistinct(targetArgs.get(i), valueArgs.get(i))) {
        return true;
      }
    }
    return false;
  }

  /**
   * The strictest type a double cast's first step can widen to, or null when the target names no
   * argument. A single upper-bounded argument is the form that still accepts the target cast: the
   * value is castable to the target class with its argument as an upper bound, and that in turn to
   * the target itself.
   */
  private static VarType strictDoubleCastInner(VarType target) {
    if (!(target instanceof GenericType generic) || generic.getArguments().size() != 1
        || generic.getArguments().get(0) == null) {
      return null;
    }
    VarType bound = GenericType.withWildcard(generic.getArguments().get(0), GenericType.WILDCARD_EXTENDS);
    return new GenericType(CodeType.OBJECT, 0, target.value, null,
      java.util.Collections.singletonList(bound), GenericType.WILDCARD_NO);
  }

  /**
   * A declared type with every type variable wildcarded, or null when the type itself is one.
   *
   * <p>A method reference records its instantiated type erased, so a type variable the source
   * pinned is only recoverable from the referenced method's declaration. The wildcard is the one
   * nameable form of an argument no source spelled, and writing it back is byte-neutral.
   */
  public static VarType wildcardUnnameableType(VarType type) {
    boolean[] captured = new boolean[1];
    VarType value = wildcardUnnameableInView(type, java.util.Collections.emptyMap(), captured);
    return captured[0] ? value : null;
  }

  /**
   * Replaces every type variable not recorded at the call site with the unbounded wildcard,
   * reporting whether any was replaced: such a position is a capture, the value our inference
   * could not name.
   */
  private static VarType wildcardUnnameableInView(VarType type, Map<VarType, List<VarType>> named,
                                                  boolean[] captured) {
    if (type == null) {
      return null;
    }
    if (type.type == CodeType.GENVAR) {
      if (Exprent.isTypeVariableNameable(type.resizeArrayDim(0), named)) {
        return type;
      }
      captured[0] = true;
      return null;
    }
    if (!(type instanceof GenericType generic) || generic.getArguments().isEmpty()) {
      return type;
    }
    List<VarType> arguments = new ArrayList<>(generic.getArguments().size());
    boolean changed = false;
    for (VarType argument : generic.getArguments()) {
      if (argument == null) {
        arguments.add(null);
        continue;
      }
      VarType value = wildcardUnnameableInView(argument, named, captured);
      if (value != argument) {
        changed = true;
      }
      arguments.add(value);
    }
    if (!changed) {
      return type;
    }
    return new GenericType(type.type, type.arrayDim, type.value, generic.getParent(),
      Collections.unmodifiableList(arguments), generic.getWildcard());
  }

  /**
   * Whether a class's type parameters are all unbounded: a wildcard argument is a legal cast
   * argument there. A self-referential bound (Builder&lt;T extends Builder&lt;T&gt;&gt;) rejects
   * the wildcard, so its subtypes' casts must not be invented.
   */
  private static boolean unboundedClassParameters(String internalName) {
    StructClass cls = DecompilerContext.getStructContext().getClass(internalName);
    if (cls == null || cls.getSignature() == null) {
      return true;
    }
    for (List<VarType> bounds : cls.getSignature().fbounds) {
      if (bounds != null && !bounds.isEmpty() && !VarType.VARTYPE_OBJECT.equals(bounds.get(0))) {
        return false;
      }
    }
    return true;
  }

  /** The erased form of a parameterized instantiation: its class with unbounded wildcards. */
  private static VarType erasedWildcardForm(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return new VarType(type.type, type.arrayDim, type.value);
    }
    List<VarType> arguments = new ArrayList<>(generic.getArguments().size());
    for (int i = 0; i < generic.getArguments().size(); i++) {
      arguments.add(null);
    }
    return new GenericType(CodeType.OBJECT, type.arrayDim, type.value, null,
      Collections.unmodifiableList(arguments), GenericType.WILDCARD_NO);
  }

  /**
   * JLS 5.5.1 for the wildcard-capture shape: a cast to {@code X<Z>} from {@code X<? extends B<..>>}
   * is legal only when Z is contained by the wildcard's bound, i.e. Z is a subtype of B. A target
   * position that is itself a wildcard, or a type variable, is never provably distinct from the
   * value's wildcard and javac accepts the unchecked cast. Anything else is provably distinct and
   * javac rejects the cast; only the raw erasure compiles.
   */
  private static boolean parameterizedCastIllegal(VarType left, VarType right) {
    if (!(left instanceof GenericType target) || !(right instanceof GenericType value)
      || target.getWildcard() != GenericType.WILDCARD_NO || value.getWildcard() != GenericType.WILDCARD_NO
      || target.arrayDim != 0 || value.arrayDim != 0 || target.value == null || value.value == null
      || !target.value.equals(value.value)) {
      return false;
    }
    List<VarType> targetArgs = target.getArguments();
    List<VarType> valueArgs = value.getArguments();
    if (targetArgs.size() != valueArgs.size()) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      VarType targetArg = targetArgs.get(i);
      VarType valueArg = valueArgs.get(i);
      if (!(valueArg instanceof GenericType wildcard) || wildcard.getWildcard() != GenericType.WILDCARD_EXTENDS
        || !wildcard.isGeneric() || wildcard.getArguments().isEmpty() || wildcard.value == null) {
        continue;
      }
      // An unbounded `?` parses as null; like every wildcard target it is never provably distinct.
      if (targetArg == null || targetArg instanceof GenericType targetWildcard
        && targetWildcard.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      // A type variable is not provably distinct from a wildcard either.
      if (targetArg.type == CodeType.GENVAR) {
        continue;
      }
      // A concrete argument is contained by `? extends B` when it is a subtype of B: Integer is
      // legal under `? extends Number`, Object is not. A parameterized argument is contained only
      // when its own class is B's class; a parameterized proper subtype is rejected even though
      // its erasure is a subtype (the capture could have been a sibling subtype), and the source
      // that compiled wrote the raw erasure there. Only an uncontained argument forces the raw.
      if (targetArg.type != CodeType.OBJECT || targetArg.arrayDim != 0 || targetArg.value == null
        || !DecompilerContext.getStructContext().instanceOf(targetArg.value, wildcard.value)
        || targetArg.isGeneric() && !targetArg.value.equals(wildcard.value)) {
        return true;
      }
    }
    return false;
  }

  /** JLS 4.5 "provably distinct" for one position, limited to the shapes the printer produces. */
  private static boolean argumentProvablyDistinct(VarType target, VarType value) {
    if (target == null || value == null || target.type == CodeType.GENVAR || value.type == CodeType.GENVAR) {
      return false;
    }
    if (target instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    if (value instanceof GenericType wild && wild.getWildcard() != GenericType.WILDCARD_NO) {
      // A capture of ? extends B may only be cast to an instantiation below B; a supertype of
      // the bound (or an unrelated class) is provably distinct.
      if (wild.getWildcard() != GenericType.WILDCARD_EXTENDS || wild.value == null
        || target.isGeneric() || target.type != CodeType.OBJECT || target.value == null) {
        return false;
      }
      return !DecompilerContext.getStructContext().instanceOf(target.value, wild.value);
    }
    if (target.isGeneric() != value.isGeneric()) {
      return false;
    }
    if (target.isGeneric()) {
      return !((GenericType) target).equalsExact(value);
    }
    return target.type == CodeType.OBJECT && value.type == CodeType.OBJECT && !target.value.equals(value.value);
  }

  /** Whether a type argument names a generic class without its type arguments. */
  private static boolean hasRawTypeArgument(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument == null) {
        continue;
      }
      if (argument.type == CodeType.OBJECT && argument.arrayDim == 0 && !argument.isGeneric()
        && isGenericClass(argument.value)) {
        return true;
      }
      if (hasRawTypeArgument(argument)) {
        return true;
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

  /** Whether the type names a type variable the enclosing source declares, at any depth. */
  private static boolean hasInScopeTypeVariable(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return named.containsKey(type);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (hasInScopeTypeVariable(argument, named)) {
          return true;
        }
      }
    }
    return false;
  }

  /** Whether a method-reference argument's inferred SAM return is an unnameable type variable. */
  private static boolean captureReturnedArgument(Exprent exprent) {
    if (!(exprent instanceof InvocationExprent invocation)) {
      return false;
    }
    Map<VarType, List<VarType>> named = exprent.getNamedGenerics();
    for (Exprent argument : invocation.getLstParameters()) {
      if (argument instanceof NewExprent lambda && lambda.isLambda() && lambda.isMethodReference()) {
        VarType produced = lambda.getFunctionalReturnType();
        if (produced != null && produced.type == CodeType.GENVAR
          && (!(produced instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO)
          && !named.containsKey(produced)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Whether a type variable can be written where the cast is printed. A class's own variables are
   * not nameable from a static member, and a variable of an enclosing class is not either.
   */
  private static boolean nameableVariable(String name) {
    MethodWrapper method = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (method == null || method.methodStruct == null) {
      return false;
    }
    GenericMethodDescriptor signature = method.methodStruct.getSignature();
    if (signature != null && signature.typeParameters.contains(name)) {
      return true;
    }
    return !method.methodStruct.hasModifier(CodeConstants.ACC_STATIC);
  }

  /** Whether the value's erasure can be converted to the target's: the same class, a subtype, or Object. */
  private static boolean castableToErasure(Exprent exprent, VarType target) {
    VarType value = exprent.getExprType();
    if (value == null || target.type != CodeType.OBJECT || target.arrayDim != 0 || target.value == null
      || value.type != CodeType.OBJECT || value.arrayDim != 0 || value.value == null) {
      return false;
    }
    if (value.value.equals(target.value) || "java/lang/Object".equals(value.value)) {
      return true;
    }
    StructContext context = DecompilerContext.getStructContext();
    return context != null && context.instanceOf(value.value, target.value);
  }

  /**
   * Whether the type is an instantiation with a `? super T` argument naming a type variable that is
   * in scope where the cast would be printed. A variable of the enclosing class is not nameable
   * from a static member, and printing it would not compile.
   */
  private static boolean lowerBoundedWildcardTarget(VarType type) {
    if (!(type instanceof GenericType generic) || generic.value == null) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument instanceof GenericType wildcard && wildcard.getWildcard() == GenericType.WILDCARD_SUPER
        && wildcard.type == CodeType.GENVAR && nameableVariable(wildcard.value)) {
        return true;
      }
    }
    return false;
  }

  /** A concrete target instantiated from a wildcard declaration: assignable only through a cast. */
  private static boolean needsCaptureCast(VarType target, VarType declared) {
    if (!(target instanceof GenericType concrete) || !(declared instanceof GenericType wild)) {
      return false;
    }
    if (concrete.value == null || !concrete.value.equals(wild.value)) {
      return false;
    }
    return !hasWildcard(concrete) && hasWildcard(wild);
  }

  private static boolean hasWildcard(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return false;
    }
    if (generic.getWildcard() != GenericType.WILDCARD_NO) {
      return true;
    }
    for (VarType argument : generic.getArguments()) {
      // An unbound wildcard is a null argument.
      if (argument == null || hasWildcard(argument)) {
        return true;
      }
    }
    return false;
  }

  /** Whether some concrete type argument of a generic type is outside its formal bound. */
  private static boolean invalidGenericInstantiation(VarType type) {
    if (!(type instanceof GenericType generic) || generic.getArguments().isEmpty()) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    if (cls == null) {
      return false;
    }
    GenericClassDescriptor signature = cls.getSignature();
    if (signature == null) {
      return false;
    }
    List<VarType> arguments = generic.getArguments();
    for (int i = 0; i < arguments.size() && i < signature.fbounds.size(); i++) {
      VarType argument = arguments.get(i);
      if (argument == null || argument.type != CodeType.OBJECT || argument.value == null) {
        continue;
      }
      for (VarType bound : signature.fbounds.get(i)) {
        if (bound == null || bound.type != CodeType.OBJECT || bound.value == null) {
          continue;
        }
        if (bound.value.equals(argument.value)) {
          // T extends Comparable<T> cannot be instantiated with a wildcard: `Comparable<?>` is not
          // a type that satisfies its own bound.
          if (bound instanceof GenericType bounded && argument instanceof GenericType concrete
              && bounded.getArguments().stream().anyMatch(a -> a != null && a.type == CodeType.GENVAR)
              && concrete.getArguments().stream().anyMatch(a -> a == null || (a instanceof GenericType g
                  && g.getWildcard() != GenericType.WILDCARD_NO))) {
            return true;
          }
          continue;
        }
        if (!DecompilerContext.getStructContext().instanceOf(argument.value, bound.value)) {
          return true;
        }
      }
    }
    return false;
  }

  // (Obj)expr; -> (Obj<T>)expr;
  public static Exprent narrowGenericCastType(Exprent expr, VarType type) {
    if (type.isGeneric() && expr instanceof FunctionExprent && ((FunctionExprent)expr).getFuncType() == FunctionType.CAST) {
      FunctionExprent func = (FunctionExprent) expr;
      VarType funcType = func.getExprType();

      GenericType genType = (GenericType) type;
      if (funcType.value.equals(type.value) && !genType.getArguments().isEmpty()) {
        // Trying to cast to a generic type but the cast isn't generic- invalid!
        if (!funcType.isGeneric()) {
          // ...unless the type arguments cannot satisfy the bounds; the original's raw cast then
          // stays raw, which is also what javac needs.
          if (!invalidGenericInstantiation(type)) {
            ConstExprent cast = ((ConstExprent) func.getLstOperands().get(1));
            cast.setConstType(type);
          }
        } else if (genType.equalsExact(funcType) && !func.doesCast()) {
          func.setNeedsCast(true);
        }
      }
    }

    return expr;
  }

  // Checks if two generic types should cast based on their type parameters.
  // If both the left and the right types are generics, compare the type parameters based on a set of rules to see if
  // the types are compatible. If a matching rule is identified, return and inform the type processor that the types
  // should cast.
  private static boolean doGenericTypesCast(Exprent ex, VarType left, VarType right) {
    Map<VarType, List<VarType>> named = ex.getNamedGenerics();
    if (left == null || right == null) {
      return false;
    }
    // A lambda argument is typed by its target: javac infers its parameter and return types from
    // the functional interface, so a cast around it is not evidence of a source cast and, when the
    // call's own type argument was inferred from a sibling argument, names the wrong type.
    if (ex instanceof NewExprent lambda && lambda.isLambda()) {
      return false;
    }
    // A cast is a source form the original wrote to make a call typecheck. Casts to a type whose
    // *direct* type argument is a wildcard (EntityType<? extends Mob>) are real and needed. An
    // invented one instead carries the wildcard one level deeper (App<Mu<? extends X>, T>), where
    // javac's inference already handles the argument and the cast can name an out-of-scope variable.
    if (left instanceof GenericType generic && generic.getWildcard() == GenericType.WILDCARD_NO
      && hasDeepWildcard(generic)) {
      return false;
    }

    if (left.isGeneric() && right.isGeneric()) {
      boolean contextFixed = contextIndependentValue(ex);
      if (shouldGenericTypesCast(named, left, right, contextFixed)) {
        return true;
      }

      GenericType leftGeneric = (GenericType) left;
      GenericType rightGeneric = (GenericType) right;

      if (leftGeneric.getArguments().size() != rightGeneric.getArguments().size()) {
        return false;
      }

      for (int i = 0; i < leftGeneric.getArguments().size(); i++) {
        VarType leftType = leftGeneric.getArguments().get(i);
        VarType rightType = rightGeneric.getArguments().get(i);
        if (rightType == null && leftType != null) {
          return true;
        }

        if (leftType != null) {
          if (shouldGenericTypesCast(named, leftType, rightType, contextFixed)) {
            return true;
          }
        }
      }
    }

    return plainClassToInvariantGeneric(left, right);
  }

  /** True when a wildcard sits below the type's direct arguments, not in them. */
  private static boolean hasDeepWildcard(GenericType type) {
    for (VarType argument : type.getArguments()) {
      if (!(argument instanceof GenericType generic)
        || generic.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      if (containsWildcard(generic)) {
        return true;
      }
    }
    return false;
  }

  private static boolean containsWildcard(GenericType type) {
    if (type.getWildcard() != GenericType.WILDCARD_NO) {
      return true;
    }
    for (VarType argument : type.getArguments()) {
      if (argument instanceof GenericType generic && containsWildcard(generic)) {
        return true;
      }
    }
    return false;
  }

  /**
   * A plain class assigned to a generic type: its supertype instantiation is recorded in its own
   * class file, and {@code class C implements Owner<Object>} is not an {@code Owner<T>} for an
   * unknown T, so the source made the assignment compile with a cast.
   */
  private static boolean plainClassToInvariantGeneric(VarType left, VarType right) {
    if (left == null || right == null || !left.isGeneric() || right.isGeneric()
      || right.type != CodeType.OBJECT) {
      return false;
    }
    VarType view = GenericType.getGenericSuperType(right, left);
    if (!(view instanceof GenericType genView) || !left.value.equals(genView.value)) {
      return false;
    }
    List<VarType> targetArgs = ((GenericType) left).getArguments();
    List<VarType> actualArgs = genView.getArguments();
    if (targetArgs.size() != actualArgs.size()) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      VarType targetArg = targetArgs.get(i);
      VarType actualArg = actualArgs.get(i);
      if (targetArg == null || actualArg == null) {
        continue;
      }
      if (targetArg instanceof GenericType genericArg && genericArg.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      if (targetArg.type == CodeType.GENVAR && actualArg.type != CodeType.GENVAR && !targetArg.equals(actualArg)) {
        return true;
      }
    }
    return false;
  }

  /** A type variable with no wildcard of its own (the variable itself, not {@code ? extends T}). */
  private static boolean plainTypeVariable(VarType type) {
    return type != null && type.type == CodeType.GENVAR
      && (!(type instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO);
  }

  /** An unbounded wildcard is a null argument; a bounded one carries its own wildcard type. */
  private static boolean isWildcardArgument(VarType type) {
    return type == null || (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO);
  }

  /**
   * A value whose type does not depend on the context it is printed in. A cast around a generic
   * call or a diamond is itself the context for its inference, so the source could not have
   * written one there: the call would have been inferred without the target and produced the
   * type the printer already sees. Only a variable, field, constant, or a conditional of them
   * is fixed by the class file alone.
   */
  private static boolean contextIndependentValue(Exprent exprent) {
    if (exprent instanceof VarExprent || exprent instanceof FieldExprent || exprent instanceof ConstExprent) {
      return true;
    }
    if (exprent instanceof FunctionExprent function && function.getFuncType() == FunctionType.TERNARY) {
      List<Exprent> operands = function.getLstOperands();
      return operands.size() == 3 && contextIndependentValue(operands.get(1)) && contextIndependentValue(operands.get(2));
    }
    return false;
  }

  /**
   * Whether the target type names a type variable where the value's recorded type carries a
   * wildcard in the same invariant position. The variable must be in scope at the point of
   * printing, otherwise the cast would be illegal; a wildcard on the target side is fine
   * (X&lt;T&gt; is an X&lt;?&gt;), so only the target-variable/value-wildcard direction counts.
   */
  private static boolean invariantWildcardTarget(Map<VarType, List<VarType>> named, VarType left, VarType right) {
    if (left == null || right == null || !left.isGeneric() || !right.isGeneric()
      || !left.value.equals(right.value) || left.type != CodeType.OBJECT) {
      return false;
    }
    GenericType leftGeneric = (GenericType) left;
    GenericType rightGeneric = (GenericType) right;
    if (leftGeneric.getWildcard() != GenericType.WILDCARD_NO
      || rightGeneric.getWildcard() != GenericType.WILDCARD_NO
      || leftGeneric.getArguments().size() != rightGeneric.getArguments().size()) {
      return false;
    }
    for (int i = 0; i < leftGeneric.getArguments().size(); i++) {
      VarType targetArg = leftGeneric.getArguments().get(i);
      VarType valueArg = rightGeneric.getArguments().get(i);
      if (targetArg != null && targetArg.type == CodeType.GENVAR && named.containsKey(targetArg)
        && isWildcardArgument(valueArg)) {
        return true;
      }
      if (targetArg != null && valueArg != null && invariantWildcardTarget(named, targetArg, valueArg)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the value's recorded generic instantiation is a subclass of the target's generic class
   * whose recorded class signature, instantiated with the value's own arguments, puts a wildcard
   * where the target has a type variable in scope. Both sides are then different instantiations of
   * the same generic supertype in an invariant position, so no assignment converts one to the
   * other and a source that compiled cast the value to the target.
   */
  private static boolean wildcardSubtypeTarget(Map<VarType, List<VarType>> named, VarType left, VarType right) {
    if (left == null || right == null || !left.isGeneric() || !right.isGeneric()
      || left.value == null || right.value == null || left.value.equals(right.value)
      || left.arrayDim != 0 || right.arrayDim != 0) {
      return false;
    }
    if (((GenericType) left).getWildcard() != GenericType.WILDCARD_NO
      || ((GenericType) right).getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    StructClass derivedClass = DecompilerContext.getStructContext().getClass(right.value);
    StructClass targetClass = DecompilerContext.getStructContext().getClass(left.value);
    if (derivedClass == null || targetClass == null
      || derivedClass.getSignature() == null || targetClass.getSignature() == null) {
      return false;
    }
    // For each type parameter of the target class, the deriving class's own type parameter the
    // recorded hierarchy binds it to.
    Map<VarType, VarType> superMap = derivedClass.getAllGenerics().get(targetClass.qualifiedName);
    if (superMap == null) {
      return false;
    }
    List<String> targetParameters = targetClass.getSignature().fparameters;
    List<VarType> targetArguments = ((GenericType) left).getArguments();
    if (targetParameters.size() != targetArguments.size()) {
      return false;
    }
    // The value's instantiation of the deriving class's type parameters: an unbounded wildcard
    // argument is recorded as null, so the map can carry null values.
    Map<VarType, VarType> actual = new HashMap<>();
    derivedClass.getSignature().genericType.mapGenVarsTo((GenericType) right, actual);
    for (int i = 0; i < targetArguments.size(); i++) {
      VarType targetArgument = targetArguments.get(i);
      if (!plainTypeVariable(targetArgument) || !named.containsKey(targetArgument)) {
        continue;
      }
      VarType derivedVariable = superMap.get(GenericType.parse("T" + targetParameters.get(i) + ";"));
      if (derivedVariable == null || derivedVariable.type != CodeType.GENVAR || !actual.containsKey(derivedVariable)) {
        continue;
      }
      VarType derived = actual.get(derivedVariable);
      // A wildcard, or a different type variable of the enclosing source, in an invariant
      // position: neither is literally the target's variable, so the value does not assign and
      // the source cast it (Constant<I> returned as CubicSpline<R>).
      if (isWildcardArgument(derived)
        || plainTypeVariable(derived) && named.containsKey(derived) && !derived.equals(targetArgument)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the target type is an array whose element is a type variable of the enclosing source
   * while the value's array type is a different one. Arrays are covariant only over reifiable
   * element types, and no array whose element is not that same variable is a subtype of
   * {@code S[]}, so a source that compiled had to cast; the call's recorded signature (a field or
   * method signature, possibly on another class) proves the target is {@code S[]}. Only a value
   * whose erased array type is exactly {@code Object[]} is judged: the cast then erases to the
   * variable's unbounded erasure, so javac emits no checkcast for it.
   */
  private static boolean typeVariableArrayTarget(Map<VarType, List<VarType>> named, VarType left, VarType right) {
    if (left == null || right == null || left.arrayDim == 0 || left.arrayDim != right.arrayDim) {
      return false;
    }
    VarType leftBase = left.resizeArrayDim(0);
    VarType rightBase = right.resizeArrayDim(0);
    return leftBase.type == CodeType.GENVAR
      && named.containsKey(leftBase)
      && !leftBase.equals(rightBase)
      && rightBase.equals(VarType.VARTYPE_OBJECT);
  }

  private static boolean shouldGenericTypesCast(Map<VarType, List<VarType>> named, VarType leftType, VarType rightType,
                                                boolean contextFixed) {
    if (leftType.isGeneric()) {
      GenericType genLeft = (GenericType) leftType;
      if (rightType.isGeneric()) {
        GenericType genRight = (GenericType) rightType;

        if (leftType.higherEqualInLatticeThan(rightType)) {
          // Casting Clazz<?> to Clazz<T> or Clazz<Concrete>
          if ((genLeft.getWildcard() == GenericType.WILDCARD_NO || genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS) &&
            genRight.getWildcard() == GenericType.WILDCARD_SUPER) {

            boolean ok = true;
            if (genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS) {
              // Equals, ignoring wildcards
              if (!genLeft.getArguments().isEmpty() && !genRight.getArguments().isEmpty() &&
                leftType.equals(rightType)) {
                ok = false;
              }
            }

            if (ok) {
              return true;
            }
          }
        } else {
          if (genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS && genRight.getWildcard() == GenericType.WILDCARD_SUPER) {
            return true;
          }
          // Trying to cast two independent generics to each other? Check if they're both the base generic type (i.e. Object)
          // and force a cast if so.
          if (leftType.type == CodeType.GENVAR && rightType.type == CodeType.GENVAR
            && genLeft.getWildcard() == GenericType.WILDCARD_NO && genLeft.getWildcard() == GenericType.WILDCARD_NO) {

            if (named.containsKey(leftType) && named.containsKey(rightType) && named.get(leftType).contains(VarType.VARTYPE_OBJECT) && named.get(rightType).contains(VarType.VARTYPE_OBJECT)) {
              return true;
            }
          }
        }

        if ((genLeft.getWildcard() == GenericType.WILDCARD_NO || genLeft.getWildcard() == GenericType.WILDCARD_SUPER) &&
          genRight.getWildcard() == GenericType.WILDCARD_EXTENDS) {
          return true;
        }

        // Recurse on the type
        // Notably, *only* recurse if the current wildcard types are the same- otherwise we may run into incorrect casting behavior
        if (genLeft.getArguments().size() != genRight.getArguments().size()) {
          return false;
        }

        if (genLeft.getWildcard() == genRight.getWildcard()) {
          // Arguments of the same generic class are invariant positions: two instantiations are
          // the same type only when each argument is literally the same. A type variable on one
          // side and a different type on the other therefore never assigns across, and the source
          // made it compile with a cast.
          boolean invariant = leftType.value.equals(rightType.value);
          for (int i = 0; i < genLeft.getArguments().size(); i++) {
            VarType lt = genLeft.getArguments().get(i);
            VarType rt = genRight.getArguments().get(i);
            // Subset of Type<?> -> Type<T> check: Only check for genvars. If T is concrete, then don't force casting.
            if (rt == null && lt != null && lt.type == CodeType.GENVAR) {
              return true;
            }
            if (invariant && lt != null && rt != null
              && ((lt.type == CodeType.GENVAR && rt.type != CodeType.GENVAR && !rt.isGeneric())
                || (rt.type == CodeType.GENVAR && lt.type != CodeType.GENVAR && !lt.isGeneric()))) {
              return true;
            }
            // Two different type variables are different types even when one is a subtype of the
            // other: invariance never assigns X<A> to X<B>, so a source that did it cast, and the
            // target's variable must be nameable where the cast is printed. Only a value whose type
            // the class file fixes without context is cast; an argument list or a method reference
            // is inferred from the cast itself, so the source need not have written one. A bounded
            // wildcard of a variable (? extends B) is not the variable itself - Class<T> does
            // assign to Class<? extends B> - so both arguments must be plain variables.
            if (invariant && contextFixed && plainTypeVariable(lt) && plainTypeVariable(rt)
              && !lt.equals(rt) && named.containsKey(lt)) {
              return true;
            }

            if (lt != null && rt != null) {
              if (shouldGenericTypesCast(named, lt, rt, contextFixed)) {
                return true;
              }
            }
          }
        }
      } else {
        // Right is not generic
        // Check for casting a concrete rightType to a specific left generic
        // e.g. (List<T>)list where 'list' is List<Object>
        if (genLeft.getWildcard() == GenericType.WILDCARD_NO && genLeft.getArguments().isEmpty()) {
          return true;
        }
      }
    }

    return false;
  }

  private static boolean isIntConstant(Exprent exprent) {
    if (exprent instanceof ConstExprent) {
      switch (((ConstExprent)exprent).getConstType().type) {
        case BYTE:
        case BYTECHAR:
        case SHORT:
        case SHORTCHAR:
        case INT:
          return true;
      }
    }

    return false;
  }

  private static boolean isNarrowedIntType(VarType type) {
    return VarType.VARTYPE_INT.higherInLatticeThan(type) ||
           type.equals(VarType.VARTYPE_BYTE_OBJ) || type.equals(VarType.VARTYPE_SHORT_OBJ);
  }

  private static boolean lambdaNeedsCast(VarType left, NewExprent exprent) {
    if (!exprent.isLambda() && !exprent.isMethodReference()) {
      return false;
    }
    // The invokedynamic names the interface javac built the lambda for, and it comes from the
    // target itself: when it is not the expected type, the source must have cast to it, or javac
    // would have built the lambda for the expected type instead.
    return RoundTrip.selector("lambdacast");
  }

  /** The single abstract method that makes {@code cls} a functional interface, or null. */
  public static StructMethod functionalMethod(StructClass cls) {
    if (!cls.hasModifier(CodeConstants.ACC_INTERFACE)) {
      return null;
    }
    StructMethod found = null;
    for (StructMethod method : cls.getMethods()) {
      if (!method.hasModifier(CodeConstants.ACC_ABSTRACT) || method.hasModifier(CodeConstants.ACC_STATIC)) {
        continue;
      }
      // Redeclaring an Object method is not an abstract method for functional-interface purposes.
      String name = method.getName();
      String desc = method.getDescriptor();
      if ((name.equals("equals") && desc.equals("(Ljava/lang/Object;)Z"))
          || (name.equals("hashCode") && desc.equals("()I"))
          || (name.equals("toString") && desc.equals("()Ljava/lang/String;"))) {
        continue;
      }
      if (found != null) {
        return null;
      }
      found = method;
    }
    return found;
  }

  private static boolean isFunctionalInterface(StructClass cls) {
    return functionalMethod(cls) != null;
  }
}

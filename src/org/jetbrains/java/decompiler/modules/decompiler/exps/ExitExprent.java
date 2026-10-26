// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.struct.attr.StructExceptionsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.struct.match.MatchNode;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.BitSet;
import java.util.List;

public class ExitExprent extends Exprent {
  /** The functional method's return type while a lambda body's returns are printed. */
  private static final ThreadLocal<VarType> LAMBDA_RETURN_TARGET = new ThreadLocal<>();

  public static void enterLambdaReturn(VarType target) {
    LAMBDA_RETURN_TARGET.set(target);
  }

  public static void exitLambdaReturn() {
    LAMBDA_RETURN_TARGET.remove();
  }

  /** Removes and returns the functional return target while a nested class body prints. */
  public static VarType takeLambdaReturn() {
    VarType target = LAMBDA_RETURN_TARGET.get();
    LAMBDA_RETURN_TARGET.remove();
    return target;
  }

  public static void restoreLambdaReturn(VarType target) {
    if (target != null) {
      LAMBDA_RETURN_TARGET.set(target);
    }
  }

  public enum Type {
    RETURN, THROW
  }

  private final Type exitType;
  private Exprent value;
  private final VarType retType;
  private final MethodDescriptor methodDescriptor;

  public ExitExprent(Type exitType, Exprent value, VarType retType, BitSet bytecodeOffsets, MethodDescriptor methodDescriptor) {
    super(Exprent.Type.EXIT);
    this.exitType = exitType;
    this.value = value;
    this.retType = retType;
    this.methodDescriptor = methodDescriptor;

    addBytecodeOffsets(bytecodeOffsets);

    ValidationHelper.validateExitExprent(this);
  }

  @Override
  public Exprent copy() {
    return new ExitExprent(exitType, value == null ? null : value.copy(), retType, bytecode, methodDescriptor);
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    if (exitType == Type.RETURN && retType.type != CodeType.VOID) {
      result.addExprLowerBound(value, VarType.findFamilyBottom(retType.typeFamily));
      result.addExprUpperBound(value, retType);
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    if (value != null) {
      lst.add(value);
    }
    return lst;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();
    buf.addBytecodeMapping(bytecode);

    if (exitType == Type.RETURN) {
      if (value == null && retType.type == CodeType.VOID && RoundTrip.printsAsBreak(this)) {
        // The target jumped here from inside the loop: the source wrote `break;`, not `return;`.
        buf.append("break");
        return buf;
      }
      if (value == null && retType.type == CodeType.VOID) {
        // The jump leaves an outer loop, out of reach of an unlabelled break: the source named it.
        String label = RoundTrip.labelledBreakLabel(this);
        if (label != null) {
          buf.append("break ").append(label);
          return buf;
        }
      }
      buf.append("return");

      if (retType.type != CodeType.VOID) {
        VarType ret = retType;
        if (methodDescriptor != null && methodDescriptor.genericInfo != null && methodDescriptor.genericInfo.returnType != null) {
          ret = methodDescriptor.genericInfo.returnType;
        }
        VarType lambdaReturn = LAMBDA_RETURN_TARGET.get();
        if (lambdaReturn != null && value instanceof InvocationExprent) {
          // A call returned from a lambda body is checked against the functional method's
          // return type; the synthetic method's own signature is erased. Other values keep
          // their own cast decisions, which the target would wrongly relax.
          ret = lambdaReturn;
          InvocationExprent.enterLambdaBody(value);
          try {
            value.getInferredExprType(lambdaReturn);
          } finally {
            InvocationExprent.exitLambdaBody();
          }
        }
        // The return instruction carries the line of the `return` keyword; the value's first
        // instruction carries the line the expression starts on. When the source broke the line
        // right after the keyword, the expression is recorded one line later.
        int valueLine = firstValueLine(value);
        int returnLine = RoundTrip.sourceLine(this);
        if (valueLine >= 0 && returnLine >= 0 && valueLine > returnLine) {
          buf.appendLineSeparator().appendIndent(indent + 1);
        } else {
          buf.append(' ');
        }

        ExprProcessor.getCastedExprent(value, ret, buf, indent, ExprProcessor.NullCastType.DONT_CAST_AT_ALL, false, false, false);
      }

      return buf;
    }
    else {
      MethodWrapper method = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
      ClassNode node = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);

      if (method != null && node != null) {
        StructExceptionsAttribute attr = method.methodStruct.getAttribute(StructGeneralAttribute.ATTRIBUTE_EXCEPTIONS);

        if (attr != null) {
          String classname = null;

          for (int i = 0; i < attr.getThrowsExceptions().size(); i++) {
            String exClassName = attr.getExcClassname(i, node.classStruct.getPool());
            if ("java/lang/Throwable".equals(exClassName)) {
              classname = exClassName;
              break;
            }
            else if ("java/lang/Exception".equals(exClassName)) {
              classname = exClassName;
            }
          }

          if (classname != null) {
            VarType exType = new VarType(classname, true);
            buf.append("throw ");
            ExprProcessor.getCastedExprent(value, exType, buf, indent, false);
            return buf;
          }
        }
      }

      return buf.append(value.toJava(indent)).prepend("throw ");
    }
  }

  /**
   * The line the returned expression starts on: the line of its earliest instruction, when the
   * expression's lines rise from there. A pattern's {@code instanceof} records its subject on the
   * last line of the pattern and its binding on an earlier one, so a non-monotonic map cannot say
   * where the source started the expression and is left alone.
   */
  private static int firstValueLine(Exprent value) {
    if (value == null) {
      return -1;
    }
    int minOffset = -1;
    int firstLine = -1;
    int minLine = -1;
    for (Exprent part : value.getAllExprents(true, true)) {
      if (part.bytecode == null || part.bytecode.isEmpty()) {
        continue;
      }
      int offset = part.bytecode.nextSetBit(0);
      int line = RoundTrip.lineAtOffset(offset);
      if (minOffset < 0 || offset < minOffset) {
        minOffset = offset;
        firstLine = line;
      }
      if (line >= 0 && (minLine < 0 || line < minLine)) {
        minLine = line;
      }
    }
    return firstLine >= 0 && firstLine == minLine ? firstLine : -1;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == value) {
      value = newExpr;
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof ExitExprent)) return false;

    ExitExprent et = (ExitExprent)o;
    return exitType == et.getExitType() &&
           InterpreterUtil.equalObjects(value, et.getValue());
  }

  public Type getExitType() {
    return exitType;
  }

  public Exprent getValue() {
    return value;
  }

  public VarType getRetType() {
    return retType;
  }

  public MethodDescriptor getMethodDescriptor() {
    return this.methodDescriptor;
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, value);
    measureBytecode(values);
  }

  
  // *****************************************************************************
  // IMatchable implementation
  // *****************************************************************************

  @Override
  public boolean match(MatchNode matchNode, MatchEngine engine) {
    if (!super.match(matchNode, engine)) {
      return false;
    }

    Type type = (Type)matchNode.getRuleValue(MatchProperties.EXPRENT_EXITTYPE);
    return type == null || this.exitType == type;
  }
}
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructRecordComponent;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

public class PatternExprent extends Exprent implements Pattern {
  private final PatternData data;
  private final VarType varType;
  private final List<Exprent> exprents;
  private final List<@Nullable VarType> boundTypes;

  public PatternExprent(PatternData data, VarType type, List<Exprent> exprents) {
    super(Type.PATTERN);
    this.data = data;
    this.varType = type;
    this.exprents = exprents;
    this.boundTypes = new ArrayList<>();

    for (Exprent exprent : exprents) {
      if (!(exprent instanceof Pattern)) {
        ValidationHelper.assertTrue(false, "Illegal input for PatternExprent");
      }
      boundTypes.add(null);
    }
  }

  @Override
  protected List<Exprent> getAllExprents(List<Exprent> list) {
    list.addAll(exprents);
    return list;
  }

  @Override
  public VarType getExprType() {
    return varType;
  }

  @Override
  public Exprent copy() {
    return new PatternExprent(data, varType, DecHelper.copyExprentList(exprents));
  }

  @Override
  public TextBuffer toJava(int indent) {
    return toJava(indent, null);
  }

  /**
   * Prints the deconstruction. With the arm the pattern matches, a component the target never
   * binds prints as the unnamed pattern {@code Type _}: javac writes no local row for a component
   * the source left unnamed and the arm's code never reads it.
   */
  public TextBuffer toJava(int indent, Statement arm) {
    TextBuffer buf = new TextBuffer();
    buf.appendCastTypeName(varType);
    buf.append("(");

    for (int i = 0; i < exprents.size(); i++) {
      appendComponent(buf, indent, exprents.get(i), arm);

      if (i < exprents.size() - 1) {
        buf.append(", ");
      }
    }

    buf.append(")");

    return buf;
  }

  private static void appendComponent(TextBuffer buf, int indent, Exprent component, Statement arm) {
    if (arm != null && component instanceof VarExprent var && RoundTrip.unnamedPatternVariable(arm, var)) {
      String type = var.getDefinitionType();
      // A type the target does not record, or a generic one, stays in its ordinary form: an
      // erased name here would print a type the class file never wrote.
      if (!type.equals("var") && type.indexOf('<') < 0) {
        buf.append(type).append(" _");
        return;
      }
    }
    if (arm != null && component instanceof PatternExprent nested) {
      buf.append(nested.toJava(indent, arm));
      return;
    }
    buf.append(component.toJava());
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    if (this.data instanceof PatternData.RecordPatternData record) {
      CheckTypesResult res = new CheckTypesResult();

      ValidationHelper.assertTrue(record.cl.getRecordComponents() != null, "Must not be null!");
      ValidationHelper.assertTrue(record.cl.getRecordComponents().size() == exprents.size(), "Record component size and expr list size must be equal!");

      // The type lower bound must be at least the type of the record. However, we might have found a stronger lower bound, use that instead in that case.
      for (int i = 0; i < exprents.size(); i++) {
        VarType type = boundTypes.get(i);
        if (type != null) {
          res.addExprLowerBound(exprents.get(i), type);
        } else {
          res.addExprLowerBound(exprents.get(i), new VarType(record.cl.getRecordComponents().get(i).getDescriptor()));
        }
      }

      return res;
    }

    return super.checkExprTypeBounds();
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, exprents);
    measureBytecode(values);
  }

  @Override
  @NotNull
  public List<VarExprent> getPatternVars() {
    List<VarExprent> vars = new ArrayList<>();

    for (Exprent e : exprents) {
      if (e instanceof Pattern p) {
        vars.addAll(p.getPatternVars());
      } else {
        ValidationHelper.assertTrue(false, "Illegal input in PatternExprent");
      }
    }

    return vars;
  }

  public PatternData getData() {
    return data;
  }

  public List<Exprent> getExprents() {
    return exprents;
  }

  public List<@Nullable VarType> getBoundTypes() {
    return boundTypes;
  }

  public static PatternData recordData(StructClass cl) {
    return new PatternData.RecordPatternData(cl);
  }

  public sealed interface PatternData {
    record RecordPatternData(StructClass cl) implements PatternData {

    }
  }
}

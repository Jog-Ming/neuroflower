package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.*;

public class SwitchExprent extends Exprent {
  private final SwitchStatement backing;
  private VarType type;
  // TODO: is needed?
  private final boolean fallthrough;
  // Whether the switch expression returns a value, for case type coercion
  private final boolean standalone;
  /**
   * The type the enclosing context expects from this value, set by the printer just before
   * {@link #toJava}. A switch expression is poly there, so an arm that cannot satisfy the
   * target's type arguments must carry the cast the source wrote.
   */
  private VarType printTarget;

  public SwitchExprent(SwitchStatement backing, VarType type, boolean fallthrough, boolean standalone) {
    super(Type.SWITCH);
    this.backing = backing;
    this.type = type;
    this.fallthrough = fallthrough;
    this.standalone = standalone;
  }

  @Override
  public TextBuffer toJava(int indent) {
    // Validity checks
    if (!this.backing.isPhantom()) {
      throw new IllegalStateException("Switch expression backing statement isn't phantom!");
    }

    TextBuffer buf = new TextBuffer();
    VarType target = this.printTarget;
    this.printTarget = null;

    VarType switchType = this.backing.getHeadexprent().getExprType();
    boolean isExhaustive = isExhaustive();

    buf.append(this.backing.getHeadexprent().toJava(indent)).append(" {").appendLineSeparator();
    List<Integer> order = armOrder();
    for (int i : order) {
      Statement stat = this.backing.getCaseStatements().get(i);
      // javac rebuilds an exhaustive switch's MatchException arm from the case list.
      if (RoundTrip.synthesizedMatchThrow(stat)) {
        continue;
      }
      List<StatEdge> edges = this.backing.getCaseEdges().get(i);
      List<Exprent> values = this.backing.getCaseValues().get(i);
      Exprent guard = this.backing.getCaseGuards().size() > i ? this.backing.getCaseGuards().get(i) : null;

      boolean hasDefault = false;
      // As switch expressions can be compiled to a tableswitch, any gaps will contain a jump to the default element.
      // Switch expressions cannot have a case point to the same statement as the default, so we check for default first and don't check for cases if it exists [TestConstructorSwitchExpression1]

      for (StatEdge edge : edges) {
        if (edge == this.backing.getDefaultEdge()) {
          if (isExhaustive) {
            if (isSyntheticThrowEdge(edge)) {
              break; // just don't mark as default
            }
          }
          hasDefault = true;
          break;
        }
      }

      boolean hasEdge = false;
      for (int j = 0; j < edges.size(); j++) {
        Exprent value = edges.get(j) == backing.getDefaultEdge() && values.size() <= j
          ? new ConstExprent(VarType.VARTYPE_NULL, null, null) // a total branch in j17 would act as a null branch too
          : values.get(j);
        if (value == null) { // TODO: how can this be null? Is it trying to inject a synthetic case value in switch-on-string processing? [TestSwitchDefaultBefore]
          continue;
        }

        // only a null label changes `default` label semantics
        if (hasDefault && (value.getExprType() != VarType.VARTYPE_NULL)) {
          continue;
        }

        if (!hasEdge) {
          buf.appendIndent(indent + 1).append("case ");
        } else {
          buf.append(", ");
        }

        if (value instanceof ConstExprent && !standalone && !Objects.equals(value.getExprType(), VarType.VARTYPE_NULL)) {
          value = value.copy();
          ((ConstExprent) value).setConstType(switchType);
        }

        if (value instanceof FieldExprent field && field.isStatic() && (!this.backing.getTopParent().mt.getBytecodeVersion().hasSwitchPatternMatch() || switchType.equals(field.getExprType()))) { // enum values
          buf.appendField(field.getName(), false, field.getClassname(), field.getName(), field.getDescriptor());
        } else if (value instanceof FieldExprent field) {
          buf.append(field.toJava(indent, false));
        } else if (value instanceof FunctionExprent && ((FunctionExprent) value).getFuncType() == FunctionExprent.FunctionType.INSTANCEOF) {
          // Pattern matching variables

          Pattern pattern = (Pattern) value.getAllExprents().get(2);
          for (VarExprent var : pattern.getPatternVars()) {
            var.setWritingPattern();
          }

          buf.append(value.getAllExprents().get(2).toJava(indent));
        } else {
          buf.append(value.toJava(indent));
        }

        hasEdge = true;
      }

      if (guard != null) {
        buf.append(" when ").append(guard.toJava());
      }

      if (hasDefault) {
        if (!hasEdge) {
          // Don't write 'default -> {}'
          if (stat instanceof BasicBlockStatement && isEmptyDefault(((BasicBlockStatement)stat), backing)) {
            continue;
          }

          buf.appendIndent(indent + 1).append("default");
        } else {
          buf.append(", default");
        }
        hasEdge = true;
      }

      if (!hasEdge) { // if we're the synthetic throw edge, we have no cases
        continue;
      }

      buf.append(" -> ");

      boolean simple = stat instanceof BasicBlockStatement;

      if (stat.getExprents() != null && stat.getExprents().size() != 1) {
        simple = false;
      }

      // Single yield or throw
      if (simple) {
        Exprent exprent = stat.getExprents().get(0);

        if (exprent instanceof YieldExprent) {
          Exprent content = bareArmValue(((YieldExprent) exprent).getContent(), target);

          if (content instanceof ConstExprent && !Objects.equals(content.getExprType(), VarType.VARTYPE_NULL)) {
            ((ConstExprent)content).setConstType(this.type);
          }

          if (armNeedsTargetCast(content, target)) {
            buf.append('(').appendCastTypeName(target).append(')');
            if (content.getPrecedence() >= FunctionType.CAST.precedence) {
              buf.append('(').append(content.toJava(indent + 1)).append(')');
            } else {
              buf.append(content.toJava(indent + 1));
            }
            buf.append(';');
          } else {
            buf.append(content.toJava(indent + 1).append(";"));
          }
        } else if (exprent instanceof ExitExprent) {
          ExitExprent exit = (ExitExprent) exprent;

          if (exit.getExitType() == ExitExprent.Type.THROW) {
            buf.append(exit.toJava(indent + 1).append(";"));
          } else {
            throw new IllegalStateException("Can't have return in switch expression");
          }
        } else { // Catchall
          buf.append(exprent.toJava(indent + 1).append(";"));
        }
      } else {
        buf.append("{");
        buf.appendLineSeparator();
        TextBuffer statBuf = stat.toJava(indent + 2);
        buf.append(statBuf);
        buf.appendIndent(indent + 1).append("}");
      }

      buf.appendLineSeparator();
    }

    buf.appendIndent(indent).append("}");

    return buf;
  }

  /**
   * Javac lays arrow arms out in source order, so the arm whose code starts first was written first.
   * Vineflower appends default to the cases; put it back where the target laid out its block.
   * Pattern arms keep their order: moving them past one another changes which pattern dominates.
   */
  private List<Integer> armOrder() {
    int count = this.backing.getCaseStatements().size();
    List<Integer> order = new ArrayList<>(count);
    for (int i = 0; i < count; i++) {
      order.add(i);
    }
    if (!RoundTrip.selector("switchorder") || count < 2) {
      return order;
    }

    int defaultIndex = -1;
    int[] offset = new int[count];
    for (int i = 0; i < count; i++) {
      offset[i] = RoundTrip.firstOffset(this.backing.getCaseStatements().get(i));
      if (offset[i] < 0) {
        return order;
      }
      List<StatEdge> edges = this.backing.getCaseEdges().get(i);
      List<Exprent> values = this.backing.getCaseValues().get(i);
      // A default block is the target of every key with no source label, so its edge list holds
      // one edge per such key (and the printer skips those values). That is still the default's
      // own block, and its offset orders it among the arms.
      if (edges.contains(this.backing.getDefaultEdge())) {
        if (defaultIndex >= 0) {
          return order; // two defaults: leave it alone
        }
        defaultIndex = i;
        continue;
      }
      for (int j = 0; j < edges.size(); j++) {
        if (j >= values.size() || !(values.get(j) instanceof ConstExprent) && !(values.get(j) instanceof FieldExprent)) {
          return order; // patterns and other labels have ordering rules of their own
        }
      }
      if (this.backing.getCaseGuards().size() > i && this.backing.getCaseGuards().get(i) != null) {
        return order;
      }
    }
    // Javac emits every arm's code in source order, the default included; the case table is
    // what reorders the labels, not the blocks. Sorting by the arm's first instruction
    // restores the source's arm order.
    order.sort((a, b) -> Integer.compare(offset[a], offset[b]));
    return order;
  }

  /** The type the enclosing context expects from this value; consumed by the next {@link #toJava}. */
  public void setPrintTarget(VarType target) {
    this.printTarget = target;
  }

  /**
   * A bare switch with a type-variable target gets one cast per arm to the switch's own erasure
   * from javac itself, so the cast the tree carries around each arm's value is that compiled
   * coercion, not something the source wrote. Printing the value lets javac put it back.
   */
  private Exprent bareArmValue(Exprent content, VarType target) {
    if (target == null || !RoundTrip.selector("switchbare") || !RoundTrip.isTypeVariableTarget(target)
        || !(content instanceof FunctionExprent cast)
        || cast.getFuncType() != FunctionExprent.FunctionType.CAST
        || cast.getLstOperands().isEmpty()
        || !Objects.equals(cast.getExprType(), this.type)) {
      return content;
    }
    // The cast to the switch's own erasure is javac's own coercion for a bare switch, which it
    // re-creates from the case list; printing it pins the arm to the erasure instead.
    return cast.getLstOperands().get(0);
  }

  /**
   * Whether an arm's value provably fails the target's type arguments. A switch expression in an
   * assignment or invocation context is poly: javac checks every arm against the target type, and
   * an arm that is a call is inferred against it. The call's own recorded arguments can pin its
   * type variable to a class the target rejects. The target's {@code ? super X} at a position
   * where the arm's instantiation is a concrete class C cannot be satisfied when X's own recorded
   * upper bound is not a subtype of C: no inference satisfies both the argument's recorded type
   * and the target, so the source cast the arm. That cast erases to the class the arm already
   * has, which is why the class file does not show it. Lambdas and method references are left
   * alone: they have no type of their own and need the poly context.
   */
  private boolean armNeedsTargetCast(Exprent content, VarType target) {
    if (!(content instanceof InvocationExprent) || target == null || !target.isGeneric()
      || target.type != CodeType.OBJECT || target.arrayDim != 0) {
      return false;
    }
    List<VarType> targetArguments = ((GenericType) target).getArguments();
    Map<VarType, List<VarType>> named = getNamedGenerics();
    boolean bounded = false;
    for (VarType argument : targetArguments) {
      if (argument instanceof GenericType wildcard && wildcard.getWildcard() == GenericType.WILDCARD_SUPER
        && wildcard.type == CodeType.GENVAR && isInScopeTypeVariable(plainVariable(wildcard), named)) {
        bounded = true;
        break;
      }
    }
    if (!bounded) {
      return false; // an unbounded wildcard accepts every instantiation; a bare variable is inferable
    }

    VarType value = content.getInferredExprType(null);
    if (value == null || !value.isGeneric() || value.type != CodeType.OBJECT || value.arrayDim != 0) {
      return false;
    }
    VarType view = value.value.equals(target.value) ? value : GenericType.getGenericSuperType(value, target);
    if (view == null || !view.isGeneric() || !view.value.equals(target.value) || view.arrayDim != 0) {
      return false;
    }
    List<VarType> viewArguments = ((GenericType) view).getArguments();
    if (viewArguments.size() != targetArguments.size()) {
      return false;
    }

    for (int i = 0; i < targetArguments.size(); i++) {
      if (!(targetArguments.get(i) instanceof GenericType wildcard)
        || wildcard.getWildcard() != GenericType.WILDCARD_SUPER || wildcard.type != CodeType.GENVAR) {
        continue;
      }
      List<VarType> bounds = named.get(plainVariable(wildcard));
      if (bounds == null || bounds.isEmpty() || bounds.get(0) == null) {
        continue;
      }
      VarType upper = bounds.get(0);
      VarType actual = viewArguments.get(i);
      if (upper.type != CodeType.OBJECT || upper.arrayDim != 0
        || actual == null || actual.type != CodeType.OBJECT || actual.arrayDim != 0 || actual.isGeneric()) {
        continue; // only a concrete class argument can fall outside the variable's upper bound
      }
      if (!DecompilerContext.getStructContext().instanceOf(upper.value, actual.value)) {
        return true;
      }
    }
    return false;
  }

  private static VarType plainVariable(GenericType wildcard) {
    return GenericType.parse("T" + wildcard.value + ";");
  }

  private static boolean isEmptyDefault(BasicBlockStatement block, SwitchStatement head) {
    if (!block.getExprents().isEmpty()) {
      return false;
    }

    List<StatEdge> edges = block.getSuccessorEdgeView(StatEdge.TYPE_BREAK);

    return edges.size() == 1;
  }

  private boolean isExhaustive() {
    // exhaustive switches have a synthetic default edge of throw new IncompatibleClassChangeException()
    // see TestInlineSwitchExpression1
    // TODO: extend to exhaustive switch statements - consider MatchException
    Set<FieldExprent> enumValuesSeen = new HashSet<>();
    for (List<Exprent> caseValue : backing.getCaseValues()) {
      for (Exprent exprent : caseValue) {
        // only enums
        if (exprent instanceof FieldExprent && ((FieldExprent) exprent).isStatic()) {
          enumValuesSeen.add((FieldExprent) exprent);
        }
      }
    }
    StructClass enumTargetClass = DecompilerContext.getStructContext().getClass(backing.getHeadexprent().getExprType().value);
    return enumTargetClass != null && enumTargetClass.hasModifier(CodeConstants.ACC_ENUM)
      && enumTargetClass.getFields()
        .stream()
        .filter(x -> x.hasModifier(CodeConstants.ACC_ENUM))
        .map(StructField::getName)
        .allMatch(fieldName -> enumValuesSeen.stream().anyMatch(found -> found.getName().equals(fieldName)));
  }

  private static boolean isSyntheticThrowEdge(StatEdge edge){
    Statement target = edge.getDestination();
    List<Exprent> targetExprs = target.getExprents();
    if (targetExprs != null && targetExprs.size() == 1) {
      Exprent targetExpr = targetExprs.get(0);
      return targetExpr instanceof ExitExprent
        && ((ExitExprent) targetExpr).getExitType() == ExitExprent.Type.THROW
        && (((ExitExprent) targetExpr).getValue().getExprType().value.equals("java/lang/IncompatibleClassChangeError")
            || ((ExitExprent) targetExpr).getValue().getExprType().value.equals("java/lang/MatchException"));
    }
    return false;
  }

  public void setType(VarType type) {
    this.type = type;
  }

  @Override
  public int getPrecedence() {
    return 1; // Should enclose in case of invocation
  }

  @Override
  public VarType getExprType() {
    return this.type;
  }

  @Override
  public Exprent copy() {
    return new SwitchExprent(this.backing, this.type, this.fallthrough, this.standalone);
  }

  public SwitchStatement getBacking() {
    return backing;
  }

  @Override
  protected List<Exprent> getAllExprents(List<Exprent> list) {
    return list;
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values);
  }
}

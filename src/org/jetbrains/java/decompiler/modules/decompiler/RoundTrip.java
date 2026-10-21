package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLineNumberTableAttribute;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.util.BitSet;
import java.util.List;

/** Target-aware choices for byte-faithful output. Only active with {@code --round-trip=1}. */
public final class RoundTrip {
  private static final java.util.Map<StructMethod, BitSet> VOID_RETURNS = new java.util.concurrent.ConcurrentHashMap<>();
  /** For each continue guard, the end offset of its condition branch maps to the loop-head offset. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> CONTINUE_GUARDS = new java.util.concurrent.ConcurrentHashMap<>();
  /** Branch opcode by the end offset of each conditional branch, for polarity checks. */
  private static final java.util.Map<StructMethod, java.util.Map<Integer, Integer>> BRANCHES = new java.util.concurrent.ConcurrentHashMap<>();

  private RoundTrip() {}

  /** Remember where a method's void returns are; the instruction sequence is gone by print time. */
  public static void recordMethod(StructMethod method, FullInstructionSequence seq) {
    BitSet returns = new BitSet();
    java.util.Map<Integer, Integer> guards = new java.util.HashMap<>();
    java.util.Map<Integer, Integer> branches = new java.util.HashMap<>();
    for (int i = 0; i < seq.length(); i++) {
      Instruction instr = seq.getInstr(i);
      if (instr.opcode == CodeConstants.opc_return) {
        returns.set(instr.startOffset);
      }
      if (isConditional(instr.opcode)) {
        branches.put(instr.startOffset + instr.length, instr.opcode);
      }
      // `if (C) continue;`: the branch falls through to a backwards goto and jumps past it to the body.
      if (i + 1 < seq.length() && isConditional(instr.opcode)) {
        Instruction next = seq.getInstr(i + 1);
        if (next.opcode == CodeConstants.opc_goto) {
          int branchTarget = instr.startOffset + instr.operand(0);
          int gotoTarget = next.startOffset + next.operand(0);
          if (gotoTarget < next.startOffset && branchTarget > next.startOffset) {
            // Key by the branch's end; the head exprent's offsets cover the branch instruction.
            guards.put(instr.startOffset + instr.length, gotoTarget);
          }
        }
      }
    }
    VOID_RETURNS.put(method, returns);
    CONTINUE_GUARDS.put(method, guards);
    BRANCHES.put(method, branches);
  }

  /**
   * True when the target branched the other way: the original wrote the negated condition with the
   * arms swapped. Only plain boolean tests are handled; comparisons and short-circuit conditions
   * compile to different opcode families and are left alone.
   */
  public static boolean swapIfArms(Exprent head) {
    if (!selector("polarity") || !(head instanceof IfExprent ifHead)) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> branches = BRANCHES.get(method);
    BitSet offsets = head.bytecode;
    if (branches == null || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer opcode = branches.get(offsets.length());
    if (opcode == null) {
      return false;
    }
    int expected = lastBranch(ifHead.getCondition());
    int other = complement(expected);
    return other != 0 && opcode == other;
  }

  /**
   * The branch opcode javac emits after the last test of this condition when the arm is skipped —
   * the opcode the target would carry had the condition been written this way. `&&` and `||` both
   * test their right operand last and jump to the else arm when it is false; a negation swaps the
   * branch. Returns 0 for tests outside the boolean/null families.
   */
  private static int lastBranch(Exprent condition) {
    if (condition instanceof FunctionExprent function) {
      FunctionExprent.FunctionType type = function.getFuncType();
      if (type == FunctionExprent.FunctionType.BOOL_NOT) {
        return complement(lastBranch(function.getLstOperands().get(0)));
      }
      if (type == FunctionExprent.FunctionType.BOOLEAN_AND || type == FunctionExprent.FunctionType.BOOLEAN_OR) {
        java.util.List<Exprent> operands = function.getLstOperands();
        return lastBranch(operands.get(operands.size() - 1));
      }
      if ((type == FunctionExprent.FunctionType.EQ || type == FunctionExprent.FunctionType.NE)
          && function.getLstOperands().size() == 2
          && (isNull(function.getLstOperands().get(0)) || isNull(function.getLstOperands().get(1)))) {
        // `x == null` is false when non-null: the skip branch is ifnonnull.
        return type == FunctionExprent.FunctionType.EQ ? CodeConstants.opc_ifnonnull : CodeConstants.opc_ifnull;
      }
      if (type == FunctionExprent.FunctionType.INSTANCEOF) {
        return CodeConstants.opc_ifeq;
      }
      if ((type == FunctionExprent.FunctionType.AND || type == FunctionExprent.FunctionType.OR
          || type == FunctionExprent.FunctionType.XOR) && booleanOperands(function)) {
        // Non-short-circuit boolean arithmetic: one test after the operation, like a plain value.
        return CodeConstants.opc_ifeq;
      }
      if (function.getLstOperands().size() == 2) {
        VarType left = function.getLstOperands().get(0).getExprType();
        VarType right = function.getLstOperands().get(1).getExprType();
        if (left != null && right != null) {
          boolean refs = left.typeFamily == TypeFamily.OBJECT && right.typeFamily == TypeFamily.OBJECT;
          boolean ints = isIntegerFamily(left) && isIntegerFamily(right);
          // long/float/double compare through lcmp/fcmp and then branch on the int result.
          boolean wide = (left.typeFamily == TypeFamily.LONG && right.typeFamily == TypeFamily.LONG)
            || (left.typeFamily == TypeFamily.FLOAT && right.typeFamily == TypeFamily.FLOAT);
          switch (type) {
            case EQ:
              if (refs) return CodeConstants.opc_if_acmpne;
              if (ints) return CodeConstants.opc_if_icmpne;
              if (wide) return CodeConstants.opc_ifne;
              break;
            case NE:
              if (refs) return CodeConstants.opc_if_acmpeq;
              if (ints) return CodeConstants.opc_if_icmpeq;
              if (wide) return CodeConstants.opc_ifeq;
              break;
            case LT:
              if (ints) return CodeConstants.opc_if_icmpge;
              if (wide) return CodeConstants.opc_ifge;
              break;
            case GE:
              if (ints) return CodeConstants.opc_if_icmplt;
              if (wide) return CodeConstants.opc_iflt;
              break;
            case GT:
              if (ints) return CodeConstants.opc_if_icmple;
              if (wide) return CodeConstants.opc_ifle;
              break;
            case LE:
              if (ints) return CodeConstants.opc_if_icmpgt;
              if (wide) return CodeConstants.opc_ifgt;
              break;
          }
        }
      }
    }
    return isPlainBoolean(condition) ? CodeConstants.opc_ifeq : 0;
  }

  private static boolean isIntegerFamily(VarType type) {
    return type.typeFamily == TypeFamily.INTEGER || type.typeFamily == TypeFamily.BOOLEAN;
  }

  private static boolean booleanOperands(FunctionExprent function) {
    for (Exprent operand : function.getLstOperands()) {
      VarType type = operand.getExprType();
      if (type == null || type.typeFamily != TypeFamily.BOOLEAN) {
        return false;
      }
    }
    return !function.getLstOperands().isEmpty();
  }

  private static int complement(int opcode) {
    return switch (opcode) {
      case CodeConstants.opc_ifeq -> CodeConstants.opc_ifne;
      case CodeConstants.opc_ifne -> CodeConstants.opc_ifeq;
      case CodeConstants.opc_ifnull -> CodeConstants.opc_ifnonnull;
      case CodeConstants.opc_ifnonnull -> CodeConstants.opc_ifnull;
      case CodeConstants.opc_if_icmpeq -> CodeConstants.opc_if_icmpne;
      case CodeConstants.opc_if_icmpne -> CodeConstants.opc_if_icmpeq;
      case CodeConstants.opc_if_icmplt -> CodeConstants.opc_if_icmpge;
      case CodeConstants.opc_if_icmpge -> CodeConstants.opc_if_icmplt;
      case CodeConstants.opc_if_icmpgt -> CodeConstants.opc_if_icmple;
      case CodeConstants.opc_if_icmple -> CodeConstants.opc_if_icmpgt;
      case CodeConstants.opc_if_acmpeq -> CodeConstants.opc_if_acmpne;
      case CodeConstants.opc_if_acmpne -> CodeConstants.opc_if_acmpeq;
      case CodeConstants.opc_iflt -> CodeConstants.opc_ifge;
      case CodeConstants.opc_ifge -> CodeConstants.opc_iflt;
      case CodeConstants.opc_ifgt -> CodeConstants.opc_ifle;
      case CodeConstants.opc_ifle -> CodeConstants.opc_ifgt;
      default -> 0;
    };
  }

  private static boolean isNull(Exprent exprent) {
    return exprent instanceof ConstExprent constant && constant.isNull();
  }

  private static boolean isPlainBoolean(Exprent exprent) {
    return exprent instanceof InvocationExprent || exprent instanceof VarExprent
      || exprent instanceof FieldExprent || exprent instanceof ConstExprent;
  }

  private static boolean isConditional(int opcode) {
    return opcode >= CodeConstants.opc_ifeq && opcode <= CodeConstants.opc_if_acmpne
      || opcode == CodeConstants.opc_ifnull || opcode == CodeConstants.opc_ifnonnull;
  }

  public static boolean enabled() {
    return DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP);
  }

  /** For bisecting a suspect transform: {@code RT_OFF=name1,name2} turns these off. */
  /** The target's source line for the first instruction the exprent owns, or -1. */
  public static int sourceLine(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return -1;
    }
    return lineAt(method, exprent.bytecode.nextSetBit(0));
  }

  /** The target's source line for the instruction at the exprent's last offset, or -1. */
  public static int sourceLineEnd(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return -1;
    }
    return lineAt(method, exprent.bytecode.previousSetBit(Integer.MAX_VALUE));
  }

  /**
   * Whether the target's line table has an entry exactly at the expression's first instruction.
   * javac only marks lines where an AST node's position sits, so an argument that merely inherits
   * the enclosing statement's line has no entry of its own; a break there is layout the original
   * never had.
   */
  public static boolean lineStartsHere(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return false;
    }
    StructLineNumberTableAttribute lnt =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (lnt == null) {
      return false;
    }
    int offset = exprent.bytecode.nextSetBit(0);
    return lnt.findLineNumber(offset) != (offset <= 0 ? -1 : lnt.findLineNumber(offset - 1));
  }

  /** Whether the target's line table has an entry exactly at the expression's last instruction. */
  public static boolean lineStartsAtEnd(Exprent exprent) {
    StructMethod method = currentMethod();
    if (method == null || exprent == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return false;
    }
    StructLineNumberTableAttribute lnt =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (lnt == null) {
      return false;
    }
    int offset = exprent.bytecode.previousSetBit(Integer.MAX_VALUE);
    return lnt.findLineNumber(offset) != (offset <= 0 ? -1 : lnt.findLineNumber(offset - 1));
  }

  /** Whether the original source started the second expression on a later line than the first ended. */
  public static boolean newlineBetween(Exprent before, Exprent after) {
    int end = sourceLineEnd(before);
    int start = sourceLine(after);
    return end >= 0 && start >= 0 && start > end;
  }

  /** The target's source line for a method's first instruction. */
  public static int methodLine(StructMethod method) {
    if (method == null) {
      return -1;
    }
    return lineAt(method, 0);
  }

  private static int lineAt(StructMethod method, int offset) {
    StructLineNumberTableAttribute lnt =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    return lnt == null ? -1 : lnt.findLineNumber(offset);
  }

  public static boolean selector(String name) {
    if (!enabled()) {
      return false;
    }
    String disabled = System.getenv("RT_OFF");
    return disabled == null || !disabled.contains(name);
  }

  /**
   * True when the two return expressions come from distinct return instructions in the target.
   * A return-position ternary shares one return after a join; an if/else has one per arm.
   */
  public static boolean hasDistinctReturnInstructions(Exprent first, Exprent second) {
    if (!selector("ternary")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    int a = returnOffset(seq, first);
    int b = returnOffset(seq, second);
    return a >= 0 && b >= 0 && a != b;
  }

  /**
   * True when the target kept a duplicate of the left-hand side next to the matching operand:
   * {@code this.f += e} compiles as {@code aload_0; dup; getfield f; ...; putfield f}, while
   * {@code this.f = this.f + e} loads the field twice.
   */
  public static boolean isCompoundTarget(Exprent left, Exprent matching) {
    if (!selector("compound")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    BitSet offsets = matching.bytecode;
    if (seq == null || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer index = seq.offsetToIndex().get(offsets.nextSetBit(0));
    if (index == null) {
      return false;
    }
    int opcode = seq.getInstr(index).opcode;
    if (left instanceof FieldExprent) {
      if (opcode != CodeConstants.opc_getfield && opcode != CodeConstants.opc_getstatic) {
        return false;
      }
      return index > 0 && isDup(seq.getInstr(index - 1).opcode);
    }
    if (left instanceof VarExprent) {
      if (!isLoad(opcode)) {
        return false;
      }
      return index + 1 < seq.length() && isDup(seq.getInstr(index + 1).opcode);
    }
    return false;
  }

  private static boolean isDup(int opcode) {
    return opcode >= CodeConstants.opc_dup && opcode <= CodeConstants.opc_dup2_x2;
  }

  /** True when the target emitted a checkcast inside this expression's bytecode range. */
  public static boolean forceCast(Exprent exprent) {
    if (!selector("cast")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    return hasOpcode(seq, exprent, CodeConstants.opc_checkcast);
  }

  /**
   * True when {@code if (!C) { body }} corresponds to a target that returns when C holds, i.e. the
   * source was the guard {@code if (C) { return; } body}. The early return sits between the condition
   * and the body in the target's instruction sequence.
   */
  public static boolean printAsGuard(Exprent head, Statement body) {
    if (!selector("guardprint") || !(head instanceof IfExprent ie)) {
      return false;
    }
    Exprent condition = ie.getCondition();
    if (!(condition instanceof FunctionExprent function) || function.getFuncType() != FunctionExprent.FunctionType.BOOL_NOT) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    BitSet returns = VOID_RETURNS.get(method);
    BitSet offsets = head.bytecode;
    int bodyStart = firstOffset(body);
    if (returns == null || returns.isEmpty() || offsets == null || offsets.isEmpty()) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    int lastStart = -1;
    int lastEnd = -1;
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer index = seq.offsetToIndex().get(offset);
      if (index != null) {
        Instruction instr = seq.getInstr(index);
        if (instr.startOffset > lastStart) {
          lastStart = instr.startOffset;
          lastEnd = instr.startOffset + instr.length;
        }
      }
    }
    return lastEnd >= 0 && lastEnd < bodyStart && returns.get(lastEnd);
  }

  /**
   * True when the target returns before the body: the source was
   * {@code if (!C) { return value; } body} rather than {@code if (C) { body } return value;}.
   */
  public static boolean returnGuard(Statement body, Statement tail) {
    if (!selector("retguard")) {
      return false;
    }
    int bodyStart = firstOffset(body);
    int tailStart = firstOffset(tail);
    if (bodyStart < 0 || tailStart < 0) {
      return false;
    }
    // The original's line table says which shape it wrote: a guard puts the exit's line before the
    // body's, while `if (C) { body } exit;` puts it after, whatever order the blocks compile in.
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table != null) {
      int bodyLine = table.findLineNumber(bodyStart);
      int tailLine = table.findLineNumber(tailStart);
      if (System.getenv("NEUROFLOWER_RETGUARD_DEBUG") != null) {
        System.err.println("retguard " + method.getName() + " bodyStart " + bodyStart + " line " + bodyLine
          + " tailStart " + tailStart + " line " + tailLine);
      }
      if (bodyLine >= 0 && tailLine >= 0) {
        return tailLine < bodyLine;
      }
    }
    return tailStart < bodyStart;
  }

  /**
   * True when the target's table puts the exit's line after the following statement's, so the
   * source wrote {@code body; exit;} rather than the guard the bytecode's block order suggests.
   */
  public static boolean exitAfterBody(Statement exitStatement, Statement body) {
    if (!selector("exitlast")) {
      return false;
    }
    int exitStart = firstOffset(exitStatement);
    int bodyStart = firstOffset(body);
    if (exitStart < 0 || bodyStart < 0) {
      return false;
    }
    StructMethod method = currentMethod();
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return false;
    }
    int exitLine = table.findLineNumber(exitStart);
    int bodyLine = table.findLineNumber(bodyStart);
    if (System.getenv("NEUROFLOWER_RETGUARD_DEBUG") != null) {
      System.err.println("exitlast " + method.getName() + " exit " + exitStart + "@" + exitLine
        + " body " + bodyStart + "@" + bodyLine);
    }
    return exitLine >= 0 && bodyLine >= 0 && exitLine > bodyLine;
  }

  /**
   * True when the target compiled this if as {@code if (C) continue;} — the condition branches to
   * the body and the fall-through jumps back to the loop head. The printer's mirror is
   * {@code if (!C) { body }}, which compiles to the opposite branch with no goto.
   */
  public static boolean printContinueGuard(Exprent head, Statement sequence) {
    if (!selector("continueguard")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    java.util.Map<Integer, Integer> guards = CONTINUE_GUARDS.get(method);
    BitSet offsets = head.bytecode;
    if (guards == null || guards.isEmpty() || offsets == null || offsets.isEmpty()) {
      return false;
    }
    Integer target = guards.get(offsets.length());
    if (target == null) {
      return false;
    }
    Statement loop = sequence.getParent();
    while (loop != null && !(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement)) {
      loop = loop.getParent();
    }
    if (!(loop instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement doStatement)) {
      return false;
    }
    return isContinueTarget(doStatement, target);
  }

  /** The instruction a {@code continue} in this loop jumps to. */
  private static boolean isContinueTarget(org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement loop, int target) {
    Exprent head = switch (loop.getLooptype()) {
      case WHILE, DO_WHILE -> loop.getConditionExprent();
      case FOR, FOR_EACH -> loop.getIncExprent() != null ? loop.getIncExprent() : loop.getConditionExprent();
      default -> null;
    };
    if (head != null && head.bytecode != null && !head.bytecode.isEmpty()) {
      // The loop top may load a local the condition exprent does not own, so the target can sit
      // a short load before the exprent's first byte.
      int start = head.bytecode.nextSetBit(0);
      if (target <= start && target >= start - 3) {
        return true;
      }
    }
    // A for-each continue jumps to the compiler's hasNext block and a for's to the increment; both
    // live inside the loop but are not owned by the iterable or condition exprent.
    if (loop.getLooptype() == org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement.Type.FOR_EACH) {
      // A for-each continue jumps into the compiler's hasNext block, which sits before the first
      // instruction any exprent of the loop covers.
      int bodyStart = firstOffset(loop.getFirst());
      return target >= 0 && bodyStart >= 0 && target < bodyStart;
    }
    int min = firstOffset(loop);
    int max = lastOffset(loop);
    return min >= 0 && max >= min && target >= min && target <= max;
  }

  /** Last target offset covered by a statement, or -1. */
  public static int lastOffset(Statement statement) {
    int max = -1;
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          BitSet bits = inner.bytecode;
          if (bits != null && !bits.isEmpty()) {
            int offset = bits.length() - 1;
            if (offset > max) {
              max = offset;
            }
          }
        }
      }
    } else {
      for (Statement child : statement.getStats()) {
        int offset = lastOffset(child);
        if (offset > max) {
          max = offset;
        }
      }
    }
    return max;
  }

  /** First target offset covered by a statement, or -1. */
  public static int firstOffset(Statement statement) {
    int min = -1;
    List<Exprent> exprents = statement.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        // Wrappers such as yield carry no offsets of their own; the expression they hold does.
        for (Exprent inner : exprent.getAllExprents(true, true)) {
          BitSet bits = inner.bytecode;
          if (bits != null && !bits.isEmpty()) {
            int offset = bits.nextSetBit(0);
            if (min < 0 || offset < min) {
              min = offset;
            }
          }
        }
      }
    } else {
      for (Statement child : statement.getStats()) {
        int offset = firstOffset(child);
        if (offset >= 0 && (min < 0 || offset < min)) {
          min = offset;
        }
      }
    }
    return min;
  }

  /** True when the target loads this local into the return, i.e. the source kept the variable. */
  public static boolean targetReturnUsesLocal(Exprent exit, int var) {
    if (!selector("returnlocal")) {
      return false;
    }
    StructMethod method = currentMethod();
    if (method == null) {
      return false;
    }
    FullInstructionSequence seq = method.getInstructionSequence();
    if (seq == null) {
      return false;
    }
    int ret = returnOffset(seq, exit);
    Integer index = ret < 0 ? null : seq.offsetToIndex().get(ret);
    if (index == null || index < 2) {
      return false;
    }
    Instruction load = seq.getInstr(index - 1);
    Instruction store = seq.getInstr(index - 2);
    return isLoad(load.opcode) && isStore(store.opcode)
      && variableIndex(load) == var && variableIndex(store) == var;
  }

  private static boolean isLoad(int opcode) {
    return opcode >= CodeConstants.opc_iload && opcode <= CodeConstants.opc_aload
      || opcode >= CodeConstants.opc_iload_0 && opcode <= CodeConstants.opc_aload_3;
  }

  private static boolean isStore(int opcode) {
    return opcode >= CodeConstants.opc_istore && opcode <= CodeConstants.opc_astore
      || opcode >= CodeConstants.opc_istore_0 && opcode <= CodeConstants.opc_astore_3;
  }

  private static int variableIndex(Instruction instr) {
    if (instr.opcode >= CodeConstants.opc_iload && instr.opcode <= CodeConstants.opc_aload
      || instr.opcode >= CodeConstants.opc_istore && instr.opcode <= CodeConstants.opc_astore) {
      return instr.operand(0);
    }
    if (instr.opcode >= CodeConstants.opc_iload_0 && instr.opcode <= CodeConstants.opc_aload_3) {
      return (instr.opcode - CodeConstants.opc_iload_0) % 4;
    }
    return (instr.opcode - CodeConstants.opc_istore_0) % 4;
  }

  private static StructMethod currentMethod() {
    StructMethod method = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    if (method != null) {
      return method;
    }
    MethodWrapper wrapper = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    return wrapper == null ? null : wrapper.methodStruct;
  }

  private static boolean hasOpcode(FullInstructionSequence seq, Exprent exprent, int wanted) {
    BitSet offsets = exprent.bytecode;
    if (offsets == null) {
      return false;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer index = seq.offsetToIndex().get(offset);
      if (index != null && seq.getInstr(index).opcode == wanted) {
        return true;
      }
    }
    return false;
  }

  private static int returnOffset(FullInstructionSequence seq, Exprent exprent) {
    BitSet offsets = exprent.bytecode;
    if (offsets == null) {
      return -1;
    }
    for (int offset = offsets.nextSetBit(0); offset >= 0; offset = offsets.nextSetBit(offset + 1)) {
      Integer index = seq.offsetToIndex().get(offset);
      if (index == null) {
        continue;
      }
      int opcode = seq.getInstr(index).opcode;
      if (opcode >= CodeConstants.opc_ireturn && opcode <= CodeConstants.opc_return) {
        return offset;
      }
    }
    return -1;
  }
}

// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.SwitchInstruction;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLineNumberTableAttribute;
import org.jetbrains.java.decompiler.struct.gen.TypeFamily;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.StartEndPair;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.*;
import java.util.stream.Collectors;

public class SwitchStatement extends Statement {

  // *****************************************************************************
  // private fields
  // *****************************************************************************

  private List<Statement> caseStatements = new ArrayList<>();

  private List<List<StatEdge>> caseEdges = new ArrayList<>();

  private List<List<Exprent>> caseValues = new ArrayList<>();

  private final List<Exprent> caseGuards = new ArrayList<>();

  private final Set<Statement> scopedCaseStatements = new HashSet<>();

  private StatEdge defaultEdge;

  private final List<Exprent> headexprent = new ArrayList<>(1);

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected SwitchStatement() {
    super(StatementType.SWITCH);

    headexprent.add(null);
  }

  protected SwitchStatement(Statement head, Statement poststat) {

    this();

    first = head;
    stats.addWithKey(head, head.id);

    // find post node
    Set<Statement> lstNodes = new HashSet<>(head.getNeighbours(StatEdge.TYPE_REGULAR, EdgeDirection.FORWARD));

    // cluster nodes
    if (poststat != null) {
      post = poststat;
      lstNodes.remove(post);
    }

    defaultEdge = head.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL).get(0);

    //We need to use set above in case we have multiple edges to the same node. But HashSets iterator is not ordered, so sort
    List<Statement> sorted = new ArrayList<>(lstNodes);
    sorted.sort(Comparator.comparingInt(o -> o.id));
    for (Statement st : sorted) {
      stats.addWithKey(st, st.id);
    }
  }

  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {

    if (head instanceof BasicBlockStatement && head.getLastBasicType() == LastBasicType.SWITCH) {

      List<Statement> lst = new ArrayList<>();
      if (DecHelper.isChoiceStatement(head, lst)) {
        Statement post = lst.remove(0);

        for (Statement st : lst) {
          if (st.isMonitorEnter()) {
            return null;
          }
        }

        if (DecHelper.checkStatementExceptions(lst)) {
          return new SwitchStatement(head, post);
        }
      }
    }

    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {

    TextBuffer buf = new TextBuffer();
    buf.append(ExprProcessor.listToJava(varDefinitions, indent));
    buf.append(first.toJava(indent));

    boolean showPhantom = DecompilerContext.getOption(IFernflowerPreferences.SHOW_HIDDEN_STATEMENTS);

    // Is phantom and we don't want to show- just return what we have so far
    if (this.isPhantom() && !showPhantom) {
      return buf;
    }

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    buf.appendIndent(indent);
    if (this.isPhantom()) {
      buf.append("/*");
    }

    buf.append(headexprent.get(0).toJava(indent)).append(" {").appendLineSeparator();

    // Two arms that define the same local name share the switch's block scope, and Java forbids a
    // nested block from shadowing an enclosing local; the target's names say they were distinct
    // variables, so the source braced the arms.
    Set<Statement> braced = new HashSet<>(this.scopedCaseStatements);
    Map<String, List<Statement>> definitions = new HashMap<>();
    for (Statement caseStat : caseStatements) {
      Set<String> names = new HashSet<>();
      collectCaseNames(caseStat, names);
      for (String name : names) {
        definitions.computeIfAbsent(name, key -> new ArrayList<>()).add(caseStat);
      }
    }
    for (List<Statement> arms : definitions.values()) {
      if (arms.size() > 1) {
        braced.addAll(arms);
      }
    }

    // A slot two arms declare in the target's table: the earlier arm's local died at its closing
    // brace and javac handed the slot to a later arm, which only a braced arm can do. Only the
    // earlier arm is braced: the later local's start says nothing about where its own arm closed,
    // since the slot it reuses is simply free by then.
    Set<Statement> bracedEarly = new HashSet<>();
    List<Map<Integer, int[]>> armSlots = new ArrayList<>();
    List<List<int[]>> armRows = new ArrayList<>();
    for (Statement arm : caseStatements) {
      List<int[]> rows = RoundTrip.declarationRows(arm);
      armRows.add(rows);
      armSlots.add(RoundTrip.targetSlotsDeclaredIn(arm, rows));
    }
    for (int a = 0; a < armSlots.size(); a++) {
      for (int b = a + 1; b < armSlots.size(); b++) {
        int armEnd = RoundTrip.lastOffset(caseStatements.get(a));
        for (Map.Entry<Integer, int[]> first : armSlots.get(a).entrySet()) {
          int[] second = armSlots.get(b).get(first.getKey());
          // The earlier local has to die at its arm's closing brace and the later one to start
          // after it: a local declared in a nested block dies inside the arm instead.
          if (second != null && first.getValue()[1] <= second[0]
              && armEnd >= 0 && first.getValue()[1] >= armEnd - 1) {
            bracedEarly.add(caseStatements.get(a));
          }
        }
      }
    }
    braced.addAll(bracedEarly);

    VarType switch_type = headexprent.get(0).getExprType();

    // The instruction just after the whole switch: an arm whose block ends with a jump landing
    // there ended in a `break;` the source wrote and the tree dropped. The sibling's first
    // instruction can overshoot the join when its condition exprent records no offset of its own,
    // so an arm's own landing that sits before it names the join more precisely.
    int switchEnd = switchEndFromSibling();
    int jumpEnd = switchEndFromJumps();
    int targetEnd = switchEndFromTargetJumps();
    if (targetEnd >= 0 && (jumpEnd < 0 || targetEnd < jumpEnd)) {
      jumpEnd = targetEnd;
    }
    if (jumpEnd >= 0 && (switchEnd < 0 || jumpEnd < switchEnd)) {
      switchEnd = jumpEnd;
    }

    // A local the arm declares whose target row ends at a jump out of the arm: the source braced
    // the arm, so the block closed before that jump and the row ends where the jump starts
    // instead of at the switch's join.
    java.util.Map<Integer, Integer> gotos = RoundTrip.gotosHere();
    int[] armClose = new int[caseStatements.size()];
    java.util.Arrays.fill(armClose, -1);
    if (gotos != null) {
      for (int a = 0; a < caseStatements.size(); a++) {
        for (int[] row : armSlots.get(a).values()) {
          Integer dest = row[1] >= 0 ? gotos.get(row[1]) : null;
          if (dest != null && dest == switchEnd) {
            braced.add(caseStatements.get(a));
            // The break this arm prints after its brace is the jump another jump lands on; the
            // arm's own close is the furthest such row, so the choice does not depend on the
            // table's row order.
            if (RoundTrip.jumpsOnto(row[1]) && row[1] > armClose[a]) {
              armClose[a] = row[1];
            }
          }
        }
      }
    }
    List<Integer> order = sourceOrder(switchEnd);
    // When the printed order leaves the arms' bytecode blocks in another sequence, the source was
    // written in an order the class file did not record and the jumps say nothing about a break
    // this printer could put back: the group a jump belongs to is not the group it prints in.
    boolean orderUnknown = layoutReordered(order);
    // An arm that only throws a synthesized MatchException prints only when the switch is an
    // expression in statement form: its arms have to cover every input, and javac rejects a
    // switch expression that misses one.
    boolean skipMatch = !RoundTrip.switchYields(caseStatements);
    // A switch expression printed in statement form yields from its arms; a `break;` there would
    // neither compile nor be what the source wrote.
    boolean yields = !skipMatch;
    int lastPrinted = -1;
    for (int i : order) {
      if (!(skipMatch && RoundTrip.synthesizedMatchThrow(caseStatements.get(i)))) {
        lastPrinted = i;
      }
    }

    // The class file's default target is the join: a value matching no label lands past the
    // switch, so the source wrote no `default:` group whose block this switch owns. The tree
    // nonetheless hangs the default edge off an arm when that arm's block holds none of its
    // instructions — a case whose jump to the join was elided, or the join block itself — and
    // printing the label there is what a recompiled table would take as the default's target.
    // Whether the source wrote a trailing `default: break;` is the rule below's decision.
    boolean defaultIsJoin = switchEnd >= 0 && defaultTargetOffset() == switchEnd
      && RoundTrip.selector("switchbreak") && RoundTrip.selector("switchdefault")
      && !yields && !isPattern() && caseGuards.stream().noneMatch(Objects::nonNull);

    // The default arm can also be the block the source wrote after the switch: the default target
    // opens the arm's block, and the local variable table says a declaration inside it shares the
    // enclosing block's scope, where a block-scoped one would have closed first. The label was
    // empty then, and the statements belong after the switch's closing brace.
    Statement joinArm = defaultJoinArm(yields);
    Statement caseJoinArm = caseJoinArm(yields, switchEnd);

    // An empty `default: break;` group compiles to a jump the table's default target points at.
    // No arm carries that edge when the group holds nothing of its own, so the label is printed
    // where the target's block sits among the arms: at the table's default offset, not at the join
    // the jump lands on.
    int defaultBreakJump = -1;
    if (switchEnd >= 0 && !yields && !isPattern() && caseGuards.stream().noneMatch(Objects::nonNull)
        && RoundTrip.selector("switchbreak") && RoundTrip.selector("switchdefault")) {
      int target = defaultTargetOffset();
      // The jump has to stand among the arm blocks: one past all of them is the switch's own
      // join, the instruction every arm falls through to, not a group the source wrote.
      int armLimit = -1;
      for (Statement arm : caseStatements) {
        armLimit = Math.max(armLimit, RoundTrip.blockEnd(arm));
      }
      if (target >= 0 && target < armLimit && RoundTrip.jumpTargetAt(target) == switchEnd) {
        boolean onArm = false;
        for (List<StatEdge> edges : caseEdges) {
          for (StatEdge edge : edges) {
            if (edge == defaultEdge) {
              onArm = true;
            }
          }
        }
        if (!onArm) {
          defaultBreakJump = target;
        }
      }
    }

    boolean defaultPrinted = false;
    boolean defaultBreakPrinted = false;
    boolean lastJoins = false;
    for (int i : order) {

      Statement stat = caseStatements.get(i);
      if (skipMatch && RoundTrip.synthesizedMatchThrow(stat)) {
        continue;
      }
      if (defaultBreakJump >= 0 && !defaultBreakPrinted && entryOffset(i) > defaultBreakJump) {
        buf.appendIndent(indent + 1).append("default:").appendLineSeparator();
        buf.append(breakLine(indent + 2, defaultBreakJump));
        defaultBreakPrinted = true;
      }
      List<StatEdge> edges = caseEdges.get(i);
      List<Exprent> values = caseValues.get(i);
      Exprent guard = caseGuards.size() > i ? caseGuards.get(i) : null;

      // An empty arm whose table entry is the join instruction itself: javac writes no code for
      // a label with an empty body, so the source either wrote no group or an empty one at the
      // very end — both compile to this table. Print nothing for it.
      if (RoundTrip.selector("switchempty") && RoundTrip.firstOffset(stat) < 0
          && armLandsOnJoinDirectly(i, switchEnd)) {
        continue;
      }

      boolean anyLabel = false;
      for (int j = 0; j < edges.size(); j++) {
        if (edges.get(j) == defaultEdge) {
          if (defaultIsJoin || stat == joinArm) {
            continue;
          }
          anyLabel = true;
          defaultPrinted = true;
          buf.appendIndent(indent + 1).append("default:");
          if (braced.contains(stat) && j == edges.size() - 1) {
            buf.append(" {");
          }

          buf.appendLineSeparator();
        } else {
          anyLabel = true;
          Exprent value = values.get(j);

          buf.appendIndent(indent + 1).append("case ");

          if (value instanceof ConstExprent && !value.getExprType().equals(VarType.VARTYPE_NULL)) {
            value = value.copy();
            ((ConstExprent)value).setConstType(switch_type);
          } if (value instanceof FieldExprent field && field.isStatic() && (!getTopParent().mt.getBytecodeVersion().hasSwitchPatternMatch() || switch_type.equals(field.getExprType()))) { // enum values
            buf.appendField(field.getName(), false, field.getClassname(), field.getName(), field.getDescriptor());
          } else if (value instanceof FieldExprent field) {
            buf.append(field.toJava(indent, false));
          } else if (value instanceof FunctionExprent && ((FunctionExprent) value).getFuncType() == FunctionType.INSTANCEOF) {
            // Pattern matching variables

            Pattern pattern = (Pattern) value.getAllExprents().get(2);
            for (VarExprent var : pattern.getPatternVars()) {
              var.setWritingPattern();
            }

            buf.append(value.getAllExprents().get(2).toJava(indent));
          } else {
            buf.append(value.toJava(indent));
          }

          if (guard != null) {
            buf.append(" when ").append(guard.toJava());
          }

          buf.append(":");
          if (braced.contains(stat) && j == edges.size() - 1) {
            buf.append(" {");
          }
          buf.appendLineSeparator();
        }
      }

      // Every label this arm carried was the joined default, which the source did not write
      // here: the arm is no group at all, and its body would attach to the arm before it.
      if (!anyLabel) {
        continue;
      }

      // The arm's block is the join itself: its table targets jump there, and the statements it
      // holds are the ones the source wrote after the switch. Only the label and its `break;`
      // belong to the switch; the body prints after the closing brace.
      if (stat == caseJoinArm) {
        int jump = caseJoinJump(caseStatements.indexOf(stat), switchEnd);
        if (jump >= 0) {
          buf.append(breakLine(indent + 2, jump));
        }
        continue;
      }

      // The target's own jump lands on the break's jump: the arm ended at a closing brace, the
      // `break;` stood outside it, and javac kept the two jumps apart. Print the break there, so
      // it does not merge with the arm's last jump. Everything the `} break;` print below needs
      // is decided here: removing the arm's own jump without printing it back would drop a break.
      int breakJump = armBreakJump(stat, edges, switchEnd);
      boolean patternArm = values.stream().anyMatch(value -> value instanceof FunctionExprent function
        && function.getFuncType() == FunctionType.INSTANCEOF);
      boolean breakOutside = braced.contains(stat) && bracedEarly.contains(stat) && breakJump >= 0
        && !yields && !orderUnknown && guard == null && !patternArm
        && RoundTrip.canCompleteNormally(stat) && !declaredScopePast(armRows.get(i), breakJump)
        && RoundTrip.selector("switchbreak") && RoundTrip.jumpsOnto(breakJump);
      // A local the arm declares ends its row exactly at the break's jump, and another jump lands
      // on that jump: the source closed the arm's block before the break, so the break prints
      // after the closing brace instead of inside whatever branch the tree hung it off.
      int deferredBreak = -1;
      if (armClose[i] > 0 && braced.contains(stat) && !breakOutside && !yields && !orderUnknown
          && guard == null && RoundTrip.selector("switchbreak")
          && (breakJump < 0 || breakJump == armClose[i])
          && !declaredScopePast(armRows.get(i), armClose[i])
          && RoundTrip.jumpsOnto(armClose[i]) && RoundTrip.breaksTo(stat, this)) {
        deferredBreak = armClose[i];
      }
      Statement previousJump = breakOutside ? RoundTrip.suppressJump(stat) : null;
      Statement previousDefer = deferredBreak > 0 ? RoundTrip.deferBreakTo(this) : null;
      TextBuffer armBuf;
      try {
        armBuf = ExprProcessor.jmpWrapper(stat, indent + 2, false);
      } finally {
        if (deferredBreak > 0) {
          RoundTrip.restoreDeferredBreak(previousDefer);
        }
        if (breakOutside) {
          RoundTrip.restoreJump(previousJump);
        }
      }
      buf.append(armBuf);
      // What the arm actually printed decides whether it still needs a `break;`. The tree's own
      // edge is not enough evidence: an explicit break edge can hang off a statement the printer
      // renders without one, which is exactly the arm that falls through on the page.
      String armText = armBuf.convertToStringAndAllowDataDiscard().stripTrailing();

      // An arm whose block ends with a jump past the switch printed no `break;`: the target's
      // jump proves the source wrote one, and `canCompleteNormally` keeps it reachable. The last
      // group is no exception: javac keeps a break's jump whenever another group follows it, and
      // the trailing `default:` below supplies that group.
      boolean armLeaves = leavesArm(armText);
      boolean joins = breakJump >= 0;
      if (i == lastPrinted) {
        lastJoins = joins;
      }
      // The arm's tail instruction is a jump past the switch, but the source may have written the
      // break inside a nested branch: an arm ending in `if (...) { ...; break; }` falls through on
      // the other path, and the explicit jump edge hanging off that branch is what the printer
      // already rendered. Only an arm whose tail path carries no explicit jump owes a break at its
      // end for the target's tail goto.
      boolean breakPrinted = RoundTrip.printsExplicitJump(stat);
      boolean breakInside = false;
      if (RoundTrip.selector("switchbreak") && joins && !yields && !orderUnknown
          && guard == null && !patternArm && !breakPrinted
          && RoundTrip.canCompleteNormally(stat) && !armLeaves) {
        // A braced arm holds the break inside the brace when the target's table still has a local
        // the arm declared alive past the jump: the block was open there.
        breakInside = braced.contains(stat) && declaredScopePast(armRows.get(i), breakJump);
        if (!braced.contains(stat) || breakInside) {
          buf.append(breakLine(indent + 2, breakJump));
        }
      }

      if (braced.contains(stat)) {
        buf.appendIndent(indent + 1);
        buf.append("}");
        // The source wrote `} break;` for an arm braced to scope its locals; the same conditions
        // that decide a dropped `break` apply, since the brace does not change reachability. A
        // deferred break is the one the table proves: its jump is reachable from the jump onto it.
        if ((breakOutside || deferredBreak > 0
             || bracedEarly.contains(stat) && !RoundTrip.printsExplicitJump(stat))
            && (breakJump >= 0 || deferredBreak > 0) && !breakInside && guard == null
            && (!patternArm || deferredBreak > 0)
            && (deferredBreak > 0 || RoundTrip.canCompleteNormally(stat))) {
          int at = buf.length();
          buf.append(" break;");
          buf.addBytecodeMappingAt(at, deferredBreak > 0 ? deferredBreak : breakJump, null, null);
        }
        buf.appendLineSeparator();
      }
    }

    if (defaultBreakJump >= 0 && !defaultBreakPrinted) {
      buf.appendIndent(indent + 1).append("default:").appendLineSeparator();
      buf.append(breakLine(indent + 2, defaultBreakJump));
      defaultBreakPrinted = true;
    }

    // A `default:` the arms never print and whose table entry lands on the join had an empty body
    // the source still wrote out: the group is what keeps the last arm's `break;` jump in place,
    // so it has to be printed back even though it compiles to no instruction of its own.
    if (RoundTrip.selector("switchbreak") && RoundTrip.selector("switchdefault")
        && switchEnd >= 0 && !defaultPrinted && lastPrinted >= 0 && lastJoins
        && !yields && !orderUnknown && !isPattern() && caseGuards.stream().noneMatch(Objects::nonNull)
        && defaultTargetOffset() == switchEnd) {
      buf.appendIndent(indent + 1).append("default:").appendLineSeparator();
      buf.appendIndent(indent + 2).append("break;").appendLineSeparator();
    }

    buf.appendIndent(indent).append("}").appendLineSeparator();

    if (joinArm != null) {
      buf.append(ExprProcessor.jmpWrapper(joinArm, indent, false));
    }
    if (caseJoinArm != null) {
      buf.append(ExprProcessor.jmpWrapper(caseJoinArm, indent, false));
    }

    if (this.isPhantom()) {
      buf.append("*/");
    }

    return buf;
  }

  /**
   * The case arm whose block is the join: the switch table's target for its label is a jump to the
   * instruction after the switch, and the arm's own block starts there. The source wrote the
   * labels with an empty body and the statements after the switch.
   */
  private Statement caseJoinArm(boolean yields, int switchEnd) {
    if (!RoundTrip.selector("switchcasejoin") || switchEnd < 0 || yields || isPattern()
        || caseGuards.stream().anyMatch(Objects::nonNull)) {
      return null;
    }
    for (int i = 0; i < caseStatements.size(); i++) {
      Statement arm = caseStatements.get(i);
      if (arm != null && arm != joinArmForDefault() && RoundTrip.firstOffset(arm) == switchEnd
          && caseJoinJump(i, switchEnd) >= 0) {
        return arm;
      }
    }
    return null;
  }

  /** The label's table target when it is a jump to the join, or -1. */
  private int caseJoinJump(int index, int switchEnd) {
    if (switchEnd < 0 || index < 0 || index >= caseEdges.size()) {
      return -1;
    }
    List<StatEdge> edges = caseEdges.get(index);
    SwitchInstruction instruction = switchInstruction();
    int[] targets = instruction == null ? null : RoundTrip.switchTargetsAt(instruction.startOffset);
    if (targets == null || edges.isEmpty()) {
      return -1;
    }
    List<StatEdge> successors = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    int jump = -1;
    for (StatEdge edge : edges) {
      if (edge == defaultEdge) {
        return -1;
      }
      int at = successors.indexOf(edge);
      if (at < 0 || at >= targets.length) {
        return -1;
      }
      int target = targets[at];
      if (RoundTrip.jumpTargetAt(target) != switchEnd || (jump >= 0 && jump != target)) {
        return -1;
      }
      jump = target;
    }
    return jump;
  }

  /**
   * True when this arm's case labels all land on the join instruction itself, and the labels sit
   * inside the table's key span: dropping them leaves the same tableswitch, since javac writes
   * the default's own offset for a key with no label. A label at the span's edge, or in a
   * lookupswitch, does change the instruction and the source must have written it.
   */
  private boolean armLandsOnJoinDirectly(int index, int switchEnd) {
    if (switchEnd < 0 || index < 0 || index >= caseEdges.size()) {
      return false;
    }
    List<StatEdge> edges = caseEdges.get(index);
    SwitchInstruction instruction = switchInstruction();
    int[] targets = instruction == null ? null : RoundTrip.switchTargetsAt(instruction.startOffset);
    if (targets == null || edges.isEmpty()
        || instruction.opcode != org.jetbrains.java.decompiler.code.CodeConstants.opc_tableswitch) {
      return false;
    }
    int[] keys = instruction.getValues();
    if (keys.length == 0 || defaultTargetOffset() != switchEnd) {
      return false;
    }
    List<StatEdge> successors = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    boolean any = false;
    for (StatEdge edge : edges) {
      if (edge == defaultEdge) {
        continue;
      }
      int at = successors.indexOf(edge);
      if (at < 0 || at >= targets.length || targets[at] != switchEnd
          || RoundTrip.jumpTargetAt(targets[at]) >= 0) {
        return false;
      }
      // The table's first and last keys come from a written label: a gap in the middle still
      // has an entry, an endpoint without one would shrink the table.
      int position = at - 1;
      if (position <= 0 || position >= keys.length - 1) {
        return false;
      }
      any = true;
    }
    return any;
  }

  private Statement joinArmForDefault() {
    return defaultEdge == null ? null : defaultEdge.getDestination();
  }

  /**
   * The default arm whose body the source wrote after the switch, or null. The arm's block has to
   * start at the default target, carry no case labels of its own, and declare a local that the
   * target's table puts in the enclosing block's scope.
   */
  private Statement defaultJoinArm(boolean yields) {
    if (defaultEdge == null || yields || isPattern() || caseGuards.stream().anyMatch(Objects::nonNull)) {
      return null;
    }
    Statement arm = defaultEdge.getDestination();
    if (arm == null || !caseStatements.contains(arm)) {
      return null;
    }
    int at = RoundTrip.firstOffset(arm);
    if (at < 0 || at != defaultTargetOffset()) {
      return null;
    }
    // The arm must be reachable only through the default label; one that also carries case labels
    // is a real group the jump table enters.
    for (List<StatEdge> edges : caseEdges) {
      for (StatEdge edge : edges) {
        if (edge != defaultEdge && edge.getDestination() == arm) {
          return null;
        }
      }
    }
    // A local already in scope where the arm's block starts was declared outside the switch; the
    // table's order says whether the arm's own declaration shares that scope.
    if (!RoundTrip.sharesEnclosingScope(arm, at)) {
      return null;
    }
    return arm;
  }

  /**
   * True when the arm's printed text already ends in an unconditional exit, so appending a
   * {@code break;} would be unreachable: a return, a throw, or a break/continue of a labelled
   * statement further out.
   */
  private static boolean leavesArm(String text) {
    String tail = text.stripTrailing();
    return tail.endsWith("break;") || tail.endsWith("continue;") || tail.endsWith("return;")
      || tail.endsWith("throw;") || LABEL_EXIT.matcher(tail).find();
  }

  private static final java.util.regex.Pattern LABEL_EXIT =
    java.util.regex.Pattern.compile("(?:break|continue) label\\d+;$");

  /**
   * A {@code break;} line tied to the jump the source's break compiled to: the target's table puts
   * that jump on the line the statement was written on, so the line alignment has to see it.
   */
  private static TextBuffer breakLine(int indent, int jumpOffset) {
    TextBuffer line = new TextBuffer();
    line.appendIndent(indent).append("break;").appendLineSeparator();
    if (jumpOffset >= 0) {
      line.addStartBytecodeMapping(jumpOffset);
    }
    return line;
  }

  /**
   * True when the order the arms print in is provably neither the bytecode's block order nor an
   * unknown. Javac lays the blocks out in source order, so a switch printed in its table's key
   * order while the blocks sit in another sequence was written in an order the class file only
   * records through the line table — and there the jump evidence belongs to a layout that is not
   * being printed. An arm with no instruction of its own makes the block order unprovable.
   */
  private boolean layoutReordered(List<Integer> order) {
    int size = caseStatements.size();
    if (size < 2) {
      return false;
    }
    // The join block is no arm: its instructions lie after the switch, so they say nothing about
    // where its label stood in the source.
    int join = RoundTrip.selector("switchcasejoin") ? switchEndFromJumps() : -1;
    List<Integer> layout = new ArrayList<>(size);
    for (int i = 0; i < size; i++) {
      int first = RoundTrip.firstOffset(caseStatements.get(i));
      if (first < 0) {
        return false;
      }
      if (first == join) {
        continue;
      }
      layout.add(i);
    }
    layout.sort(Comparator.comparingInt(i -> RoundTrip.firstOffset(caseStatements.get(i))));
    List<Integer> printed = new ArrayList<>(order);
    printed.retainAll(layout);
    return !layout.equals(printed);
  }

  /** The offset just past the switch, read from the statement that follows it, or -1. */
  private int switchEndFromSibling() {
    if (!(getParent() instanceof SequenceStatement sequence)) {
      return -1;
    }
    List<Statement> siblings = sequence.getStats();
    for (int k = siblings.indexOf(this) + 1; k > 0 && k < siblings.size(); k++) {
      int offset = RoundTrip.firstOffset(siblings.get(k));
      if (offset >= 0) {
        return offset;
      }
    }
    return -1;
  }

  /**
   * The join a dropped {@code break;} jumps to, read from the arms themselves. A `break` in a
   * group another group follows compiles to a jump the elision cannot remove, so where an arm's
   * tail jump lands is the join — but only when that point lies past every arm's body and is not
   * where a {@code continue;} of an enclosing loop would land instead.
   */
  private int switchEndFromJumps() {
    if (!RoundTrip.selector("switchjump")) {
      return -1;
    }
    // An arm is the join itself when another arm's tail jump lands on its first instruction: that
    // block is the code after the switch, and its own instructions must not raise the bar the
    // join has to clear.
    int limit = -1;
    for (Statement arm : caseStatements) {
      int first = RoundTrip.firstOffset(arm);
      boolean isJoinBlock = false;
      if (first >= 0 && RoundTrip.selector("switchcasejoin")) {
        for (Statement other : caseStatements) {
          if (other != arm && RoundTrip.tailJumpTarget(other) == first) {
            isJoinBlock = true;
            break;
          }
        }
      }
      if (!isJoinBlock) {
        limit = Math.max(limit, RoundTrip.blockEnd(arm));
      }
    }
    int join = -1;
    for (Statement arm : caseStatements) {
      int target = RoundTrip.tailJumpTarget(arm);
      if (target < 0 || target < limit || RoundTrip.enclosingContinueTarget(this, target)) {
        continue;
      }
      if (join >= 0 && join != target) {
        return -1; // two landings past every arm: not the plain break this rule can read
      }
      join = target;
    }
    return join;
  }

  /**
   * The join a label's table target names through its own jump. An empty group's {@code break;}
   * compiles to a jump the case label points at, and that jump lands on the instruction after the
   * switch: when the group is the body's last statement the loop makes the landing the only such
   * evidence there is. A destination before the labels (a {@code continue;} to the loop head) or
   * one an enclosing loop continues to says nothing, and two different landings are not a join.
   */
  private int switchEndFromTargetJumps() {
    if (!RoundTrip.selector("switchjump")) {
      return -1;
    }
    SwitchInstruction instruction = switchInstruction();
    int[] targets = instruction == null ? null : RoundTrip.switchTargetsAt(instruction.startOffset);
    if (targets == null) {
      return -1;
    }
    List<StatEdge> successors = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    int limit = -1;
    for (int i = 0; i < caseStatements.size(); i++) {
      limit = Math.max(limit, entryOffset(i));
    }
    int join = -1;
    for (List<StatEdge> edges : caseEdges) {
      for (StatEdge edge : edges) {
        int at = successors.indexOf(edge);
        if (at < 0 || at >= targets.length) {
          continue;
        }
        int landed = RoundTrip.jumpTargetAt(targets[at]);
        if (landed < 0 || landed < limit || RoundTrip.continuesAtLoopHead(this, landed)) {
          continue;
        }
        if (join >= 0 && join != landed) {
          return -1;
        }
        join = landed;
      }
    }
    return join;
  }

  /** The switch instruction starting this statement, or null when the head holds none. */
  private SwitchInstruction switchInstruction() {
    if (first instanceof BasicBlockStatement head
      && head.getBlock().getLastInstruction() instanceof SwitchInstruction instruction) {
      return instruction;
    }
    return null;
  }

  /** The offset a value matching no case jumps to, or -1. */
  private int defaultTargetOffset() {
    SwitchInstruction instruction = switchInstruction();
    int[] targets = instruction == null ? null : RoundTrip.switchTargetsAt(instruction.startOffset);
    return targets == null ? -1 : targets[0];
  }

  /**
   * The offset of the jump that proves this arm ended in a {@code break;}, or -1. The arm's own
   * tail jump carries the proof for a printed body; an arm with no statements at all compiles its
   * {@code break;} to a jump the case label lands on, kept because a later group still follows.
   */
  private int armBreakJump(Statement stat, List<StatEdge> edges, int switchEnd) {
    if (switchEnd < 0 || !RoundTrip.selector("switchbreak")) {
      return -1;
    }
    int end = RoundTrip.tailJumpOffset(stat);
    if (end >= 0) {
      return RoundTrip.jumpTargetAt(end) == switchEnd ? end : -1;
    }
    if (!RoundTrip.selector("switchempty") || RoundTrip.firstOffset(stat) >= 0) {
      return -1;
    }
    SwitchInstruction instruction = switchInstruction();
    int[] targets = instruction == null ? null : RoundTrip.switchTargetsAt(instruction.startOffset);
    if (targets == null || edges.isEmpty()) {
      return -1;
    }
    List<StatEdge> successors = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    int jump = -1;
    for (StatEdge edge : edges) {
      int index = successors.indexOf(edge);
      if (index < 0 || index >= targets.length) {
        return -1;
      }
      int target = targets[index];
      if (RoundTrip.jumpTargetAt(target) != switchEnd || (jump >= 0 && jump != target)) {
        return -1;
      }
      jump = target;
    }
    return jump;
  }

  /** True when a local this arm declares at its own level is still in scope at {@code offset}. */
  private static boolean declaredScopePast(List<int[]> rows, int offset) {
    if (offset < 0) {
      return false;
    }
    for (int[] row : rows) {
      if (row[2] > offset) {
        return true;
      }
    }
    return false;
  }

  /**
   * Collects the local names this arm declares at its own level. A name declared inside a loop or
   * a nested block lives in that construct's scope whether or not the arm is braced, so it can
   * share a name with another arm and says nothing about the switch's block.
   */
  private static void collectCaseNames(Statement stat, Set<String> names) {
    addDefinitionNames(stat.getVarDefinitions(), names);
    if (stat.getExprents() != null) {
      addDefinitionNames(stat.getExprents(), names);
    }
    if (stat instanceof SequenceStatement) {
      for (Statement child : stat.getStats()) {
        collectCaseNames(child, names);
      }
    } else if (stat instanceof IfStatement ifStat) {
      collectCaseNames(ifStat.getFirst(), names);
    }
  }

  private static void addDefinitionNames(List<? extends Exprent> exprents, Set<String> names) {
    for (Exprent exprent : exprents) {
      if (exprent == null) {
        continue;
      }
      for (Exprent nested : exprent.getAllExprents(true, true)) {
        if (nested instanceof VarExprent var && var.isDefinition()) {
          String name = var.getName();
          if (name != null) {
            names.add(name);
          }
        }
      }
    }
  }

  /**
   * The offset of the block this arm's labels enter. The switch instruction's targets name it even
   * when the arm prints no statement of its own: a dummy arm's range is empty, so its line would
   * read as the method's first one. Falls back to the statement's range when the table cannot say.
   */
  private int entryOffset(int index) {
    List<StatEdge> edges = index < caseEdges.size() ? caseEdges.get(index) : null;
    SwitchInstruction instruction = switchInstruction();
    int[] targets = instruction == null ? null : RoundTrip.switchTargetsAt(instruction.startOffset);
    if (edges != null && !edges.isEmpty() && targets != null) {
      List<StatEdge> successors = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
      int entry = -1;
      for (StatEdge edge : edges) {
        int at = successors.indexOf(edge);
        if (at < 0 || at >= targets.length) {
          entry = -1;
          break;
        }
        if (entry < 0 || targets[at] < entry) {
          entry = targets[at];
        }
      }
      if (entry >= 0) {
        return entry;
      }
    }
    StartEndPair range = caseStatements.get(index).getStartEndRange();
    return range == null ? -1 : range.start;
  }

  /**
   * Whether the arms' line-table spans run forward in this order. The printed output can only
   * push a line down, so an arm whose recorded body ends on a line past the next arm's start
   * cannot be laid out in this sequence: something the source wrote after the switch was glued
   * onto it. An arm that records no span at all puts nothing in the way.
   */
  private boolean spansRunForward(List<Integer> sorted, StructLineNumberTableAttribute table, int switchEnd) {
    int previous = -1;
    int join = switchEnd >= 0 ? switchEnd : switchEndFromJumps();
    for (int i : sorted) {
      Statement stat = caseStatements.get(i);
      int first = RoundTrip.firstOffset(stat);
      int last = RoundTrip.lastOffset(stat);
      // An arm whose block is the join holds none of its own statements: what it records was
      // written after the switch and says nothing about the arm's place in the source.
      if (join >= 0 && first == join) {
        continue;
      }
      if (first < 0 || last < first) {
        continue;
      }
      int firstLine = table.findLineNumber(first);
      int lastLine = table.findLineNumber(last);
      if (firstLine < 0 || lastLine < 0) {
        continue;
      }
      if (previous >= 0 && firstLine < previous) {
        return false;
      }
      previous = Math.max(previous, lastLine);
    }
    return true;
  }

  /**
   * The order the original source wrote the case bodies in. A switch instruction sorts its labels
   * by value, so the bytecode cannot tell `case 40964:` before `case 40963:`; the target's line
   * table can, because every body's first instruction carries the line of the statement behind it.
   * The same holds for an enum label recovered from a synthetic map: its group's block sits where
   * the source wrote it even though the table key is not the label.
   */
  private List<Integer> sourceOrder(int switchEnd) {
    int size = caseStatements.size();
    List<Integer> order = new ArrayList<>(size);
    for (int i = 0; i < size; i++) {
      order.add(i);
    }
    boolean debugSwitch = System.getenv("NEUROFLOWER_SWITCH_DEBUG") != null;
    if (debugSwitch) {
      System.err.println("switch order called size=" + size + " option="
        + DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_SWITCH_ORDER));
    }
    if (size < 2 || !DecompilerContext.getOption(IFernflowerPreferences.ROUND_TRIP_SWITCH_ORDER)) {
      return order;
    }
    // The target's arm blocks record the source order directly when the switch instruction's keys
    // are the labels themselves: a plain int switch or a direct ordinal switch. A `$SwitchMap`
    // enum switch keys its table with synthetic numbers and a string switch keys it with hashes,
    // so there the keys prove nothing and the line table below decides.
    List<Integer> byOffset = offsetOrder();
    if (byOffset != null) {
      return byOffset;
    }
    // Pattern labels, guards and `case null` have ordering rules of their own; a constant or an
    // enum field is a label whose group the source may have written in any order.
    if (isPattern() || caseValues.stream().flatMap(List::stream)
        .anyMatch(v -> v != null && !labelOrdersByLine(v))) {
      return order;
    }
    StructMethod method = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    if (method == null) {
      return order;
    }
    StructLineNumberTableAttribute table =
      method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    if (table == null) {
      return order;
    }
    int[] lines = new int[size];
    for (int i = 0; i < size; i++) {
      Statement stat = caseStatements.get(i);
      if (stat == null) {
        return order;
      }
      int line = table.findLineNumber(entryOffset(i));
      if (line < 0) {
        if (System.getenv("NEUROFLOWER_SWITCH_DEBUG") != null) {
          System.err.println("switch order skipped, line " + line + " case " + i + " of " + size);
        }
        return order;
      }
      lines[i] = line;
    }
    order.sort(Comparator.comparingInt(i -> lines[i]));
    // The line alignment only ever pushes a printed line down, so the sorted order has to run
    // forward in the target's own spans too: an arm whose recorded body ends past the next arm's
    // first line cannot be laid out where it would now print. That happens when the tree glued a
    // statement the source wrote after the whole switch — a lambda's tail return, say — onto a
    // group, and the written order is then not one this printer can reproduce.
    if (!spansRunForward(order, table, switchEnd)) {
      if (System.getenv("NEUROFLOWER_SWITCH_DEBUG") != null) {
        System.err.println("switch order spans overlap " + method.getName() + method.getDescriptor()
          + " lines " + java.util.Arrays.toString(lines) + " -> " + order);
      }
      List<Integer> unchanged = new ArrayList<>(size);
      for (int i = 0; i < size; i++) {
        unchanged.add(i);
      }
      return unchanged;
    }
    if (System.getenv("NEUROFLOWER_SWITCH_DEBUG") != null) {
      System.err.println("switch order " + method.getName() + method.getDescriptor() + " lines "
        + java.util.Arrays.toString(lines) + " -> " + order);
    }
    return order;
  }

  /**
   * The arm order the target's switch instruction records, or null when its layout does not record
   * one. Javac lays the arm blocks out in source order, and when every table key is the case label
   * itself (a plain int switch, or an enum switched directly on its ordinal) the block offsets are
   * the source order. A shared default, a label whose key is not the label, or an arm with no
   * instruction of its own makes the offsets unusable.
   */
  private List<Integer> offsetOrder() {
    int size = caseStatements.size();
    if (!(first instanceof BasicBlockStatement head)
      || !(head.getBlock().getLastInstruction() instanceof SwitchInstruction instruction)) {
      return null;
    }
    List<StatEdge> successors = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    int[] keys = instruction.getValues();
    int[] offsets = new int[size];
    int defaultIndex = -1;
    for (int i = 0; i < size; i++) {
      Statement stat = caseStatements.get(i);
      if (stat == null) {
        return null;
      }
      List<StatEdge> edges = caseEdges.get(i);
      List<Exprent> values = caseValues.get(i);
      for (int j = 0; j < edges.size(); j++) {
        StatEdge edge = edges.get(j);
        int index = successors.indexOf(edge);
        if (index < 0) {
          return null;
        }
        if (edge == defaultEdge) {
          if (edges.size() > 1 || defaultIndex >= 0) {
            return null;
          }
          defaultIndex = i;
          continue;
        }
        Exprent value = j < values.size() ? values.get(j) : null;
        if (index == 0 || index - 1 >= keys.length || value == null || !labelIsKey(value, keys[index - 1])) {
          return null;
        }
      }
      offsets[i] = RoundTrip.firstOffset(stat);
      if (offsets[i] < 0) {
        return null;
      }
    }

    List<Integer> order = new ArrayList<>(size);
    for (int i = 0; i < size; i++) {
      order.add(i);
    }
    order.sort(Comparator.comparingInt(i -> offsets[i]));
    for (int i = 1; i < size; i++) {
      if (offsets[order.get(i - 1)] == offsets[order.get(i)]) {
        return null;
      }
    }
    return order;
  }

  /**
   * Whether this case label's arm order is the one the class file records: a constant, or the
   * static field an enum switch was recovered to. Either way javac laid the group's block out
   * where the source wrote it, so the line table orders it. A `case null` label or a pattern
   * label follows rules of its own and stays in the key order.
   */
  private static boolean labelOrdersByLine(Exprent value) {
    if (value instanceof ConstExprent constant) {
      return !constant.isNull();
    }
    return value instanceof FieldExprent field && field.isStatic();
  }

  /** Whether a printed case label names the switch instruction's key at that position. */
  private static boolean labelIsKey(Exprent value, int key) {
    if (value instanceof ConstExprent constant) {
      return constant.getConstType().typeFamily == TypeFamily.INTEGER && constant.getIntValue() == key;
    }
    if (value instanceof FieldExprent field && field.isStatic()) {
      StructClass owner = DecompilerContext.getStructContext().getClass(field.getClassname());
      if (owner == null || !owner.hasModifier(CodeConstants.ACC_ENUM)) {
        return false;
      }
      int ordinal = 0;
      for (StructField member : owner.getFields()) {
        if (!member.hasModifier(CodeConstants.ACC_ENUM)) {
          continue;
        }
        if (member.getName().equals(field.getName())) {
          return ordinal == key;
        }
        ordinal++;
      }
    }
    return false;
  }

  @Override
  public void initExprents() {
    SwitchHeadExprent swexpr = (SwitchHeadExprent)first.getExprents().remove(first.getExprents().size() - 1);
    swexpr.setCaseValues(caseValues);

    headexprent.set(0, swexpr);
  }

  @Override
  public List<Exprent> getStatExprents() {
    List<Exprent> lst = new ArrayList<>(headexprent);
    // make sure guards can be simplified by other helpers
    for (Exprent caseGuard : getCaseGuards()) {
      if (caseGuard != null) {
        lst.add(caseGuard);
      }
    }

    for (List<Exprent> caseList : this.caseValues) {
      for (Exprent exp : caseList) {
        if (exp != null) {
          lst.add(exp);
        }
      }
    }

    return lst;
  }

  // Returns true if this switch is a pattern matching switch.
  public boolean isPattern() {
    // Simple test, if there's a guard then it is for sure pattern matching
    if (!this.caseGuards.isEmpty()) {
      return true;
    }

    for (List<Exprent> l : this.caseValues) {
      for (Exprent e : l) {
        // If we have instanceofs in our case values, we're a pattern matching switch
        if (e instanceof FunctionExprent && ((FunctionExprent)e).getFuncType() == FunctionType.INSTANCEOF) {
          return true;
        }
      }
    }

    return false;
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>();

    List<Exprent> caseList = this.caseValues.stream()
      .flatMap(List::stream) // List<List<Exprent>> -> List<Exprent>
      .collect(Collectors.toList());
    // guards can also contain pattern variables
    caseList.addAll(this.caseGuards);
    // guards may also contain nested variables, like `a instanceof B b && b == ...`
    caseList = caseList.stream()
      .filter(Objects::nonNull)
      .flatMap(x -> x.getAllExprents(true, true).stream())
      .collect(Collectors.toList());

    for (Exprent caseContent : caseList) {
      if (caseContent == null) {
        continue;
      }

      if (caseContent instanceof FunctionExprent func) {

        // Pattern match variable is implicitly defined
        if (func.getFuncType() == FunctionType.INSTANCEOF && func.getLstOperands().size() > 2) {
          vars.addAll(((Pattern) func.getLstOperands().get(2)).getPatternVars());
        }
      }
    }

    return vars;
  }

  @Override
  public void replaceExprent(Exprent oldexpr, Exprent newexpr) {
    if (headexprent.get(0) == oldexpr) {
      headexprent.set(0, newexpr);
    } else {
      int idx = caseGuards.indexOf(oldexpr);
      if (idx > -1) {
        caseGuards.set(idx, newexpr);
      }
    }
  }

  @Override
  public void replaceStatement(Statement oldstat, Statement newstat) {

    boolean changedAny = false;
    for (int i = 0; i < caseStatements.size(); i++) {
      if (caseStatements.get(i) == oldstat) {
        caseStatements.set(i, newstat);
        changedAny = true;
      }
    }

    ValidationHelper.assertTrue(changedAny, "Replaced statement in switch without changing any case statements!");

    super.replaceStatement(oldstat, newstat);
  }

  @Override
  public Statement getSimpleCopy() {
    return new SwitchStatement();
  }

  @Override
  public void initSimpleCopy() {
    first = stats.get(0);
    defaultEdge = first.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL).get(0);

    sortEdgesAndNodes();
  }

  @Override
  public StartEndPair getStartEndRange() {
    StartEndPair[] sepairs = new StartEndPair[caseStatements.size() + 1];
    int i = 0;
    sepairs[i++] = super.getStartEndRange();
    for (Statement st : caseStatements) {
      sepairs[i++] = st.getStartEndRange();
    }
    return StartEndPair.join(sepairs);
  }

  // *****************************************************************************
  // private methods
  // *****************************************************************************

  public void sortEdgesAndNodes() {

    // skip for pattern switches
    if (caseValues.stream().flatMap(Collection::stream).anyMatch(u -> !(u instanceof ConstExprent) || ((ConstExprent) u).isNull())
      || caseGuards.stream().anyMatch(Objects::nonNull)) {
      return;
    }

    HashMap<StatEdge, Integer> mapEdgeIndex = new HashMap<>();

    List<StatEdge> lstFirstSuccs = first.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    for (int i = 0; i < lstFirstSuccs.size(); i++) {
      mapEdgeIndex.put(lstFirstSuccs.get(i), i == 0 ? lstFirstSuccs.size() : i);
    }

    // case values
    BasicBlockStatement bbstat = (BasicBlockStatement)first;
    int[] values = ((SwitchInstruction)bbstat.getBlock().getLastInstruction()).getValues();

    List<Statement> nodes = new ArrayList<>(stats.size() - 1);
    List<List<Integer>> edges = new ArrayList<>(stats.size() - 1);

    // collect regular edges
    for (int i = 1; i < stats.size(); i++) {

      Statement stat = stats.get(i);

      List<Integer> lst = new ArrayList<>();
      for (StatEdge edge : stat.getPredecessorEdges(StatEdge.TYPE_REGULAR)) {
        if (edge.getSource() == first) {
          lst.add(mapEdgeIndex.get(edge));
        }
      }
      Collections.sort(lst);

      nodes.add(stat);
      edges.add(lst);
    }

    // collect exit edges
    List<StatEdge> lstExitEdges = first.getSuccessorEdges(StatEdge.TYPE_BREAK | StatEdge.TYPE_CONTINUE);
    while (!lstExitEdges.isEmpty()) {
      StatEdge edge = lstExitEdges.get(0);

      List<Integer> lst = new ArrayList<>();
      for (int i = lstExitEdges.size() - 1; i >= 0; i--) {
        StatEdge edgeTemp = lstExitEdges.get(i);
        if (edgeTemp.getDestination() == edge.getDestination() && edgeTemp.getType() == edge.getType()) {
          lst.add(mapEdgeIndex.get(edgeTemp));
          lstExitEdges.remove(i);
        }
      }
      Collections.sort(lst);

      nodes.add(null);
      edges.add(lst);
    }

    // sort edges (bubblesort)
    for (int i = 0; i < edges.size() - 1; i++) {
      for (int j = edges.size() - 1; j > i; j--) {
        if (edges.get(j - 1).get(0) > edges.get(j).get(0)) {
          edges.set(j, edges.set(j - 1, edges.get(j)));
          nodes.set(j, nodes.set(j - 1, nodes.get(j)));
        }
      }
    }

    // sort statement cliques
    for (int index = 0; index < nodes.size(); index++) {
      Statement stat = nodes.get(index);

      if (stat != null) {
        HashSet<Statement> setPreds = new HashSet<>(stat.getNeighbours(StatEdge.TYPE_REGULAR, EdgeDirection.BACKWARD));
        setPreds.remove(first);

        if (!setPreds.isEmpty()) {
          Statement pred =
            setPreds.iterator().next(); // assumption: at most one predecessor node besides the head. May not hold true for obfuscated code.
          for (int j = 0; j < nodes.size(); j++) {
            if (j != (index - 1) && nodes.get(j) == pred) {
              nodes.add(j + 1, stat);
              edges.add(j + 1, edges.get(index));

              if (j > index) {
                nodes.remove(index);
                edges.remove(index);
                index--;
              }
              else {
                nodes.remove(index + 1);
                edges.remove(index + 1);
              }
              break;
            }
          }
        }
      }
    }

    // translate indices back into edges
    List<List<StatEdge>> lstEdges = new ArrayList<>(edges.size());
    List<List<Exprent>> lstValues = new ArrayList<>(edges.size());

    for (List<Integer> lst : edges) {
      List<StatEdge> lste = new ArrayList<>(lst.size());
      List<Exprent> lstv = new ArrayList<>(lst.size());

      List<StatEdge> lstSuccs = first.getSuccessorEdges(STATEDGE_DIRECT_ALL);
      for (Integer in : lst) {
        int index = in == lstSuccs.size() ? 0 : in;

        lste.add(lstSuccs.get(index));
        lstv.add(index == 0 ? null : new ConstExprent(values[index - 1], false, null));
      }
      lstEdges.add(lste);
      lstValues.add(lstv);
    }

    // replace null statements with dummy basic blocks
    for (int i = 0; i < nodes.size(); i++) {
      if (nodes.get(i) == null) {
        BasicBlockStatement bstat = BasicBlockStatement.create();

        StatEdge sample_edge = lstEdges.get(i).get(0);

        bstat.addSuccessor(new StatEdge(sample_edge.getType(), bstat, sample_edge.getDestination(), sample_edge.closure));

        for (StatEdge edge : lstEdges.get(i)) {

          edge.getSource().changeEdgeType(EdgeDirection.FORWARD, edge, StatEdge.TYPE_REGULAR);
          edge.closure.getLabelEdges().remove(edge);

          edge.getDestination().removePredecessor(edge);
          edge.getSource().changeEdgeNode(EdgeDirection.FORWARD, edge, bstat);
          bstat.addPredecessor(edge);
        }

        nodes.set(i, bstat);
        stats.addWithKey(bstat, bstat.id);
        bstat.setParent(this);
      }
    }

    caseStatements = nodes;
    caseEdges = lstEdges;
    caseValues = lstValues;
  }

  @Override
  public boolean hasBasicSuccEdge() {
    // FIXME: default switch

    return false;
  }

  @Override
  protected void onNodeCollapse() {
    // special case switch, sorting edges and nodes
    sortEdgesAndNodes();
  }

  public List<Exprent> getHeadexprentList() {
    return headexprent;
  }

  public Exprent getHeadexprent() {
    return headexprent.get(0);
  }

  public List<List<StatEdge>> getCaseEdges() {
    return caseEdges;
  }

  public List<Statement> getCaseStatements() {
    return caseStatements;
  }

  public @Nullable StatEdge getDefaultEdge() {
    return defaultEdge;
  }

  public List<List<Exprent>> getCaseValues() {
    return caseValues;
  }

  public List<Exprent> getCaseGuards() {
    return caseGuards;
  }

  public void scopeCaseStatement(Statement stat) {
    if (!this.getCaseStatements().contains(stat)) {
      throw new IllegalStateException("Tried to scope a case statement that isn't in the switch!");
    }

    this.scopedCaseStatements.add(stat);
  }

  public void setDefaultEdge(StatEdge edge) {
    this.defaultEdge = edge;
  }

  public Optional<Statement> getDefaultCase() {
    StatEdge defaultEdge = this.getDefaultEdge();
    return defaultEdge != null ? Optional.of(defaultEdge.getDestination()) : Optional.empty();
  }

  /**
   * Replaces the default case if it exists. Adds a new default case to the switch if it doesn't exist.
   * @param stat the case statement to be linked to
   */
  public void setDefaultCase(Statement stat) {
    Optional<Statement> defaultCase = this.getDefaultCase();
    if (defaultCase.isPresent()) {
      defaultCase.get().replaceWith(stat);
      return;
    }

    this.addCaseInternal(0, Collections.singletonList(null), stat);
  }

  /**
   * Adds a new case to the switch.
   * @param values the list of non-null exprents to use as case values
   * @param stat the case statement to be linked to
   */
  public void addCase(List<Exprent> values, Statement stat) {
    int caseCount = this.getCaseStatements().size();
    this.addCaseInternal(this.getDefaultEdge() != null ? caseCount - 1 : caseCount, values, stat);
  }

  /**
   * Adds a new case to the switch.
   * @param index the index of where the case should be added
   * @param values the list of exprents to use as case values
   * @param stat the case statement to be linked to
   */
  public void addCase(int index, List<Exprent> values, Statement stat) {
    this.addCaseInternal(index, values, stat);
  }

  private void addCaseInternal(int index, List<@Nullable Exprent> values, Statement stat) {
    // Basichead is always the first stat
    this.getStats().addWithKeyAndIndex(1 + index, stat, stat.id);
    this.getCaseStatements().add(index, stat);
    this.getCaseValues().add(index, values);

    // If it's a default case, or a regular case
    if (values.size() == 1 && values.get(0) == null) {
      StatEdge edge = new StatEdge(StatEdge.TYPE_REGULAR, this.getBasichead(), stat);
      this.getCaseEdges().add(index, List.of(edge));
      this.setDefaultEdge(edge);
    } else {
      ArrayList<StatEdge> newCaseEdgeLst = new ArrayList<>();
      for (int i = 0; i < values.size(); i++) {
        StatEdge edge = new StatEdge(StatEdge.TYPE_REGULAR, this.getBasichead(), stat);
        newCaseEdgeLst.add(i, edge);

        this.getBasichead().addSuccessor(edge);
      }

      this.getCaseEdges().add(index, newCaseEdgeLst);
    }

    stat.setParent(this);
  }

  /**
   * Removes a case from the switch statement. This includes the case statement, values, and edges.
   * You should NOT manually handle stats/values/edges if you are calling this method.
   * @param stat the case statement to remove
   */
  public void removeCase(Statement stat) {
    int index = this.caseStatements.indexOf(stat);
    if (index == -1) {
      throw new IllegalStateException("Tried to remove a case statement that isn't in the switch!");
    }

    this.removeCase(index);
  }

  /**
   * Removes a case from the switch statement. This includes the case statement, values, and edges.
   * You should NOT manually handle stats/values/edges if you are calling this method.
   * @param index the index of the case to remove
   */
  public void removeCase(int index) {
    Statement stat = this.getCaseStatements().get(index);
    stat.getAllPredecessorEdges().forEach(StatEdge::remove);
    stat.getAllSuccessorEdges().forEach(StatEdge::remove);

    this.getStats().removeWithKey(stat.id);
    this.getCaseStatements().remove(index);
    this.getCaseValues().remove(index);
    this.getCaseEdges().get(index).forEach(StatEdge::remove);
    this.getCaseEdges().remove(index);
  }
}

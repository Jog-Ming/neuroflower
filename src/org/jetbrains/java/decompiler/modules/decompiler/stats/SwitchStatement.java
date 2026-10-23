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
      collectCaseNames(caseStat, names, null);
      for (String name : names) {
        definitions.computeIfAbsent(name, key -> new ArrayList<>()).add(caseStat);
      }
    }
    for (List<Statement> arms : definitions.values()) {
      if (arms.size() > 1) {
        braced.addAll(arms);
      }
    }

    VarType switch_type = headexprent.get(0).getExprType();

    for (int i : sourceOrder()) {

      Statement stat = caseStatements.get(i);
      List<StatEdge> edges = caseEdges.get(i);
      List<Exprent> values = caseValues.get(i);
      Exprent guard = caseGuards.size() > i ? caseGuards.get(i) : null;

      for (int j = 0; j < edges.size(); j++) {
        if (edges.get(j) == defaultEdge) {
          buf.appendIndent(indent + 1).append("default:");
          if (braced.contains(stat) && j == edges.size() - 1) {
            buf.append(" {");
          }

          buf.appendLineSeparator();
        } else {
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

      buf.append(ExprProcessor.jmpWrapper(stat, indent + 2, false));

      if (braced.contains(stat)) {
        buf.appendIndent(indent + 1);
        buf.append("}");
        buf.appendLineSeparator();
      }
    }

    buf.appendIndent(indent).append("}").appendLineSeparator();

    if (this.isPhantom()) {
      buf.append("*/");
    }

    return buf;
  }

  /**
   * The order the original source wrote the case bodies in. A switch instruction sorts its labels
   * by value, so the bytecode cannot tell `case 40964:` before `case 40963:`; the target's line
   * table can, because every body's first instruction carries the line of the statement behind it.
   */
  private static void collectCaseNames(Statement stat, Set<String> names, SwitchStatement inner) {
    if (stat instanceof SwitchStatement) {
      inner = (SwitchStatement) stat; // an inner switch scopes its own arms
    }
    if (inner == null) {
      if (stat.getExprents() != null) {
        for (Exprent exprent : stat.getExprents()) {
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
    }
    for (Statement child : stat.getStats()) {
      collectCaseNames(child, names, inner);
    }
  }

  private List<Integer> sourceOrder() {
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
    // so there the labels prove nothing; those switches and pattern switches stay untouched.
    List<Integer> byOffset = offsetOrder();
    if (byOffset != null) {
      return byOffset;
    }
    // Pattern labels, guards and `case null` have ordering rules of their own; only a plain
    // constant switch may be written in an order the switch instruction does not define.
    if (isPattern() || caseValues.stream().flatMap(List::stream)
        .anyMatch(v -> v != null && (!(v instanceof ConstExprent) || ((ConstExprent)v).isNull()))) {
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
      StartEndPair range = stat.getStartEndRange();
      int line = range == null ? -1 : table.findLineNumber(range.start);
      if (line < 0) {
        if (System.getenv("NEUROFLOWER_SWITCH_DEBUG") != null) {
          System.err.println("switch order skipped, line " + line + " case " + i + " of " + size);
        }
        return order;
      }
      lines[i] = line;
    }
    order.sort(Comparator.comparingInt(i -> lines[i]));
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

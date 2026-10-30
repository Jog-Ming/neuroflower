package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.struct.StructClass;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TryHelper {
  public static boolean enhanceTryStats(RootStatement root, StructClass cl) {
    boolean ret = makeTryWithResourceRec(cl, root);

    if (ret) {
      SequenceHelper.condenseSequences(root);
    }

    if (mergeTrys(root)) {
      SequenceHelper.condenseSequences(root);

      ret = true;
    }

    return ret;
  }

  private static boolean makeTryWithResourceRec(StructClass cl, Statement stat) {
      boolean ret = false;

      if (cl.getVersion().hasNewTryWithResources() && stat instanceof CatchStatement trySt) {
        if (TryWithResourcesProcessor.makeTryWithResourceJ11(trySt)) {
          ret = true;
        }
      } else if (stat instanceof CatchAllStatement trySt && trySt.isFinally()) {
        if (TryWithResourcesProcessor.makeTryWithResource(trySt)) {
          ret = true;
        }
      }

      for (Statement st : new ArrayList<>(stat.getStats())) {
        if (makeTryWithResourceRec(cl, st)) {
          ret = true;
        }
      }

      return ret;
  }

  private static boolean mergeTrys(Statement root) {
    boolean ret = false;

    if (root instanceof CatchStatement) {
      if (mergeTry((CatchStatement) root)) {
        ret = true;
      }
    }

    for (Statement stat : new ArrayList<>(root.getStats())) {
      ret |= mergeTrys(stat);
    }

    return ret;
  }

  // J11+
  // Merges try with resource statements that are nested within each other, as well as try with resources statements nested in a normal try.
  private static boolean mergeTry(CatchStatement stat) {
    if (stat.getStats().isEmpty()) {
      return false;
    }

    // Get the statement inside of the current try
    Statement inner = stat.getStats().get(0);

    // If the inside is a sequence, check the first of the sequence, which can happen for J8 try with resources due to
    // finally return behavior. Don't do this if there are non-exit breaks coming out of the statement.
    Set<StatEdge> edges = new HashSet<>();
    TryWithResourcesProcessor.findEdgesLeaving(stat, inner, edges);
    Statement parent = stat;
    if (inner instanceof SequenceStatement && edges.isEmpty()) {
      // Two resource trials merged into one header: a statement beside the inner try then lies
      // between the two close blocks, where the inner resource is already closed, and the
      // merged header would move it inside the inner scope. javac only nests resources without
      // siblings for one header's list. A try without resources of its own is the shell the
      // printer lifts a nested try-with-resources into, and its siblings belong inside.
      if (!stat.getResources().isEmpty() && inner.getStats().size() > 1) {
        return false;
      }
      // A sibling that starts where the nested resource's scope ended runs after the source
      // closed it: the table's row for the resource says where that block closed, and merging
      // would print the sibling inside the resource's scope. The rest of the enclosing try stays
      // outside, as in GlDevice's hidden-window context and the GL capabilities read after it.
      if (siblingAfterResourceScope(inner)) {
        return false;
      }
      parent = inner;
      inner = inner.getStats().get(0);
    }

    // Check if the inner statement is a try statement
    if (inner instanceof CatchStatement) {
      // Filter on try with resources statements
      List<Exprent> resources = ((CatchStatement) inner).getResources();
      if (!resources.isEmpty()) {
        // One try inside of the catch

        // Only merge try statements without catches, otherwise we might produce invalid code
        if (inner.getStats().size() == 1) {
          // Set the outer try to be resources, and initialize
          stat.getResources().addAll(resources);
          stat.getVarDefinitions().addAll(inner.getVarDefinitions());

          // Get inner block of inner try stat
          Statement innerBlock = inner.getStats().get(0);

          // Remove successors as the replaceStatement call will add the appropriate successor
          List<StatEdge> innerEdges = inner.getAllSuccessorEdges();
          for (StatEdge succ : innerBlock.getAllSuccessorEdges()) {
            boolean found = false;
            for (StatEdge innerEdge : innerEdges) {
              if (succ.getDestination() == innerEdge.getDestination()) {
                found = true;
                break;
              }
            }

            if (found) {
              innerBlock.removeSuccessor(succ);
            }
          }

          // Replace the inner try statement with the block inside
          parent.replaceStatement(inner, innerBlock);

          return true;
        }
      }
    }

    return false;
  }

  /**
   * Whether a statement beside the nested try runs after the nested resource's scope ended. The
   * resource variable's table row ends where the source closed the resource; a sibling that
   * starts at or after that offset belongs to the enclosing try, not to the resource's block.
   * Only a declared resource carries the row; without one there is no offset evidence.
   */
  private static boolean siblingAfterResourceScope(Statement sequence) {
    List<Statement> stats = sequence.getStats();
    if (stats.size() < 2 || !(stats.get(0) instanceof CatchStatement nested)
        || nested.getResources().isEmpty()) {
      return false;
    }
    int scopeEnd = -1;
    for (Exprent resource : nested.getResources()) {
      if (resource instanceof AssignmentExprent assignment
          && assignment.getLeft() instanceof VarExprent var && var.getLVT() != null) {
        scopeEnd = Math.max(scopeEnd, var.getLVT().getEnd());
      }
    }
    if (scopeEnd < 0) {
      return false;
    }
    for (int i = 1; i < stats.size(); i++) {
      int start = RoundTrip.firstOffset(stats.get(i));
      if (start >= 0 && start >= scopeEnd) {
        return true;
      }
    }
    return false;
  }
}

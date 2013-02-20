package edu.colorado.thresher;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.AbstractNumberedGraph;
import com.ibm.wala.util.graph.NumberedEdgeManager;
import com.ibm.wala.util.graph.NumberedGraph;
import com.ibm.wala.util.graph.NumberedNodeManager;
import com.ibm.wala.util.intset.BasicNaturalRelation;
import com.ibm.wala.util.intset.IBinaryNaturalRelation;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.MutableSparseIntSet;

public class MySubGraph<T> extends AbstractNumberedGraph<T> {

  private final NumberedGraph<T> delegate;

  // p -> q pairs to ignore
  private final IBinaryNaturalRelation ignoreEdges;

  // WALA encodes p ->{f} q as p -> f -> q. it's not correct to remove edges p
  // -> f and f -> q. instead, we must say that
  // if p -> f, then f does not point to q
  // private final IBinaryNaturalRelation ignoreIfBoth;

  private final Edges edges;

  public MySubGraph(NumberedGraph<T> delegate) {
    super();
    this.delegate = delegate;
    this.edges = new Edges();

    this.ignoreEdges = new BasicNaturalRelation();
    // this.ignoreIfBoth = new BasicNaturalRelation();
  }

  public void addIgnoreEdge(T src, T snk, NumberedGraph<T> g) {
    this.ignoreEdges.add(g.getNumber(src), g.getNumber(snk));
  }

  /*
   * public void addIgnoreIfBoth(T src, T field, T snk, NumberedGraph<T> g) {
   * this.ignoreIfBoth.add(g.getNumber(src), g.getNumber(field));
   * this.ignoreIfBoth.add(g.getNumber(field), g.getNumber(snk)); }
   */

  @Override
  protected NumberedEdgeManager<T> getEdgeManager() {
    return edges;
  }

  private final class Edges implements NumberedEdgeManager<T> {

    private T lastNode;

    public void addEdge(T src, T dst) {
      Assertions.UNREACHABLE();
    }

    public int getPredNodeCount(T N) {
      Assertions.UNREACHABLE();
      return 0;
    }

    public Iterator<T> getPredNodes(T N) {
      Assertions.UNREACHABLE();
      return null;
    }

    public int getSuccNodeCount(T N) {
      Assertions.UNREACHABLE();
      return 0;
    }

    public Iterator<T> getSuccNodes(T N) {
      Iterator<T> iter = delegate.getSuccNodes(N);
      int srcNum = getNumber(N);
      List<T> result = new LinkedList<T>();
      while (iter.hasNext()) {
        T next = iter.next();
        // System.err.println("edge " + N + " " + srcNum + "  -> " + next + " "
        // + getNumber(next));
        // System.err.println(srcNum + "  -> " + getNumber(next));

        /*
         * if (this.lastNode != null) { if
         * (ignoreIfBoth.contains(getNumber(lastNode), srcNum) &&
         * ignoreIfBoth.contains(srcNum, getNumber(next))) {
         * System.err.println("ignore if both: ignoring edge " + lastNode +
         * " -> " + N + " -> " + next); Util.Assert(false, "ignore if both!");
         * continue; } }
         */

        if (!ignoreEdges.contains(srcNum, getNumber(next))) {
          result.add(next);
        } else {
          // System.err.println("ignoring edge " + N + " " + next);
        }
      }
      lastNode = N;
      return result.iterator();
    }

    public boolean hasEdge(T src, T dst) {
      Assertions.UNREACHABLE();
      return false;
    }

    public void removeAllIncidentEdges(T node) throws UnsupportedOperationException {
      Assertions.UNREACHABLE();
    }

    public void removeEdge(T src, T dst) throws UnsupportedOperationException {
      Assertions.UNREACHABLE();
    }

    public void removeIncomingEdges(T node) throws UnsupportedOperationException {
      Assertions.UNREACHABLE();
    }

    public void removeOutgoingEdges(T node) throws UnsupportedOperationException {
      Assertions.UNREACHABLE();
    }

    public IntSet getPredNodeNumbers(T node) {
      IntSet s = delegate.getPredNodeNumbers(node);
      MutableIntSet result = MutableSparseIntSet.makeEmpty();
      for (IntIterator it = s.intIterator(); it.hasNext();) {
        int y = it.next();
        if (!ignoreEdges.contains(y, getNumber(node))) {
          result.add(y);
        }
      }
      return result;
    }

    public IntSet getSuccNodeNumbers(T node) {
      Assertions.UNREACHABLE();
      return null;
    }

  }

  @Override
  protected NumberedNodeManager<T> getNodeManager() {
    return delegate;
  }
}

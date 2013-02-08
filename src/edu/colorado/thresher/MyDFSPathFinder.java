package edu.colorado.thresher;

import java.util.*;

import com.ibm.wala.util.collections.*;
import com.ibm.wala.util.graph.*;
import com.ibm.wala.util.intset.*;

  /**
   * This class searches depth-first search for node that matches some criteria. If found, it reports a path to the first node found.
   * 
   * This class follows the outNodes of the graph nodes to define the graph, but this behavior can be changed by overriding the
   * getConnected method.
   * 
   * This slightly modified version can also ignore a pair of edges
   */
  public class MyDFSPathFinder<T> extends Stack<T> {
    public static final long serialVersionUID = 9939900773328288L;

    /**
     * Pairs of edges that cannot be used together 
     */
    private IBinaryNaturalRelation ignoreIfBoth;
    private IntSet notAllowed;
    
    /**
     * The graph to search
     */
    protected final NumberedGraph<T> G;

    /**
     * The Filter which defines the target set of nodes to find
     */
    final private Filter<T> filter;

    /**
     * an enumeration of all nodes to search from
     */
    final private Iterator<T> roots;

    /**
     * An iterator of child nodes for each node being searched
     */
    final protected Map<Object, Iterator<? extends T>> pendingChildren = HashMapFactory.make(25);

    /**
     * Flag recording whether initialization has happened.
     */
    private boolean initialized = false;


    
    /**
     * Construct a depth-first enumerator starting with a particular node in a directed graph.
     * 
     * @param G the graph whose nodes to enumerate
     * @throws IllegalArgumentException if G is null
     */
    public MyDFSPathFinder(NumberedGraph<T> G, T N, Filter<T> f) throws IllegalArgumentException {
      if (G == null) {
        throw new IllegalArgumentException("G is null");
      }
      if (!G.containsNode(N)) {
        throw new IllegalArgumentException("source node not in graph: " + N);
      }
      this.G = G;
      this.roots = new NonNullSingletonIterator<T>(N);
      this.filter = f;
      this.ignoreIfBoth = new BasicNaturalRelation();
    }

    /**
     * Construct a depth-first enumerator across the (possibly improper) subset of nodes reachable from the nodes in the given
     * enumeration.
     * 
     * @param nodes the set of nodes from which to start searching
     */
    public MyDFSPathFinder(NumberedGraph<T> G, Iterator<T> nodes, Filter<T> f) {
      this.G = G;
      this.roots = nodes;
      this.filter = f;
      if (G == null) {
        throw new IllegalArgumentException("G is null");
      }
      if (roots == null) {
        throw new IllegalArgumentException("roots is null");
      }
      if (filter == null) {
        throw new IllegalArgumentException("filter is null");
      }
      this.ignoreIfBoth = new BasicNaturalRelation();
    }

    private void init() {
      initialized = true;
      notAllowed = null;
      if (roots.hasNext()) {
        T n = roots.next();
        push(n);
        setPendingChildren(n, getConnected(n));
      }
    }

    /**
     * @return a List of nodes that specifies the first path found from a root to a node accepted by the filter. Returns null if no
     *         path found.
     */
    public List<T> find() {
      if (!initialized) {
        init();
      }
      while (hasNext()) {
        T n = peek();
        Util.Debug("NEXT " + n);
        List<T> path = currentPath();
          
        if (filter.accepts(n)) {
          advance();
          return path;
        }
        advance();
      }
      return null;
    }

    protected List<T> currentPath() {
      ArrayList<T> result = new ArrayList<T>();
      for (Iterator<T> path = iterator(); path.hasNext();) {
        result.add(0, path.next());
      }
      return result;
    }

    /**
     * Return whether there are any more nodes left to enumerate.
     * 
     * @return true if there nodes left to enumerate.
     */
    public boolean hasNext() {
      return (!empty());
    }

    /**
     * Method getPendingChildren.
     * 
     * @return Object
     */
    protected Iterator<? extends T> getPendingChildren(T n) {
      return pendingChildren.get(n);
    }

    /**
     * Method setPendingChildren.
     * 
     * @param v
     * @param iterator
     */
    protected void setPendingChildren(T v, Iterator<? extends T> iterator) {
      pendingChildren.put(v, iterator);
    }

    /**
     * Advance to the next graph node in discover time order.
     */
    private void advance() {

      // we always return the top node on the stack.
      T currentNode = peek();

      // compute the next node to return.
      assert getPendingChildren(currentNode) != null;
      do {
        T stackTop = peek();
        for (Iterator<? extends T> it = getPendingChildren(stackTop); it.hasNext();) {
          T child = it.next();
          
          // check for edges that should be excluded
          if (stackTop != null) {
            if (notAllowed != null && notAllowed.contains(G.getNumber(child))) {
              System.err.println("found second ignored edge ending in " + child);
              // edge is second of pair of edges that should be excluded; don't continue along this path
              continue;
            }
            if (ignoreIfBoth.contains(G.getNumber(stackTop), G.getNumber(child))) {
              System.err.println("found first ignored edge " + stackTop + " -> " + child);
              notAllowed = ignoreIfBoth.getRelated(G.getNumber(child));
            }
          }
          
          if (getPendingChildren(child) == null) {
            // found a new child.
            push(child);
            setPendingChildren(child, getConnected(child));
            return;
          }
        }
        // didn't find any new children. pop the stack and try again.
        pop();

      } while (!empty());

      // search for the next unvisited root.
      while (roots.hasNext()) {
        T nextRoot = roots.next();
        if (getPendingChildren(nextRoot) == null) {
          push(nextRoot);
          setPendingChildren(nextRoot, getConnected(nextRoot));
        }
      }

      return;
    }
    
    public void addIgnoreIfBoth(T src, T field, T snk) {
        this.ignoreIfBoth.add(G.getNumber(src), G.getNumber(field));  
        this.ignoreIfBoth.add(G.getNumber(field), G.getNumber(snk));  
    }

    /**
     * get the out edges of a given node
     * 
     * @param n the node of which to get the out edges
     * @return the out edges
     * 
     */
    protected Iterator<? extends T> getConnected(T n) {
      return G.getSuccNodes(n);
    }
    
    public IBinaryNaturalRelation getIgnoreIfBoth() {
    	return ignoreIfBoth;
    }
    
    public void setIgnoreIfBoth(IBinaryNaturalRelation ignoreIfBoth) {
    	this.ignoreIfBoth = ignoreIfBoth;
    }
    
  }


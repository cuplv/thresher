package edu.colorado.thresher;

/*******************************************************************************
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.util.collections.CollectionFilter;
import com.ibm.wala.util.collections.Filter;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.NonNullSingletonIterator;
import com.ibm.wala.util.graph.NumberedGraph;
import com.ibm.wala.util.intset.BasicNaturalRelation;
import com.ibm.wala.util.intset.IBinaryNaturalRelation;
import com.ibm.wala.util.intset.IntSet;

/**
 * This class searches breadth-first for node that matches some criteria. If found, it reports a path to the first node found.
 * 
 * This class follows the outNodes of the graph nodes to define the graph, but this behavior can be changed by overriding the
 * getConnected method.
 * 
 * TODO: if finding many paths, use a dynamic programming algorithm instead of calling this repeatedly.
 */
public class MyBFSPathFinder<T> {

  private final boolean DEBUG = false;

  
  /**
   * Pairs of edges that cannot be used together 
   */
  private IBinaryNaturalRelation ignoreIfBoth;
  private IntSet notAllowed;
  
  /**
   * The graph to search
   */
  final private NumberedGraph<T> G;

  /**
   * The Filter which defines the target set of nodes to find
   */
  final private Filter<T> filter;

  /**
   * an enumeration of all nodes to search from
   */
  final private Iterator<T> roots;

  /**
   * Construct a breadth-first enumerator starting with a particular node in a directed graph.
   * 
   * @param G the graph whose nodes to enumerate
   */
  public MyBFSPathFinder(NumberedGraph<T> G, T N, Filter<T> f) {
    if (G == null) {
      throw new IllegalArgumentException("G is null");
    }
    if (f == null) {
      throw new IllegalArgumentException("null f");
    }
    this.G = G;
    this.roots = new NonNullSingletonIterator<T>(N);
    this.filter = f;
    this.ignoreIfBoth = new BasicNaturalRelation();
  }

  /**
   * Construct a breadth-first enumerator starting with a particular node in a directed graph.
   * 
   * @param G the graph whose nodes to enumerate
   * @throws IllegalArgumentException if G is null
   */
  public MyBFSPathFinder(NumberedGraph<T> G, T src, final T target) throws IllegalArgumentException {
    if (G == null) {
      throw new IllegalArgumentException("G is null");
    }
    this.G = G;
    this.roots = new NonNullSingletonIterator<T>(src);
    if (!G.containsNode(src)) {
      throw new IllegalArgumentException("src is not in graph " + src);
    }
    this.filter = new Filter<T>() {
      public boolean accepts(T o) {
        return target.equals(o);
      }
    };
    this.ignoreIfBoth = new BasicNaturalRelation();
  }

  /**
   * @return a List of nodes that specifies the first path found from a root to a node accepted by the filter. Returns null if no
   *         path found.
   */
  public List<T> find() {

    LinkedList<T> Q = new LinkedList<T>();
    HashMap<Object, T> history = HashMapFactory.make();
    while (roots.hasNext()) {
      T next = roots.next();
      Q.addLast(next);
      history.put(next, null);
    }
    while (!Q.isEmpty()) {
      T N = Q.removeFirst();
      //System.err.println("Node is " + N);
      /*
      // check for edges that should be excluded
      if (notAllowed != null && notAllowed.contains(G.getNumber(N))) {
    	  System.err.println("found second ignored edge ending in " + N);
    	  // edge is second of pair of edges that should be excluded; don't continue along this path
          continue;
      }
      */

      if (DEBUG) {
        System.err.println(("visit " + N));
      }
      if (filter.accepts(N)) {
        return makePath(N, history);
      }
      Iterator<? extends T> children = getConnected(N);
      while (children.hasNext()) {
        T c = children.next();
        /*
        if (ignoreIfBoth.contains(G.getNumber(N), G.getNumber(c))) {
        	System.err.println("found first ignored edge " + N + " -> " + c);
            notAllowed = ignoreIfBoth.getRelated(G.getNumber(c));
        }
        */
        if (!history.containsKey(c)) {
          Q.addLast(c);
          history.put(c, N);
        }
      }
    }

    return null;
  }

  /**
   * @return a List which represents a path in the breadth-first search to Q[i]. Q holds the nodes visited during the BFS, in order.
   */
  private List<T> makePath(T node, Map<Object, T> history) {
    ArrayList<T> result = new ArrayList<T>();
    T n = node;
    result.add(n);
    while (true) {
      T parent = history.get(n);
      if (parent == null)
        return result;
      else {
        result.add(parent);
        n = parent;
      }
    }
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
  
  public void addIgnoreIfBoth(T src, T field, T snk) {
      this.ignoreIfBoth.add(G.getNumber(src), G.getNumber(field));  
      this.ignoreIfBoth.add(G.getNumber(field), G.getNumber(snk));  
  }
}

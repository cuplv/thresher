package edu.colorado.thresher.core;

import java.util.Collection;
import java.util.Iterator;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.util.graph.Graph;

/**
 * publicly accessible methods needed by all symbolic executors
 * 
 * @author sam
 */
public interface ISymbolicExecutor {

  /**
   * perform symbolic execution until query is refuted or witnessed
   * 
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   * @return false if query is refuted on all paths, true otherwise
   */
  public boolean executeBackward(CGNode startNode, IQuery query);

  /**
   * perform symbolic execution until query is refuted or witnessed
   * 
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   * @return false if query is refuted on all paths, true otherwise
   */
  public boolean executeBackward(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query);

  /**
   * perform symbolic execution until query is refuted or witnessed
   * @param path - path to begin execution with
   * @return false if query is refuted on all paths, true otherwise
   */
  public boolean executeBackward(IPathInfo path);

    
  /**
   * main execution loop - keep exploring until no paths are left
   * 
   * @return false if query is refuted on all paths, true otherwise
   */
  boolean executeBackward();

  /**
   * find possible callers for current path and add a new path for each
   * 
   * @param info
   *          - path that has reached a procedure boundary
   * @return - true if a witness has been found, false otherwise
   */
  boolean handleInterproceduralExecution(IPathInfo path);

  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   */
  public void executeForward(CGNode startNode, IQuery query);

  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   */
  public void executeForward(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query);

  /**
   * execute given path until it splits or reaches beginning of procedure.
   * 
   * @return true if procedure boundary is reached, false if path splits
   */
  boolean executeBackwardsPathIntraprocedural(IPathInfo path);

  /**
   * remove and return a path from paths to explore. override to change
   * exploration strategy. default is DFS
   * 
   * @return path removed from pathsToExplore
   */
  IPathInfo selectPath();

  /**
   * exposed to allow the inclusion of heuristics for prioritizing or avoiding
   * the exploration of certain callers default uses no heuristics and simply
   * returns all possible callers according to graph
   */
  Iterator<CGNode> getCallers(IPathInfo path, Graph<CGNode> graph);

  /**
   * add a path to the paths to explore. override to change exploration
   * strategy. default is DFS override to change exploration strategy. default
   * is DFS
   */
  void addPath(IPathInfo path);

  /**
   * override to customize instruction visiting
   * 
   * @return false if instr causes path to become infeasible or split; true
   *         otherwise
   */
  boolean visit(SSAInstruction instr, IPathInfo info);

  /**
   * override to use different kind of PathInfo during execution
   */
  IPathInfo makePath(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query);

  /**
   * @return the names of classes we have synthesized during execution
   */
  public Collection<String> getSynthesizedClasses();
  
}

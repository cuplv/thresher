package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.impl.GraphInverter;
import com.ibm.wala.util.graph.traverse.BFSIterator;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;
import com.ibm.wala.util.graph.traverse.DFS;
import com.ibm.wala.util.intset.BasicNaturalRelation;
import com.ibm.wala.util.intset.OrdinalSet;

/**
 * symbolic executor that prunes the call graph to *only* the call graph
 * relevant to the current constraints at interprocedural boundaries
 * 
 * @author sam
 * 
 */
public class PruningSymbolicExecutor extends OptimizedPathSensitiveSymbolicExecutor {

  // private final Map<Constraint,Set<CGNode>> reachableCache;
  // transitive closure of the "calls" relation
  final Map<CGNode, OrdinalSet<CGNode>> callGraphTransitiveClosure;
  private final Logger logger;

  public PruningSymbolicExecutor(CallGraph callGraph, Logger logger) {
    super(callGraph, logger);
    this.logger = logger;
    callGraphTransitiveClosure = WALACallGraphUtil.getCallGraphTransitiveClosure(callGraph);
  }

  public boolean isCalledByClassInit(CGNode node) {
    return callGraphTransitiveClosure.get(WALACFGUtil.getFakeWorldClinitNode(callGraph)).contains(node);
  }
  
  /*
  @Override
  public Iterator<CGNode> getCallers(IPathInfo path, Graph<CGNode> graph) {
    if (!Options.CALLGRAPH_PRUNING) return this.callGraph.getPredNodes(path.getCurrentNode());
    IPathInfo copy = path.deepCopy();
    CGNode node = copy.getCurrentNode();

    // first, consider special case for when the caller is a class initializer
    Set<CGNode> preds = Util.iteratorToSet(this.callGraph.getPredNodes(node));
    // TODO: what if there are several modifiers and only one is a clinit?
    if (preds.size() == 1) { // &&
                             // preds.iterator().next().getMethod().isClinit())
                             // {
      return preds.iterator();
    }
    // else, caller is not a class init...
    copy.removeAllLocalConstraintsFromQuery(); // eliminate all non-heap
                                               // constraints (constraints on
                                               // function params should be only
                                               // local constraints left)
    Util.Debug("after removing all local" + path);
    if (copy.foundWitness())
      return this.callGraph.getPredNodes(node); // no heap constraints left to
                                                // produce, so can't prune any
                                                // callers

    // compute set of all CGNode's that might affect our query
    Map<Constraint, Set<CGNode>> queryModMap = copy.getModifiersForQuery();
    // TODO: check for class inits in modifiers?
    Set<CGNode> modifiers = Util.flatten(queryModMap.values());

    if (Options.DEBUG)
      for (CGNode nod : modifiers)
        Util.Debug("possible modifier " + nod);

    // return computeReducedCallerSet(queryModMap, preds);
    return computeReducedCallerSet(modifiers, preds);
  }

  private Iterator<CGNode> computeReducedCallerSet(Set<CGNode> modifiers, Set<CGNode> toPrune) {
    // assume everything is reachable from the class inits
    for (CGNode node : modifiers) {
      if (isCalledByClassInit(node)) return toPrune.iterator();
    }
    Set<CGNode> reachable = getReachable(modifiers, toPrune, true);

    // TODO: this is unecessary (could just modify caller list in method call),
    // but want to be explicit about what's pruned
    // if (Options.DEBUG) {
    for (CGNode pruneMe : toPrune) {
      if (!reachable.contains(pruneMe)) {
        Util.Print("pruned " + pruneMe);
        logger.log("prunedCaller");
      }// else Util.Debug("caller " + toPrune + " reachable");
    }
    // }
    toPrune.retainAll(reachable);
    return toPrune.iterator();
  }
  */
  
  
  /**
   * Ask flow-insensitively: can we get from src to snk?
   * @param snk - node we are trying to reach
   * @param src - node we are starting from
   */
  boolean isReachableFrom(CGNode snk, CGNode src) {
    OrdinalSet<CGNode> reachable = callGraphTransitiveClosure.get(src);
    return reachable.contains(snk);
  }

  /**
   * @return true if a path from srcNode to snkNode exists
   */
  boolean feasiblePathExists(CGNode srcNode, ISSABasicBlock srcBlk, CGNode snkNode, ISSABasicBlock snkBlk) {
    Set<ISSABasicBlock> reachableBlks = DFS.getReachableNodes(srcNode.getIR().getControlFlowGraph(), 
        Collections.singleton(srcBlk));
    if (srcNode == snkNode) {
       if (reachableBlks.contains(snkBlk)) return true;
       // TODO: need to look for other calls of srcNode here? in general, yes obviously, but
       // given the usage of this function, there may be some scope issues
    } else {
      Set<CGNode> reachable = HashSetFactory.make();
      for (CGNode callee : WALACFGUtil.getCallTargetsInBlocks(reachableBlks, srcNode, callGraph)) {
        reachable.addAll(OrdinalSet.toCollection(callGraphTransitiveClosure.get(callee)));
      }
      if (reachable.contains(snkNode)) return true;
      reachable = getReachableStartingBackwardsFrom(Collections.singleton(srcNode), 
          Collections.singleton(snkNode), reachable, true);
    }
    return false;
  }

  /**
   * Ask flow-sensitively: can we get from src to snk?
   */
  boolean feasiblePathExists(CGNode src, CGNode snk) {
    if (!Options.CALLGRAPH_PRUNING) return true;
    if (isCalledByClassInit(src)) return true; // assume everything is reachable from the class inits
    Set<CGNode> reachable = getReachable(Collections.singleton(src), Collections.singleton(snk), false);
    return reachable.contains(snk);
  }

  /**
   * @param srcs - seeds for the search
   * @param snks
   *          - nodes we are trying to reach from the search (needed for
   *          optimization)
   * @return - the set of nodes whose entrypoints are reachable from srcs (or a subset 
   *          containing all nodes in snks)
   */
  public Set<CGNode> getReachable(Collection<CGNode> srcs, Set<CGNode> snks, final boolean includeCallers) {
    // all nodes that are completely reachable
    Set<CGNode> reachable = HashSetFactory.make();

    for (CGNode src : srcs) {
      reachable.addAll(OrdinalSet.toCollection(callGraphTransitiveClosure.get(src)));
    }
    if (reachable.containsAll(snks)) return reachable; // early return if we cover everything
    reachable.add(callGraph.getFakeRootNode()); // don't want to model control
                                                // flow among entrypoints
    return getReachableStartingBackwardsFrom(srcs, snks, reachable, includeCallers);
  }
  
  
  Set<CGNode> getReachableStartingBackwardsFrom(Collection<CGNode> srcs, 
                                                Set<CGNode> snks, Set<CGNode> reachable, final boolean includeCallers) {
    // nodes whose entrypoints are reachable, but some callees may not be reachable
    Set<CGNode> partiallyReachable = HashSetFactory.make();
    for (;;) {
      boolean progress = false;
      // callers of a node in srcs that we have yet to explore
      Set<CGNode> frontier = HashSetFactory.make();
      // not all elements of snks are directly reachable
      for (CGNode src : srcs) {
        // for each caller
        for (Iterator<CGNode> callerNodes = callGraph.getPredNodes(src); callerNodes.hasNext();) {
          CGNode caller = callerNodes.next();
          // class inits should be handled separately...
          Util.Assert(!caller.getMethod().isClinit());

          // avoid redundant exploration
          if (reachable.contains(caller)) continue;
          progress = true;
          frontier.add(caller);
          // Manu's optimization; do FI check (using callgraph) on nodes reachable from caller first.
          // if no nodes in toPrune are reachable according to the callgraph, we
          // needn't do the expensive intraprocedural search
          Collection<CGNode> reachableFromCaller = OrdinalSet.toCollection(callGraphTransitiveClosure.get(caller));

          if (Util.intersectionNonEmpty(reachableFromCaller, snks)) {
            partiallyReachable.add(caller);
            Set<ISSABasicBlock> possibleStartBlocks = HashSetFactory.make();
            IR ir = caller.getIR();
            SSACFG cfg = ir.getControlFlowGraph();
            // for each context for the the caller
            for (Iterator<CallSiteReference> sites = callGraph.getPossibleSites(caller, src); sites.hasNext();) { 
              CallSiteReference site = sites.next();
              ISSABasicBlock[] blks = ir.getBasicBlocksForCall(site);
              for (int i = 0; i < blks.length; i++) {
                // get succs because we want to exclude the block containing the 
                // call we came from
                Iterator<ISSABasicBlock> succBlks = cfg.getSuccNodes(blks[i]);
                while (succBlks.hasNext()) {
                  possibleStartBlocks.add(succBlks.next());
                }
              }
            }
            
            Set<ISSABasicBlock> localReachable = DFS.getReachableNodes(cfg, possibleStartBlocks);
            Set<CGNode> callees = WALACFGUtil.getCallTargetsInBlocks(localReachable, caller, callGraph);
            for (CGNode callee : callees) {
              if (reachable.add(callee)) {
                reachable.addAll(OrdinalSet.toCollection(callGraphTransitiveClosure.get(callee)));
              }
            }
            if (reachable.containsAll(snks)) return reachable; // early return if we cover everything
          } else {
             if (includeCallers) reachable.add(caller);
            reachable.addAll(reachableFromCaller);
          }
        }
      } // end for (;;)
      if (!progress) break;
      srcs = frontier;
    }
    // add partially reachable to the reachable set; we only kept this set to prevent unsound skipping during the search
    if (includeCallers) reachable.addAll(partiallyReachable);
    return reachable;
  }
  
  static boolean alreadyJumped = false;
  
  public boolean computeRelevanceGraph(IPathInfo path) { 
    // TODO: tmp hack! prepare for jump
    IPathInfo copy = path.deepCopy();
    boolean jumping = false;
    if (!alreadyJumped && path.query instanceof CombinedPathAndPointsToQuery) {
      CombinedPathAndPointsToQuery qry = (CombinedPathAndPointsToQuery) path.query;
      //if (qry.constraints.size() > 1) {
      if (qry.constraints.size() > 0) {
        Util.Debug("jumping on path " + path);
        // TODO: say also that the constraint does not depend on a parameter
        path.removeAllLocalConstraintsFromQuery();
        Util.Debug("after removing locals " + path);
        jumping = true;
        alreadyJumped = true;
      }
    } 
    // end tmp hack
    
    // the edges backward reachable from start node
    BasicNaturalRelation relevantEdges = new BasicNaturalRelation();
    List<CGNode> nodeWorklist = new ArrayList<CGNode>();
    Set<CGNode> seen = HashSetFactory.make();
    CGNode startNode = path.getCurrentNode();
    SSACFG.BasicBlock startBlock = path.getCurrentBlock();
    nodeWorklist.add(startNode);
    seen.add(startNode);
    
    // the set of methods that may be on the call stack when start is called
    Map<CGNode,Set<ISSABasicBlock>> upSet = HashMapFactory.make();
    
    Iterator<IStackFrame> stackIter = path.getCallStack().iterator();
    CGNode last = null;
    do {
      if (last != null) {
        IStackFrame frame = stackIter.next();
        startNode = frame.getCGNode();
        startBlock = frame.getBlock();
        // add caller -> callee edge
        relevantEdges.add(callGraph.getNumber(startNode), callGraph.getNumber(last));
      } 
      IR ir = startNode.getIR();
      // get blocks backward reachable from start location and add them to the upSet for this node
      Set<ISSABasicBlock> reachableFromStart = HashSetFactory.make();
      Graph<ISSABasicBlock> invertedStartCFG = GraphInverter.invert(ir.getControlFlowGraph());
      getBackwardReachableFrom(invertedStartCFG.getPredNodes(startBlock), invertedStartCFG, reachableFromStart);
      last = startNode;
      upSet.put(startNode, reachableFromStart);
    } while (stackIter.hasNext());
    
    
    // mark nodes backward reachable from start node
    while (!nodeWorklist.isEmpty()) {
      CGNode node = nodeWorklist.remove(0);
      int nodeNum = this.callGraph.getNumber(node);
      for (Iterator<CGNode> preds = this.callGraph.getPredNodes(node); preds.hasNext();) {
        CGNode next = preds.next();
        // add caller -> callee edge
        relevantEdges.add(this.callGraph.getNumber(next), nodeNum);
        if (!seen.add(next)) continue;
        nodeWorklist.add(next);
      }
    }
   
    // sanity check to identify recursion
    // TODO: think we can actually handle recursion by detecting a fixed point w.r.t reachable blocks for each node
    Set<CGNode> processed = HashSetFactory.make();
    
    /*
    if (startInstr != null) {
      IR startIR = startNode.getIR();
      ISSABasicBlock startBlock = startIR.getBasicBlockForInstruction(startInstr);
      // should only call this if the start instruction is at the beginning of a block
      Util.Assert(startBlock.iterator().next() == startInstr);
      // get blocks backward reachable from start node and add them to the upSet
      Set<ISSABasicBlock> reachableFromStart = HashSetFactory.make();
      Graph<ISSABasicBlock> invertedStartCFG = GraphInverter.invert(startIR.getControlFlowGraph());
      getBackwardReachableFrom(invertedStartCFG.getPredNodes(startBlock), invertedStartCFG, reachableFromStart);
      upSet.put(startNode, reachableFromStart);
    } // else, startInstr == null means we are starting from the beginning of the method
    */
    
    // list of (callee, caller) pairs to process
    List<Pair<CGNode,CGNode>> worklist = new ArrayList<Pair<CGNode,CGNode>>();
    // add predecessors of start node to the worklist
    for (Iterator<CGNode> startPreds = callGraph.getPredNodes(startNode); startPreds.hasNext();) {
      worklist.add(Pair.make(startNode, startPreds.next()));
    }

    // compute the UP set for the start node
    while (!worklist.isEmpty()) {
      Pair<CGNode,CGNode> pair = worklist.remove(0);
      CGNode callee = pair.fst, caller = pair.snd;
      // we are analyzing statements in caller
      Set<ISSABasicBlock> reachableBlocks = upSet.get(caller);
      if (reachableBlocks == null) {
        reachableBlocks = HashSetFactory.make();
        upSet.put(caller, reachableBlocks);
      }
      
      IR callerIR = caller.getIR();
      Graph<ISSABasicBlock> invertedCallerCFG = GraphInverter.invert(callerIR.getControlFlowGraph());
      // mark all the nodes that are backward reachable from each call site that might dispatch to callee
      for (Iterator<CallSiteReference> sites = callGraph.getPossibleSites(caller, callee); sites.hasNext();) { 
        CallSiteReference site = sites.next();
        ISSABasicBlock[] blks = callerIR.getBasicBlocksForCall(site);
        for (int i = 0; i < blks.length; i++) {
          if (reachableBlocks.contains(blks[i])) continue; // we've already seen this block
          // start from preds since we don't want to mark the call site / block we started from as reachable
          getBackwardReachableFrom(invertedCallerCFG.getPredNodes(blks[i]), invertedCallerCFG, reachableBlocks);
        }
      }
      
      int callerNumber = callGraph.getNumber(caller), calleeNumber = callGraph.getNumber(callee);
      Util.Assert(relevantEdges.contains(callerNumber, calleeNumber));
      relevantEdges.remove(callerNumber, calleeNumber);

      // if we have processed all the relevant callees for this caller
      if (relevantEdges.getRelatedCount(callerNumber) == 0) {
        for (Iterator<CGNode> preds = callGraph.getPredNodes(caller); preds.hasNext();) {
          CGNode next = preds.next();
          Util.Assert(relevantEdges.contains(callGraph.getNumber(next), callerNumber), 
              "no edge " + next.getMethod() + " -> " + caller.getMethod());
          // caller is the new callee and preds.next() is the new caller
          worklist.add(Pair.make(caller, next));
        }
        // make sure we won't loop forever due to recursion
        Util.Assert(processed.add(caller), "recursion detected from " + caller);
      }
    }
    
    // map of nodes in the UP set to sets of nodes in their DOWN set
    Map<CGNode,Set<CGNode>> downSet = HashMapFactory.make();
    // set of nodes in DOWN sets of *all* nodes in UP set
    Set<CGNode> downSetAll = HashSetFactory.make();
    // done computing UP set. can now compute the DOWN set for each method in the UP set
    for (Entry<CGNode,Set<ISSABasicBlock>> entry : upSet.entrySet()) {
      CGNode node = entry.getKey();
      Set<ISSABasicBlock> reachableBlocks = entry.getValue();
      Set<CGNode> set = downSet.get(node);
      if (set == null) {
        set = HashSetFactory.make();
        downSet.put(node, set);
      }
      IR ir = node.getIR();
      // TODO: can be smarter about not doing redundant work here
      for (Iterator<CallSiteReference> sites = node.iterateCallSites(); sites.hasNext();) {
        CallSiteReference site = sites.next();
        ISSABasicBlock[] blocks = ir.getBasicBlocksForCall(site);
        for (int i = 0; i < blocks.length; i++) {
          if (reachableBlocks.contains(blocks[i])) {
            // add down set for this call
            for (CGNode targetNode : this.callGraph.getNodes(site.getDeclaredTarget())) {
              if (!set.contains(targetNode)) {
                set.addAll(OrdinalSet.toCollection(callGraphTransitiveClosure.get(targetNode)));
              }
            }
            break;
          }
        }
      }
      downSetAll.addAll(set);
    }
    // done computing DOWN set. now how do we use DOWN and UP sets?
    Util.Debug("real UP set has " + upSet.keySet().size());    
    Util.Debug("real DOWN set has " + downSetAll.size() + ", " + downSet.keySet().size() + " keys.");
    
    
    Map<Constraint,Set<CGNode>> constraintModMap = path.query.getRelevantNodes();//path.getModifiersForQuery();
    // get potential producers for constraints
    //Set<CGNode> relevantNodes = Util.flatten(constraintModMap.values());
    Set<CGNode> relevantNodes = Util.flattenAndIntersect(constraintModMap.values());
    if (Options.DEBUG) {
      Util.Debug("MAP: ");
      for (Constraint constraint : constraintModMap.keySet()) {
        Util.Debug(constraint + " ===>\n" + Util.printCollection(constraintModMap.get(constraint)));
      }
    }
    
    for (CGNode node : relevantNodes) {
      if (upSet.keySet().contains(node)) {
        Util.Debug("UP set contains " + node);
        if (jumping) {
          IPathInfo fork = path.deepCopy();
          fork.getCallStack().clear();
          // TODO: this should actually be each call site that has a DOWN set
          SSACFG.BasicBlock exit = node.getIR().getControlFlowGraph().exit();
          fork.setCurrentNode(node);
          fork.addContextualConstraints(node); 
          fork.setCurrentBlock(exit);
          fork.setCurrentLineNum(exit.getAllInstructions().size());
          Util.Debug("adding relevance fork " + fork.getPathId());
          this.addPath(fork);
        }
        // relevant as long as relevant statement(s) are reachable
        // TODO: check
        continue;
      } 
      
      if (downSetAll.contains(node)) {
        // definitely relevant
          Util.Debug("DOWN set contains " + node);
        if (jumping) {
          IPathInfo fork = path.deepCopy();
          fork.getCallStack().clear();
          SSACFG.BasicBlock exit = node.getIR().getControlFlowGraph().exit();
          fork.setCurrentNode(node);
          fork.addContextualConstraints(node); 
          fork.setCurrentBlock(exit);
          fork.setCurrentLineNum(exit.getAllInstructions().size());
          Util.Debug("adding relevance fork " + fork.getPathId());
          this.addPath(fork);
        }
      } else {
        // definitely not relevant
        Util.Debug("node " + node + " not in UP or DOWN set");
      }
    }
    return jumping;
  }
  
  public static boolean computeRelGraph(IPathInfo opath, CallGraph callGraph, Map<CGNode, OrdinalSet<CGNode>> callGraphTransitiveClosure) { 
	    // TODO: tmp hack! prepare for jump
	    IPathInfo path = opath.deepCopy();
	    boolean jumping = false;
	    if (!alreadyJumped && path.query instanceof CombinedPathAndPointsToQuery) {
	      CombinedPathAndPointsToQuery qry = (CombinedPathAndPointsToQuery) path.query;
	      //if (qry.constraints.size() > 1) {
	      if (qry.constraints.size() > 0) {
	        Util.Print("jumping on path " + path);
	        // TODO: say also that the constraint does not depend on a parameter
	        path.removeAllLocalConstraintsFromQuery();
	        Util.Print("after removing locals " + path);
	        jumping = true;
	        alreadyJumped = true;
	      }
	    } 
	    // end tmp hack
	    
	    // the edges backward reachable from start node
	    BasicNaturalRelation relevantEdges = new BasicNaturalRelation();
	    List<CGNode> nodeWorklist = new ArrayList<CGNode>();
	    Set<CGNode> seen = HashSetFactory.make();
	    CGNode startNode = path.getCurrentNode();
	    SSACFG.BasicBlock startBlock = path.getCurrentBlock();
	    nodeWorklist.add(startNode);
	    seen.add(startNode);
	    
	    // the set of methods that may be on the call stack when start is called
	    Map<CGNode,Set<ISSABasicBlock>> upSet = HashMapFactory.make();
	    
	    Iterator<IStackFrame> stackIter = path.getCallStack().iterator();
	    CGNode last = null;
	    do {
	      if (last != null) {
	        IStackFrame frame = stackIter.next();
	        startNode = frame.getCGNode();
	        startBlock = frame.getBlock();
	        // add caller -> callee edge
	        relevantEdges.add(callGraph.getNumber(startNode), callGraph.getNumber(last));
	      } 
	      IR ir = startNode.getIR();
	      // get blocks backward reachable from start location and add them to the upSet for this node
	      Set<ISSABasicBlock> reachableFromStart = HashSetFactory.make();
	      Graph<ISSABasicBlock> invertedStartCFG = GraphInverter.invert(ir.getControlFlowGraph());
	      getBackwardReachableFrom(invertedStartCFG.getPredNodes(startBlock), invertedStartCFG, reachableFromStart);
	      last = startNode;
	      upSet.put(startNode, reachableFromStart);
	    } while (stackIter.hasNext());
	    
	    
	    // mark nodes backward reachable from start node
	    while (!nodeWorklist.isEmpty()) {
	      CGNode node = nodeWorklist.remove(0);
	      int nodeNum = callGraph.getNumber(node);
	      for (Iterator<CGNode> preds = callGraph.getPredNodes(node); preds.hasNext();) {
	        CGNode next = preds.next();
	        // add caller -> callee edge
	        relevantEdges.add(callGraph.getNumber(next), nodeNum);
	        if (!seen.add(next)) continue;
	        nodeWorklist.add(next);
	      }
	    }
	   
	    // sanity check to identify recursion
	    // TODO: think we can actually handle recursion by detecting a fixed point w.r.t reachable blocks for each node
	    Set<CGNode> processed = HashSetFactory.make();
	    
	    /*
	    if (startInstr != null) {
	      IR startIR = startNode.getIR();
	      ISSABasicBlock startBlock = startIR.getBasicBlockForInstruction(startInstr);
	      // should only call this if the start instruction is at the beginning of a block
	      Util.Assert(startBlock.iterator().next() == startInstr);
	      // get blocks backward reachable from start node and add them to the upSet
	      Set<ISSABasicBlock> reachableFromStart = HashSetFactory.make();
	      Graph<ISSABasicBlock> invertedStartCFG = GraphInverter.invert(startIR.getControlFlowGraph());
	      getBackwardReachableFrom(invertedStartCFG.getPredNodes(startBlock), invertedStartCFG, reachableFromStart);
	      upSet.put(startNode, reachableFromStart);
	    } // else, startInstr == null means we are starting from the beginning of the method
	    */
	    
	    // list of (callee, caller) pairs to process
	    List<Pair<CGNode,CGNode>> worklist = new ArrayList<Pair<CGNode,CGNode>>();
	    // add predecessors of start node to the worklist
	    for (Iterator<CGNode> startPreds = callGraph.getPredNodes(startNode); startPreds.hasNext();) {
	      worklist.add(Pair.make(startNode, startPreds.next()));
	    }

	    // compute the UP set for the start node
	    while (!worklist.isEmpty()) {
	      Pair<CGNode,CGNode> pair = worklist.remove(0);
	      CGNode callee = pair.fst, caller = pair.snd;
	      // we are analyzing statements in caller
	      Set<ISSABasicBlock> reachableBlocks = upSet.get(caller);
	      if (reachableBlocks == null) {
	        reachableBlocks = HashSetFactory.make();
	        upSet.put(caller, reachableBlocks);
	      }
	      
	      IR callerIR = caller.getIR();
	      Graph<ISSABasicBlock> invertedCallerCFG = GraphInverter.invert(callerIR.getControlFlowGraph());
	      // mark all the nodes that are backward reachable from each call site that might dispatch to callee
	      for (Iterator<CallSiteReference> sites = callGraph.getPossibleSites(caller, callee); sites.hasNext();) { 
	        CallSiteReference site = sites.next();
	        ISSABasicBlock[] blks = callerIR.getBasicBlocksForCall(site);
	        for (int i = 0; i < blks.length; i++) {
	          if (reachableBlocks.contains(blks[i])) continue; // we've already seen this block
	          // start from preds since we don't want to mark the call site / block we started from as reachable
	          getBackwardReachableFrom(invertedCallerCFG.getPredNodes(blks[i]), invertedCallerCFG, reachableBlocks);
	        }
	      }
	      
	      int callerNumber = callGraph.getNumber(caller), calleeNumber = callGraph.getNumber(callee);
	      Util.Assert(relevantEdges.contains(callerNumber, calleeNumber));
	      relevantEdges.remove(callerNumber, calleeNumber);

	      // if we have processed all the relevant callees for this caller
	      if (relevantEdges.getRelatedCount(callerNumber) == 0) {
	        for (Iterator<CGNode> preds = callGraph.getPredNodes(caller); preds.hasNext();) {
	          CGNode next = preds.next();
	          Util.Assert(relevantEdges.contains(callGraph.getNumber(next), callerNumber), 
	              "no edge " + next.getMethod() + " -> " + caller.getMethod());
	          // caller is the new callee and preds.next() is the new caller
	          worklist.add(Pair.make(caller, next));
	        }
	        // make sure we won't loop forever due to recursion
	        Util.Assert(processed.add(caller), "recursion detected from " + caller);
	      }
	    }
	    
	    // map of nodes in the UP set to sets of nodes in their DOWN set
	    Map<CGNode,Set<CGNode>> downSet = HashMapFactory.make();
	    // set of nodes in DOWN sets of *all* nodes in UP set
	    Set<CGNode> downSetAll = HashSetFactory.make();
	    // done computing UP set. can now compute the DOWN set for each method in the UP set
	    for (Entry<CGNode,Set<ISSABasicBlock>> entry : upSet.entrySet()) {
	      CGNode node = entry.getKey();
	      Set<ISSABasicBlock> reachableBlocks = entry.getValue();
	      Set<CGNode> set = downSet.get(node);
	      if (set == null) {
	        set = HashSetFactory.make();
	        downSet.put(node, set);
	      }
	      IR ir = node.getIR();
	      // TODO: can be smarter about not doing redundant work here
	      for (Iterator<CallSiteReference> sites = node.iterateCallSites(); sites.hasNext();) {
	        CallSiteReference site = sites.next();
	        ISSABasicBlock[] blocks = ir.getBasicBlocksForCall(site);
	        for (int i = 0; i < blocks.length; i++) {
	          if (reachableBlocks.contains(blocks[i])) {
	            // add down set for this call
	            for (CGNode targetNode : callGraph.getNodes(site.getDeclaredTarget())) {
	              if (!set.contains(targetNode)) {
	                set.addAll(OrdinalSet.toCollection(callGraphTransitiveClosure.get(targetNode)));
	              }
	            }
	            break;
	          }
	        }
	      }
	      downSetAll.addAll(set);
	    }
	    // done computing DOWN set. now how do we use DOWN and UP sets?
	    Util.Print("real UP set has " + upSet.keySet().size());    
	    Util.Print("real DOWN set has " + downSetAll.size() + ", " + downSet.keySet().size() + " keys.");
	    
	    
	    Map<Constraint,Set<CGNode>> constraintModMap = path.query.getRelevantNodes();//path.getModifiersForQuery();
	    // get potential producers for constraints
	    //Set<CGNode> relevantNodes = Util.flatten(constraintModMap.values());
	    Set<CGNode> relevantNodes = Util.flattenAndIntersect(constraintModMap.values());
	    Util.Print("MAP: ");
	    for (Constraint constraint : constraintModMap.keySet()) {
	    	Util.Print(constraint + " ===>\n" + Util.printCollection(constraintModMap.get(constraint)));
	    }
	    
	    
	    for (CGNode node : relevantNodes) {
	      if (upSet.keySet().contains(node)) {
	        Util.Print("UP set contains " + node);
	        if (jumping) {
	          IPathInfo fork = path.deepCopy();
	          fork.getCallStack().clear();
	          // TODO: this should actually be each call site that has a DOWN set
	          SSACFG.BasicBlock exit = node.getIR().getControlFlowGraph().exit();
	          fork.setCurrentNode(node);
	          fork.addContextualConstraints(node); 
	          fork.setCurrentBlock(exit);
	          fork.setCurrentLineNum(exit.getAllInstructions().size());
	          Util.Print("adding relevance fork " + fork.getPathId());
	          //this.addPath(fork);
	        }
	        // relevant as long as relevant statement(s) are reachable
	        // TODO: check
	        continue;
	      } 
	      
	      if (downSetAll.contains(node)) {
	        // definitely relevant
	          Util.Print("DOWN set contains " + node);
	        if (jumping) {
	          IPathInfo fork = path.deepCopy();
	          fork.getCallStack().clear();
	          SSACFG.BasicBlock exit = node.getIR().getControlFlowGraph().exit();
	          fork.setCurrentNode(node);
	          fork.addContextualConstraints(node); 
	          fork.setCurrentBlock(exit);
	          fork.setCurrentLineNum(exit.getAllInstructions().size());
	          Util.Print("adding relevance fork " + fork.getPathId());
	          //this.addPath(fork);
	        }
	      } else {
	        // definitely not relevant
	        Util.Print("node " + node + " not in UP or DOWN set");
	      }
	    }
	    return jumping;
	  }

  @Override
  public boolean handleInterproceduralExecution(IPathInfo path) {
    Graph<CGNode> reversed = GraphInverter.invert(this.callGraph);
    
    // TMP SANITY CHECK
    CGNode startNode = path.getCurrentNode();
    LinkedList<IStackFrame> callStack = path.getCallStack();
    if (!callStack.isEmpty()) {
      startNode = callStack.getLast().getCGNode();
    }
    
    // assume single entrypoint node
    BFSPathFinder<CGNode> finder = new BFSPathFinder<CGNode>(reversed, startNode, this.callGraph.getFakeRootNode());
    List<CGNode> cgPath = finder.find();
    Util.Debug("Path to root " + Util.printCollection(cgPath));
    Util.Debug(cgPath.size() + " nodes in shortest path.");
    
    Set<CGNode> upSet = HashSetFactory.make();
    Set<CGNode> downSet = HashSetFactory.make();
    
    int blockCount = 0;
    
    BFSIterator<CGNode> iter = new BFSIterator<CGNode>(reversed, startNode);
    while (iter.hasNext()) {
      CGNode next = iter.next();
      blockCount += next.getIR().getControlFlowGraph().getNumberOfNodes();
      upSet.add(next);
      downSet.addAll(OrdinalSet.toCollection(callGraphTransitiveClosure.get(next)));
      Util.Debug("node is " + next);
    }
    Util.Debug(upSet.size() + " nodes in UP set.");
    Util.Debug(blockCount + " blocks in naive UP set");
    Util.Debug(downSet.size() + " nodes in naive DOWN set.");
    // END TMP SANITY CHECK!

    boolean jumped = computeRelevanceGraph(path);

    if (!jumped) return super.handleInterproceduralExecution(path);
    return false;
  }
  
  /**
   * 
   * add all nodes backward reachable from @param startingPoints (including the nodes in startingPoints) to @param reachable
   */
  public static <T> void getBackwardReachableFrom(Iterator<T> startingPoints, Graph<T> graph, Set<T> reachable) {
    while (startingPoints.hasNext()) {
      T next = startingPoints.next();
      if (!reachable.add(next)) {
        // find and add the predecessors of the block 
        reachable.addAll(DFS.getReachableNodes(graph, Collections.singletonList(next)));
      }
    }
  }
}


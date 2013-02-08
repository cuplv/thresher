package edu.colorado.thresher;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import com.ibm.wala.dataflow.IFDS.ICFGSupergraph;
import com.ibm.wala.dataflow.IFDS.IFlowFunction;
import com.ibm.wala.dataflow.IFDS.IMergeFunction;
import com.ibm.wala.dataflow.IFDS.IPartiallyBalancedFlowFunctions;
import com.ibm.wala.dataflow.IFDS.ISupergraph;
import com.ibm.wala.dataflow.IFDS.IUnaryFlowFunction;
import com.ibm.wala.dataflow.IFDS.IdentityFlowFunction;
import com.ibm.wala.dataflow.IFDS.KillEverything;
import com.ibm.wala.dataflow.IFDS.PartiallyBalancedTabulationProblem;
import com.ibm.wala.dataflow.IFDS.PathEdge;
import com.ibm.wala.dataflow.IFDS.TabulationDomain;
import com.ibm.wala.dataflow.graph.BitVectorSolver;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.AbstractNumberedGraph;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.NumberedEdgeManager;
import com.ibm.wala.util.graph.NumberedNodeManager;
import com.ibm.wala.util.graph.traverse.DFSFinishTimeIterator;
import com.ibm.wala.util.intset.BitVector;
import com.ibm.wala.util.intset.BitVectorIntSet;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.MutableMapping;
import com.ibm.wala.util.intset.MutableSparseIntSet;
import com.ibm.wala.util.intset.SparseIntSet;


/**
 * Ordinary callgraph augmented with edges between methods called from the same method. For example, if in method main() 
 * foo() is called and then bar() is called, we will ad an edge between foo() and bar() in the expanded callgraph.
 * @author sam
 *
 * @param <CGNode>
 */
public class ExpandedCallgraph extends AbstractNumberedGraph<CGNode> {
    private final CallGraph delegate;
    
    private final NumberedEdgeManager<CGNode> edgeMgr = new NumberedEdgeManager<CGNode>() {
    	
    	private final Map<CGNode,Set<CGNode>> localEdgesFwMap = new HashMap<CGNode,Set<CGNode>>();
    	private final Map<CGNode,Set<CGNode>> localEdgesBwMap = new HashMap<CGNode,Set<CGNode>>();
    	
    	
    	//private final IBinaryNaturalRelaation localEdges = new BasicNaturalRelation();
    	
    	public void addEdge(CGNode src, CGNode dst) {
    		addEdgeToMap(src, dst, localEdgesFwMap);
    		addEdgeToMap(dst, src, localEdgesBwMap);
 	    }
    	
    	private void addEdgeToMap(CGNode src, CGNode dst, Map<CGNode,Set<CGNode>> map) {
    		Set<CGNode> edgeSet = map.get(src);
    		if (edgeSet == null) {
    			edgeSet = new HashSet<CGNode>();
    			map.put(src, edgeSet);
    		}
    		edgeSet.add(dst);
    	}
    	
        public int getPredNodeCount(CGNode N) {
	        Assertions.UNREACHABLE();
	        return 0;
        }

        public Iterator<CGNode> getPredNodes(CGNode N) {
        	Iterator<CGNode> preds = delegate.getPredNodes(N);
        	// augment pred nodes of main graph with preds in localEdgesBwMap
        	return augmentIteratorWithMapEdges(N, preds, localEdgesBwMap);
        }

        public int getSuccNodeCount(CGNode N) {
        	Assertions.UNREACHABLE();
	        return 0;
        }

        public Iterator<CGNode> getSuccNodes(CGNode N) {
        	Iterator<CGNode> succs = delegate.getSuccNodes(N);
        	// augment succ nodes of main graph with succs in localEdgesFwMap
        	return augmentIteratorWithMapEdges(N, succs, localEdgesFwMap);
        }
        
        private Iterator<CGNode> augmentIteratorWithMapEdges(CGNode N, Iterator<CGNode> iter, Map<CGNode,Set<CGNode>> map) {
        	// augment succ nodes of main graph with succs in localEdgesMap
        	Set<CGNode> set = new HashSet<CGNode>();
        	while (iter.hasNext()) set.add(iter.next());
        	Set<CGNode> mapEdges = map.get(N);
        	if (mapEdges != null) {
        		set.addAll(mapEdges);
        		return mapEdges.iterator();
        	}
        	return set.iterator();//Collections.EMPTY_LIST.iterator();        	
        }
        
        public boolean hasEdge(CGNode src, CGNode dst) {
        	if (delegate.hasEdge(src, dst)) return true;
        	// else, check local succs
        	Set<CGNode> localSuccs = localEdgesFwMap.get(src);
        	if (localSuccs == null) return false;
        	return localSuccs.contains(dst);
        }
        
    	public void removeAllIncidentEdges(CGNode node) throws UnsupportedOperationException {
    		Assertions.UNREACHABLE();
    	}

    	public void removeEdge(CGNode src, CGNode dst) throws UnsupportedOperationException {
    		Assertions.UNREACHABLE();
    	}

    	public void removeIncomingEdges(CGNode node) throws UnsupportedOperationException {
	        Assertions.UNREACHABLE();
    	}

    	public void removeOutgoingEdges(CGNode node) throws UnsupportedOperationException {
    		Assertions.UNREACHABLE();
    	}
    	
        public IntSet getPredNodeNumbers(CGNode N) {
	        Assertions.UNREACHABLE();
	        return null;
        }

        public IntSet getSuccNodeNumbers(CGNode node) {
        	Assertions.UNREACHABLE();
	        return null;
	    }
	};

    private ExpandedCallgraph(CallGraph delegate) {
      super();
      this.delegate = delegate;
  	  //computeLocalEdgesFlowSensitive(delegate.getFakeRootNode());
      computeLocalEdges();      
    }
    
    public static Graph<CGNode> make(CallGraph graph) {
    	return new ExpandedCallgraph(graph);
    }
 
    private void computeLocalEdges() {
    	Iterator<CGNode> iter = delegate.iterator();
    	CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(delegate);
    	while (iter.hasNext()) {
    		CGNode node = iter.next();
    		// there's no deterministic flow between edges in fakeWorldClinit; skip
    		if (node.equals(fakeWorldClinit)) continue;
    		// TODO: this ruins everything. need pathfinder that takes return edges into account
    		// add return edge between caller and callee
    		Iterator<CGNode> succs = this.delegate.getSuccNodes(node);
    		while (succs.hasNext()) {
    			CGNode succ = succs.next();
    			Util.Debug("adding return edge between " + succ + " and " + node); 
    			addEdge(succ, node);
    		}
    		
    		// compute set of CGNode's that can reach each block
    		final IntraprocReachingCalls reaching = new IntraprocReachingCalls(node, delegate);
    		final BitVectorSolver<ISSABasicBlock> solver = reaching.analyze();
    		SSACFG cfg = node.getIR().getControlFlowGraph();
    		for (ISSABasicBlock blk : cfg) { // for each block
    			IntSet curSet = solver.getOut(blk).getValue();
    			if (curSet == null) continue;
    			Iterator<ISSABasicBlock> preds = cfg.getPredNodes(blk);
    			while (preds.hasNext()) {
    				ISSABasicBlock pred = preds.next();
    				IntSet predSet = solver.getOut(pred).getValue();
    				if (predSet == null ||
    					predSet.size() == curSet.size()) continue; // optimization: same set size means same call set
    				// create {all nodes in pred} -> {all nodes in cur \ pred} edges
    				IntIterator predIter = predSet.intIterator();
    				while (predIter.hasNext()) { // for each call in pred
    					int predNum = predIter.next();
    					IntIterator curIter = curSet.intIterator();
    					while (curIter.hasNext()) { // for each call in cur
    						int curNum = curIter.next();
    						// TODO: this is probably wrong. how do we detect calling the same CGNode multiple times v.s. just copying?
    						if (predSet.contains(curNum)) continue; // don't want to create self edges
    						// else, curNum is in curSet but not in predSet. add edge
    						CGNode curNode = reaching.getCorrespondingNode(curNum), predNode = reaching.getCorrespondingNode(predNum);
    						addEdge(predNode, curNode);
    					}
    				}
    			}
    		}
    	}
    }
    
    /**
     * augment the call graph with edges between methods called at the same level
     */
    private void computeLocalEdgesFlowInsensitive(CGNode fakeRootNode) {
    	Iterator<CGNode> iter = delegate.iterator();
    	while (iter.hasNext()) {
    		CGNode node = iter.next();
    		//if (node.equals(fakeRootNode)) continue; 
    		Iterator<CGNode> succs = delegate.getSuccNodes(node);
    		List<CGNode> succList = new LinkedList<CGNode>();
    		while (succs.hasNext()) succList.add(succs.next());
    		// (flow-insensitively) add edges between all succs
    		for (CGNode node0 : succList) {
    			for (CGNode node1 : succList) {
    				//edgeMgr.addEdge(node0, node1);
    				addEdge(node0, node1);
    				addEdge(node1, node0);
    			}
    		}
    		/*
    		Iterator<CallSiteReference> siteIter = node.iterateCallSites();
    		while (siteIter.hasNext()) {
    			CallSiteReference site = siteIter.next();
    			site.
    		}
    		*/
    	}
    }
    
    private void computeLocalEdgesFlowSensitive(CGNode fakeRootNode) {
    	Iterator<CGNode> iter = delegate.iterator();
    	CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(delegate);
    	while (iter.hasNext()) {
    		CGNode node = iter.next();	
    		Util.Debug("NODE " + node);
    		/*
    		if (node.equals(fakeWorldClinit)) {
    			// special handling class initializers--need to consider every possible order
    			Iterator<CGNode> succs = delegate.getSuccNodes(node);
        		List<CGNode> succList = new LinkedList<CGNode>();
        		while (succs.hasNext()) succList.add(succs.next());
        		// (flow-insensitively) add edges between all succs
        		for (CGNode node0 : succList) {
        			for (CGNode node1 : succList) {
        				//edgeMgr.addEdge(node0, node1);
        				this.addEdge(node0, node1);
        				this.addEdge(node1, node0);
        			}
        		}
        		continue;
    		}
    		*/
    		Set<CGNode> previousCalls = new HashSet<CGNode>();
    		ISSABasicBlock entry = node.getIR().getControlFlowGraph().entry();
    		computeLocalEdgesRec(entry, previousCalls, node);
    	}
    }
    
    /**
     * return the block where edge computation halted (either the end of the proc or a join point)
     */
    private ISSABasicBlock computeLocalEdgesRec(ISSABasicBlock blk, Set<CGNode> previousCalls, CGNode node) {
    	SSACFG cfg = node.getIR().getControlFlowGraph();
		Iterator<SSAInstruction> instrIter = blk.iterator();
		Set<CGNode> previous = new HashSet<CGNode>();
		while (instrIter.hasNext()) {
			SSAInstruction instr = instrIter.next();
			Util.Debug("ANINSTR" + instr);
			if (instr instanceof SSAInvokeInstruction) {
				Util.Debug("invoke");
				SSAInvokeInstruction invoke = (SSAInvokeInstruction) instr;
				Set<CGNode> targets = delegate.getPossibleTargets(node, invoke.getCallSite());
				if (targets == null) {
					Util.Debug("no targets for " + invoke.getCallSite());
					break;
				}
				for (CGNode target : targets) {
					for (CGNode prev : previous) {
						Util.Debug("adding edge between " + prev + " and " + target);
						this.addEdge(prev, target); // add control flow edge between this target and all previous calls
					}
				}
				previous.addAll(targets);
				break; 
			}
		}
		Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(blk);
		if (succs.isEmpty()) return blk; // if we have reached the end of the node
		
		if (cfg.getNormalPredecessors(blk).size() > 1) { // or if we have hit a join point
			Util.Assert(succs.size() == 1, "only expecting one successor here");
			return succs.iterator().next(); // the next block is a join point
		}
		
		if (succs.size() >= 1) {
			if (WALACFGUtil.isLoopHead((SSACFG.BasicBlock) blk, node.getIR())) {
				return handleLoopHeadCase((SSACFG.BasicBlock) blk, node, previous, succs);
			}
			
			// optimization: can save the cost of copying the previous set in the single successor case
			if (succs.size() == 1) return computeLocalEdgesRec(succs.iterator().next(), previous, node);
			return handleMultipleSuccsCase(succs, previous, node);
		}
		Assertions.UNREACHABLE();
		return null;
    }
    
    /**
     * add edges between all previous calls and all calls in the loop
     * treat the loop body flow-insensitively, adding bi-directional edges between each
     */
    private ISSABasicBlock handleLoopHeadCase(SSACFG.BasicBlock loopHead, CGNode node, Set<CGNode> previous, Collection<ISSABasicBlock> succs) {
		Set<CGNode> targets = WALACFGUtil.getCallTargetsInLoop(loopHead, node, delegate);
		// add edges between previous calls and calls in loop
		for (CGNode prev : previous) {
			for (CGNode loopTarget : targets) {
				this.addEdge(prev, loopTarget);
			}
		}
		// add bi-directional edges between all calls in  loop
		for (CGNode tgt0 : targets) {
			for (CGNode tgt1 : targets) {
				addEdge(tgt0, tgt1);
			}
		}
		previous.addAll(targets); // add all loop calls to previous list 
		ISSABasicBlock end = null;
		for (ISSABasicBlock succ : succs) {
			if (WALACFGUtil.isLoopEscapeBlock((SSACFG.BasicBlock) succ, loopHead, node.getIR())) {
				Util.Assert(end == null, "should only be one loop escape block!");
				end = computeLocalEdgesRec(succ, previous, node);
			}
		}
		Util.Assert(end != null, "couldn't find escape block!");
		return end;
    }
    
    @Override
    protected NumberedNodeManager<CGNode> getNodeManager() { return delegate; }
    
    private ISSABasicBlock handleMultipleSuccsCase(Collection<ISSABasicBlock> succs, Set<CGNode> previous, CGNode node) {
    	SSACFG cfg = node.getIR().getControlFlowGraph();
		// else, multiple successor case. need to join paths that enter same block in order to avoid exponential (and redundant) exploration
		// list of (blk, prev caller set) pairs
		Map<ISSABasicBlock,Set<CGNode>> joinedBlksMap = new HashMap<ISSABasicBlock,Set<CGNode>>();
		// map from join point blocks to set of incoming blocks we have yet to see
		Map<ISSABasicBlock,Set<ISSABasicBlock>> joinPointIncomingBlks = new HashMap<ISSABasicBlock, Set<ISSABasicBlock>>();	
		
		LinkedList<Pair<ISSABasicBlock,Set<CGNode>>> allSuccs = new LinkedList<Pair<ISSABasicBlock,Set<CGNode>>>();
		for (ISSABasicBlock succ : succs) {
			allSuccs.add(Pair.make(succ, Util.deepCopySet(previous)));
		}
		
		while (!allSuccs.isEmpty()) {
			Pair<ISSABasicBlock,Set<CGNode>> pair = allSuccs.removeFirst();
			Set<CGNode> prevCalls = pair.snd;
			ISSABasicBlock retBlk = computeLocalEdgesRec(pair.fst, prevCalls, node);
			// after return of computeLocalEdgesRec, we have either hit the end of the proc or we have hit a join point
			Collection<ISSABasicBlock> newSuccs = Util.iteratorToCollection(cfg.getSuccNodes(retBlk));
			if (newSuccs.size() == 1) { // join point
				ISSABasicBlock joinBlk = newSuccs.iterator().next();
				Set<ISSABasicBlock> incomingBlks = joinPointIncomingBlks.get(joinBlk);
				if (incomingBlks == null) {
					// this is the first time we've seen this join point
					incomingBlks = new HashSet<ISSABasicBlock>();
					Iterator<ISSABasicBlock> iter = cfg.getPredNodes(retBlk);
					// initialize list of blocks coming into the join point, including all but the current block
					while (iter.hasNext()) {
						ISSABasicBlock incomingBlk = iter.next();
						if (!incomingBlk.equals(joinBlk)) incomingBlks.add(incomingBlk);
					}
					joinPointIncomingBlks.put(joinBlk, Util.iteratorToSet(cfg.getPredNodes(retBlk)));
				} else {
					// we've already seen this join point; update list of incoming blocks we've seen
					boolean removed = incomingBlks.remove(joinBlk);
					if (Options.DEBUG) Util.Assert(removed, "couldn't remove " + joinBlk);
				}
				
				// update prev calls list for ths join block
				Set<CGNode> prevCalls2 = joinedBlksMap.get(joinBlk);
				if (prevCalls2 == null) { // if prevCalls list hasn't been initialized for this join point
					joinedBlksMap.put(joinBlk, prevCalls); // initialize prevCalls list
				} else prevCalls2.addAll(prevCalls); // update prev calls list
				
				// if we've seen all incoming blocks for this join point
				if (incomingBlks.isEmpty()) {
					// remove join point from maps
					joinPointIncomingBlks.remove(joinBlk);
					joinedBlksMap.remove(joinBlk);
					Util.Assert(prevCalls2 != null);
					// have seen all incoming blocks, so add join point to succs to explore
					allSuccs.add(Pair.make(joinBlk, prevCalls2));
				}
			}
			else Util.Assert(newSuccs.isEmpty(), "expecting either 0 succs or 1!");
		}
		return null;
    }
    
    @Override
    protected NumberedEdgeManager<CGNode> getEdgeManager() {
      return edgeMgr;
    }
 
 
    /*
    
    class CallGraphSearch {
    	Map<CGNode,CGNode> flowEdges; // can switch current node from key to value
    	
    	Map<CGNode,CGNode> callEdges; // can switch current node from key to value by pushing key onto call stack
    	
    	Map<CGNode,CGNode> returnEdges; // can switch current node from key to value IF popping call stack yields value
    	
    	
    	Stack<CGNode> callStack;
    	CGNode currentNode;
    	Graph<CGNode> callGraph;
    	Set<CGNode> srcs;
    	
    	// rules:
    	// 
    	
    	public void compute() {
    		for (CGNode node : srcs) {
    			currentNode = node;
    			Iterator<CGNode> iter = callGraph.getSuccNodes(node);
    			while (iter.hasNext()) {
    				CGNode next = iter.next();
    				if
    			}
    		}
    	}
    }
    */
    
}

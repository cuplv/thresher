package edu.colorado.thresher;

import java.util.Collection;
import java.util.Set;

import com.ibm.wala.dataflow.IFDS.IFlowFunction;
import com.ibm.wala.dataflow.IFDS.IMergeFunction;
import com.ibm.wala.dataflow.IFDS.IPartiallyBalancedFlowFunctions;
import com.ibm.wala.dataflow.IFDS.ISupergraph;
import com.ibm.wala.dataflow.IFDS.IUnaryFlowFunction;
import com.ibm.wala.dataflow.IFDS.IdentityFlowFunction;
import com.ibm.wala.dataflow.IFDS.KillEverything;
import com.ibm.wala.dataflow.IFDS.PartiallyBalancedTabulationProblem;
import com.ibm.wala.dataflow.IFDS.PartiallyBalancedTabulationSolver;
import com.ibm.wala.dataflow.IFDS.PathEdge;
import com.ibm.wala.dataflow.IFDS.TabulationDomain;
import com.ibm.wala.dataflow.IFDS.TabulationResult;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.MutableMapping;
import com.ibm.wala.util.intset.MutableSparseIntSet;


/**
 * compute the set of {@ref CGNode's} from which control can flow to the current block 
 * the srcs param to the constructor is the set of nodes from which flow can originate
 * this is a partially balanced parentheses problem, as we also want to model flow that occurs 
 * from the callers of nodes in srcs
 * @author sam
 *
 */
public class ReachingCallsAnalysis {

    private final ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> superGraph;
    private final CallGraph callgraph;
    private final Collection<CGNode> srcs;
	
	public ReachingCallsAnalysis(ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> superGraph, CallGraph callgraph, Collection<CGNode> srcs) {
		this.superGraph = superGraph;
		this.callgraph = callgraph;
		this.srcs = srcs;
	}
	
	 /**
	   * perform the tabulation analysis and return the {@link TabulationResult}
	   */
	  public TabulationResult<BasicBlockInContext<IExplodedBasicBlock>,CGNode,Integer> analyze() {
	    PartiallyBalancedTabulationSolver<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Integer> solver = PartiallyBalancedTabulationSolver
	        .createPartiallyBalancedTabulationSolver(new ReachingCallsProblem(), null);
	    TabulationResult<BasicBlockInContext<IExplodedBasicBlock>,CGNode,Integer> result = null;
	    try {
	      result = solver.solve();
	    } catch (CancelException e) {
	      // this shouldn't happen 
	      Assertions.UNREACHABLE();
	    }
	    return result;

	  }

	  private class ReachingCallsFlowFunctions implements IPartiallyBalancedFlowFunctions<BasicBlockInContext<IExplodedBasicBlock>> {

	        protected ReachingCallsFlowFunctions() {
	        	super();
	        }

	        public IFlowFunction getUnbalancedReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
	            BasicBlockInContext<IExplodedBasicBlock> dest) {
	          return IdentityFlowFunction.identity();
	        }

	        public IUnaryFlowFunction getCallFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
	            BasicBlockInContext<IExplodedBasicBlock> dest, BasicBlockInContext<IExplodedBasicBlock> ret) {
	          return IdentityFlowFunction.identity();
	        }

	        public IUnaryFlowFunction getCallNoneToReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
	            BasicBlockInContext<IExplodedBasicBlock> dest) {
	        	return IdentityFlowFunction.identity();
	        }

	        public IUnaryFlowFunction getCallToReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> src,
	            BasicBlockInContext<IExplodedBasicBlock> dest) {
	        	// everything should flow through callee
	        	return IdentityFlowFunction.identity();
	        }
	        
	        public IUnaryFlowFunction getNormalFlowFunction(final BasicBlockInContext<IExplodedBasicBlock> src,
	                BasicBlockInContext<IExplodedBasicBlock> dest) {
	        	// don't model control flow between entrypoints
	        	if (src.getNode().equals(callgraph.getFakeRootNode())) return IdentityFlowFunction.identity();
	        	
	        	// add containing CGNode for current block to set of nodes seen
	        	return new IUnaryFlowFunction() {
	        		public IntSet getTargets(int d1) {
	        			MutableIntSet set = MutableSparseIntSet.makeEmpty();
	        			set.add(callgraph.getNumber(src.getNode()));
	        			return set;
	        		}
	        	};
	        }
	        
	        public IFlowFunction getReturnFlowFunction(BasicBlockInContext<IExplodedBasicBlock> call,
	                BasicBlockInContext<IExplodedBasicBlock> src, BasicBlockInContext<IExplodedBasicBlock> dest) {
	        	 return IdentityFlowFunction.identity();
	        }
	    }
	    
	 class ReachingCallsProblem implements
	    PartiallyBalancedTabulationProblem<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Integer> {

		 private final ReachingCallsFlowFunctions flowFunctions = new ReachingCallsFlowFunctions();
		 private TabulationDomain<Integer, BasicBlockInContext<IExplodedBasicBlock>> domain = new ReachingCallsDomain();

		 private Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> initialSeeds = collectInitialSeeds();

		 /**
		  * we use the entry block of the CGNode as the fake entry when propagating from callee to caller with unbalanced parens
		  */
		 public BasicBlockInContext<IExplodedBasicBlock> getFakeEntry(BasicBlockInContext<IExplodedBasicBlock> node) {
			 final CGNode cgNode = node.getNode();
			 return getFakeEntry(cgNode);
		 }

		 /**
		  * we use the entry block of the CGNode as the "fake" entry when propagating from callee to caller with unbalanced parens
		  */
		 private BasicBlockInContext<IExplodedBasicBlock> getFakeEntry(final CGNode cgNode) {
			 BasicBlockInContext<IExplodedBasicBlock>[] entriesForProcedure = superGraph.getEntriesForProcedure(cgNode);
			 Util.Assert(entriesForProcedure.length == 1);
			 return entriesForProcedure[0];
		 }

	  /**
	   * use the src nodes as seeds for the analysis
	   */
	  private Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> collectInitialSeeds() {
	      Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> result = HashSetFactory.make();
	      
	      for (CGNode node : srcs) {
	    	  int factNum = callgraph.getNumber(node);
	    	  domain.add(factNum);
	    	  BasicBlockInContext<IExplodedBasicBlock>[] entries = superGraph.getEntriesForProcedure(node);
	    	  for (int i = 0; i < entries.length; i++) {
	    		  BasicBlockInContext<IExplodedBasicBlock> fakeEntry = getFakeEntry(entries[i]);
	    		  result.add(PathEdge.createPathEdge(fakeEntry, factNum, entries[i], factNum));
	    	  }
	      }
	      
	      return result;
	  }

	  public IPartiallyBalancedFlowFunctions<BasicBlockInContext<IExplodedBasicBlock>> getFunctionMap() {
	    return flowFunctions;
	  }

	  public TabulationDomain<Integer,BasicBlockInContext<IExplodedBasicBlock>> getDomain() {
	    return domain;
	  }

	  /**
	   * we don't need a merge function; the default unioning of tabulation works fine
	   */
	  public IMergeFunction getMergeFunction() {
	    return null;
	  }

	  public ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> getSupergraph() {
	    return superGraph;
	  }

	  public Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> initialSeeds() {
	    return initialSeeds;
	  }

	}
	 
	 /**
	  * controls numbering of putstatic instructions for use in tabulation
	  */
	 private class ReachingCallsDomain extends MutableMapping<Integer> implements
	     TabulationDomain<Integer, BasicBlockInContext<IExplodedBasicBlock>> {

	   public boolean hasPriorityOver(PathEdge<BasicBlockInContext<IExplodedBasicBlock>> p1,
	       PathEdge<BasicBlockInContext<IExplodedBasicBlock>> p2) {
	     // don't worry about worklist priorities
	     return false;
	   }
	 }
	
}

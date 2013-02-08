package edu.colorado.thresher;

import java.util.Iterator;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.dataflow.graph.AbstractMeetOperator;
import com.ibm.wala.dataflow.graph.BitVectorFramework;
import com.ibm.wala.dataflow.graph.BitVectorIdentity;
import com.ibm.wala.dataflow.graph.BitVectorSolver;
import com.ibm.wala.dataflow.graph.BitVectorUnion;
import com.ibm.wala.dataflow.graph.BitVectorUnionVector;
import com.ibm.wala.dataflow.graph.ITransferFunctionProvider;
import com.ibm.wala.fixpoint.BitVectorVariable;
import com.ibm.wala.fixpoint.UnaryOperator;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.intset.BitVector;
import com.ibm.wala.util.intset.MutableMapping;

/**
 * dataflow analysis that lists the set of {@linkCGNode}'s that may have been called at each block 
 * @author sam
 *
 */
public class IntraprocReachingCalls {
	private final MutableMapping<CGNode> nodeIntMapping = MutableMapping.make();
	private final CGNode node;
	private final CallGraph graph;
	
	public IntraprocReachingCalls(CGNode node, CallGraph graph) {
		this.node = node;
		this.graph = graph;
		createNodeIntMapping();
	}
	
	private void createNodeIntMapping() {
		Iterator<CallSiteReference> calls = node.iterateCallSites();
		while (calls.hasNext()) {
			CallSiteReference site = calls.next();
			Set<CGNode> targets = graph.getPossibleTargets(node, site);
			for (CGNode target : targets) {
				nodeIntMapping.add(target);
			}
		}
	}
	
	public CGNode getCorrespondingNode(int index) {
		return nodeIntMapping.getMappedObject(index);
	}
	
	public BitVectorSolver<ISSABasicBlock> analyze() {
		Graph<ISSABasicBlock> cfg = node.getIR().getControlFlowGraph();
		BitVectorFramework<ISSABasicBlock,CGNode> framework = new BitVectorFramework<ISSABasicBlock,CGNode>(cfg, new TransferFunctions(), nodeIntMapping);
		BitVectorSolver<ISSABasicBlock> solver = new BitVectorSolver<ISSABasicBlock>(framework);
		try {
			solver.solve(null);
		} catch (CancelException e) {
			// this shouldn't happen
			Assertions.UNREACHABLE();
		}
		return solver;
	 }
    
	 private class TransferFunctions implements ITransferFunctionProvider<ISSABasicBlock, BitVectorVariable> {
        
    	public UnaryOperator<BitVectorVariable> getEdgeTransferFunction(ISSABasicBlock src, ISSABasicBlock dst) {
    		throw new UnsupportedOperationException();
    	}

	    /**
	     * our meet operator is set union
	     */
	    public AbstractMeetOperator<BitVectorVariable> getMeetOperator() {
	    	return BitVectorUnion.instance();
	    }
    
        public UnaryOperator<BitVectorVariable> getNodeTransferFunction(ISSABasicBlock blk) {
        	Iterator<SSAInstruction> instrIter = blk.iterator();
    		while (instrIter.hasNext()) {
    			SSAInstruction instr = instrIter.next();
    			if (instr instanceof SSAInvokeInstruction) {
    				SSAInvokeInstruction invoke = (SSAInvokeInstruction) instr;
    				Set<CGNode> targets = graph.getPossibleTargets(node, invoke.getCallSite());
    				if (targets == null) break; // safe to return here because each block will have at most one call instruction
    				BitVector v = new BitVector(nodeIntMapping.getSize());
    	            // get all call targets from this call instruction and add to set
    				for (CGNode target : targets) {
    					v.set(nodeIntMapping.getMappedIndex(target));
    				}
    				// safe to return here because each block will have at most one call instruction
    				return new BitVectorUnionVector(v);
    			}
    		}
        	// if no calls, nothing to add to our set
        	return BitVectorIdentity.instance();
        }
    	
	    // edge transfer functions propagate the call set from one node to another
	    public boolean hasEdgeTransferFunctions() {
	    	return false;
	    }
	
	    // node transfer functions collect the set of call targets in each node
	    public boolean hasNodeTransferFunctions() {
	    	return true;
	    }
    }
}

package edu.colorado.thresher;

import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;

public abstract class AbstractQuery implements IQuery {
	@Override
	public boolean foundWitness() { return false; }
	
	@Override 
	public boolean isFeasible() { return false; }
	
	@Override
	public IQuery deepCopy() {
		Util.Unimp("deep copying");
		return this;
	}
	
	@Override
	public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranchFeasible) {
		Util.Unimp("adding constraint from branch point");
		return true;
	}
	
	@Override
	public List<IQuery> visitPhi(SSAPhiInstruction instr, int phiIndex, IPathInfo currentPath) { return IQuery.FEASIBLE; } 
	
	@Override
	public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) { return IQuery.FEASIBLE; }
	
	@Override
	public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath, Set<PointsToEdge> refuted) { return IQuery.FEASIBLE; }
	
	@Override
	public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) { return IQuery.FEASIBLE; }
	
	@Override
	public List<IQuery> returnFromCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) { return IQuery.FEASIBLE; }
	
	@Override 
	public boolean containsStaleConstraints(CGNode currentNode) { return false; }
	
	@Override
	public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) { return true; }
	
	@Override
	public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee) { } // do nothing
	
	@Override
	public void declareFakeWitness() { } // do nothing
	
	@Override
	public boolean addContextualConstraints(CGNode node, IPathInfo currentPath) { return true; }
	
	@Override
	public void removeAllLocalConstraints() { } // do nothing
	
	//@Override
	//public Set<CGNode> getMethodsRelevantToQuery() { return null; }
	
	@Override
	public Map<Constraint,Set<CGNode>> getModifiersForQuery() { return null; }
	
	@Override
	public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {}
	
	@Override
	public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) { return false; }

	@Override
	public void enterCallFromJump(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) { } // do nothing

	@Override
	public void intializeStaticFieldsToDefaultValues() { } // do nothing
	
	@Override
	public boolean contains(IQuery other) { return false; }
	
	@Override
	public int hashCode() { return 5; }
	
}

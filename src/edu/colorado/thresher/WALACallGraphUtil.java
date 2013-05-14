package edu.colorado.thresher;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;

public final class WALACallGraphUtil {
  
  /**
   * @return all SSAInvokeInstructions that call callee. Each instruction is returned in a pair with its containing CGNode.
   */
  public static Collection<Pair<SSAInvokeInstruction,CGNode>> getCallInstrsForNode(CGNode node, CallGraph cg) {
    return getCallInstrsForNodes(Collections.singleton(node), cg);
  }
  
  /**
   * @return all SSAInvokeInstructions that call callee. Each instruction is returned in a pair with its containing CGNode.
   */
  public static Collection<Pair<SSAInvokeInstruction,CGNode>> getCallInstrsForNodes(Set<CGNode> nodes, CallGraph cg) {
    List<Pair<SSAInvokeInstruction,CGNode>> invokes = new ArrayList<Pair<SSAInvokeInstruction,CGNode>>();
    
    for (CGNode node : nodes) { 
      Iterator<CGNode> preds = cg.getPredNodes(node);
      while (preds.hasNext()) { // for each CGNode caller that may call callee in some context
        CGNode pred = preds.next();
        IR ir = pred.getIR();
        SSAInstruction[] instrs = ir.getInstructions();
        Iterator<CallSiteReference> sites = cg.getPossibleSites(pred, node);
        while (sites.hasNext()) { // for each call site that may dispatch to callee
          CallSiteReference site = sites.next();
          IntSet indices = ir.getCallInstructionIndices(site);
          IntIterator indexIter = indices.intIterator();
          while (indexIter.hasNext()) { // for each invocation of a call site
            int callIndex = indexIter.next();
            Util.Assert(instrs[callIndex] instanceof SSAInvokeInstruction);
            SSAInvokeInstruction instr = (SSAInvokeInstruction) instrs[callIndex];
            invokes.add(Pair.make(instr, pred));
          }
        }
      }
    }
    return invokes;
  }
  
  /**
   * @return all SSAInvokeInstructions that call callee. Each instruction is returned in a pair with its containing CGNode.
   */
  public static Collection<Pair<SSAInvokeInstruction,CGNode>> getCallInstrsForMethod(MethodReference callee, CallGraph cg) {
    Set<CGNode> nodes = cg.getNodes(callee);
    return getCallInstrsForNodes(nodes, cg);
  }
  
}

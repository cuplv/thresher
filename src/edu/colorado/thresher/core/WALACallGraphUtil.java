package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphTransitiveClosure;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.functions.Function;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.OrdinalSet;

public final class WALACallGraphUtil {
  
  public static Map<CGNode, OrdinalSet<CGNode>> getCallGraphTransitiveClosure(final CallGraph callGraph) {
    Util.Pre(callGraph != null);
    Map<CGNode, Collection<CGNode>> resultMap = CallGraphTransitiveClosure.collectNodeResults(callGraph,
        new Function<CGNode, Collection<CGNode>>() {
          public Set<CGNode> apply(CGNode node) {
            return Util.iteratorToSet(callGraph.getSuccNodes(node));
          }
        });
    return CallGraphTransitiveClosure.transitiveClosure(callGraph, resultMap); 
  }
  
  /**
   * @return all SSAInvokeInstructions that call callee. Each instruction is returned in a pair with its containing CGNode.
   */
  public static Collection<Pair<SSAInvokeInstruction,CGNode>> getCallInstrsForNode(CGNode node, CallGraph cg) {
    return getCallInstrsForNodes(Collections.singleton(node), cg);
  }
  
  /**
   * 
   * @param caller
   * @param callee
   * @param cg
   * @return all instruction indices corresponding to possilble calls of @param calle in @caller according to @param cg
   */
  public static Collection<Integer> getCallInstrIndices(CGNode caller, CGNode callee, CallGraph cg) {
    Set<Integer> siteIndices = HashSetFactory.make();
    IR callerIR = caller.getIR();
    Iterator<CallSiteReference> sites = cg.getPossibleSites(caller, callee);
    while (sites.hasNext()) { // for each each caller
      CallSiteReference possibleCaller = sites.next();
      // caller may call callee multiple times. consider each call site
      IntSet indices = callerIR.getCallInstructionIndices(possibleCaller);
      for (IntIterator indexIter = indices.intIterator(); indexIter.hasNext();) {
        siteIndices.add(indexIter.next());
      }
    }
    return siteIndices;
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
    //Util.Assert(!nodes.isEmpty(), "no nodes for " + callee);
    return getCallInstrsForNodes(nodes, cg);
  }
  
  public static boolean isLibraryMethod(CGNode node) {
    return node.getMethod().getDeclaringClass().getClassLoader().getReference().
        equals(ClassLoaderReference.Primordial);
  }
  
}

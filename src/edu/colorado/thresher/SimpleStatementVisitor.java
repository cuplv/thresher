package edu.colorado.thresher;

import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSANewInstruction;

public class SimpleStatementVisitor extends SSAInstruction.Visitor {

  private CGNode node;
  private CallGraph cg;
  private int snkId;
  private Map<SSAInstruction, Integer> instrLineMap;
  private boolean foundSink;

  public SimpleStatementVisitor(CGNode node, CallGraph cg, Map<SSAInstruction, Integer> instrLineMap, int snkId) {
    this.node = node;
    this.cg = cg;
    this.instrLineMap = instrLineMap;
    this.snkId = snkId;
    foundSink = false;
  }

  /*
   * @Override public void visitNew(SSANewInstruction instruction) {
   * 
   * 
   * }
   */

  @Override
  public void visitInvoke(SSAInvokeInstruction instruction) {
    CallSiteReference ref = instruction.getCallSite();
    // check if we have a summary for method
    // if not, dive into the method and create one
    Set<CGNode> targets = cg.getPossibleTargets(node, ref);
    // not sure what to do with dynamic dispatch information; abort if we get
    // any
    assert targets.size() == 1;
    System.err.println("Executing call!");
    for (CGNode target : targets) {
      // symbolically execute this call
      SSACFG cfg = target.getIR().getControlFlowGraph();
      SSACFG.BasicBlock entry = cfg.entry();
      System.err.println(entry);
      List<SSAInstruction> instrs = entry.getAllInstructions();
      for (SSAInstruction instr : instrs) {
        System.err.println("CALL INSTR: " + instr);
        if (instrLineMap.get(instr) == snkId) {
          // if so check, that our constraints hold
          // int result = checkConstraints(assumes, asserts, evt);
          System.err.println("FOUND SINK!");
          foundSink = true;
          return;
        }

        // instr.visit(this);
      }

    }

  }

}

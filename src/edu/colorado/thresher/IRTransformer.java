package edu.colorado.thresher;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstruction;

/**
 * transforms the unstructured control flow of WALA IR into a structured, high-level IR 
 * consisting of a list of statements. the statements we emit include all of the WALA 
 * SSA instructions (minus goto) as well as while(), if(), break, and continue.
 * @author sam
 *
 */
public class IRTransformer {

  public IRTransformer() {
    
  }
  
  /*
  public List<Instruction> transform(IR ir) {
    Util.Print("IR " + ir);
    SSACFG cfg = ir.getControlFlowGraph();
    return transform(cfg, ir, cfg.entry());
  }
  
  public List<Instruction> transform(SSACFG cfg, IR ir, ISSABasicBlock startBlk) {
    List<Instruction> output = new ArrayList<Instruction>();
    Iterator<SSAInstruction> instrs = startBlk.iterator();
    if (WALACFGUtil.isLoopHead((SSACFG.BasicBlock) startBlk, ir)) {
      // do...while loop case
      Util.Assert(startBlk.getLastInstruction() instanceof SSAConditionalBranchInstruction);
      Util.Unimp("loops not handled!");
    } else if (startBlk.getLastInstruction() instanceof SSAConditionalBranchInstruction)) {
      // branching
    } 
    // else, normal instruction
    
    
    
    List<ISSABasicBlock> toExplore = new ArrayList<ISSABasicBlock>();
    toExplore.add(entry);
    while (!toExplore.isEmpty()) {
      ISSABasicBlock blk  = toExplore.remove(0);
            
      Iterator<SSAInstruction> instrs = blk.iterator();
      boolean cond = false;
      while (instrs.hasNext()) {
        SSAInstruction instr = instrs.next();
        
        if (instr instanceof SSAConditionalBranchInstruction) {
          Util.Unimp("branching");
        }
        
        output.add(new Instruction(instr));
      }
      // TODO: optionally output exceptional control flow
      Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(blk);
      if (succs.size() > 1) {
        // conditional branch or loop
        Util.Unimp("branching");
      }
      
      for (ISSABasicBlock succ : succs) {
        toExplore.add(succ);
      }
    }
    Util.Print(Util.printCollection(output));
    return output;
    return null;
  }
  
  public ISSABasicBlock transformBlk(IR ir, SSACFG cfg, ISSABasicBlock blk) {
    Iterator<SSAInstruction> instrs = blk.iterator();
    // TODO: optionally output exceptional control flow
    Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(blk);
    switch (succs.size()) {
      case 1:
        while (instrs.hasNext())
        return succs.iterator().next();
        break;
      case 2:
        Util.Assert(!WALACFGUtil.isLoopHead((SSACFG.BasicBlock) blk, ir));
        return makeBranch();
        break;
      default:
        Util.Assert(succs.isEmpty());
        return null;
    }
    
  }
  
  public List<Instruction> transformBranch(IR ir, ISSABasicBlock branchBlk) {
    List<Instruction> output = new ArrayList<Instruction>();
    SSACFG cfg = ir.getControlFlowGraph();
    List<ISSABasicBlock> toExplore = new ArrayList<ISSABasicBlock>();
    toExplore.add(branchBlk);
    while (!toExplore.isEmpty()) {
      ISSABasicBlock blk  = toExplore.remove(0);
      if (cfg.getPredNodeCount(branchBlk) > 1) {
        // join point
        continue;
      }
      Iterator<SSAInstruction> instrs = blk.iterator();
    }
  }
  
  class Instruction {
    private final SSAInstruction instr;
    public Instruction(SSAInstruction instr) {
      Util.Assert(!(instr instanceof SSAGotoInstruction));
      this.instr = instr;
    }
    
    @Override
    public String toString() {
      return instr.toString();
    }
  }
  
  class ConditionalInstr {
    
    public ConditionalInstr(SSAConditionalBranchInstruction cond) {
      
    }
    
  }
  */
  
}

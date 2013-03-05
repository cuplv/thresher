package edu.colorado.thresher;

import java.util.Set;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.util.collections.HashSetFactory;

/**
 * represents a conditional branch instruction and the paths on each of its
 * branches (true and false) that we have seen so far
 * 
 * @author sam
 * 
 */
public class IBranchPoint {

  private final SSAInstruction instr;
  private final int lineNum;
  private final SSACFG.BasicBlock blk;
  private final IR ir;
  private final CGNode node;
  private final SymbolTable symbolTable; // symbolTable for the method
                                         // containing this point
  // paths that we have seen on the true/false branch of this instruction
  private final Set<IPathInfo> truePaths, falsePaths;
  // does this branch point correspond to a loop head?
  private final boolean loopHead;
  private final String branchPointKey;
  public final int id;

  private static final int DUMMY_ID = -1;
  private static int idCounter = 0;

  public static IBranchPoint makeBranchPoint(SSAConditionalBranchInstruction instr, int lineNum, SSACFG.BasicBlock blk, CGNode node) {
    return new IBranchPoint(instr, lineNum, blk, node, false, idCounter++);
  }

  public static IBranchPoint makeBranchPoint(SSAInstruction instr, int lineNum, SSACFG.BasicBlock blk, CGNode node, boolean loopHead) {
    return new IBranchPoint(instr, lineNum, blk, node, loopHead, idCounter++);
  }

  public static IBranchPoint makeDummyBranchPoint() {
    return new IBranchPoint();
  }

  private IBranchPoint() {
    this.instr = null;
    this.ir = null;
    this.lineNum = -1;
    this.blk = null;
    this.symbolTable = null;
    this.node = null;
    this.loopHead = false;
    this.truePaths = null;
    this.falsePaths = null;
    this.branchPointKey = null;
    this.id = DUMMY_ID;
  }

  private IBranchPoint(SSAInstruction instr, int lineNum, SSACFG.BasicBlock blk, CGNode node, boolean loopHead, int id) {
    SSACFG cfg = node.getIR().getControlFlowGraph();
    // Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(blk);
    // Util.Assert(succs.size() == 2, "branch should go exactly two ways; " +
    // blk + " goes " + succs.size());
    this.instr = instr;
    this.lineNum = lineNum;
    this.blk = blk;
    this.node = node;
    this.ir = node.getIR();
    this.symbolTable = ir.getSymbolTable();
    this.truePaths = HashSetFactory.make();
    this.falsePaths = HashSetFactory.make();
    this.branchPointKey = makeBranchPointKey(instr, blk, node);
    this.loopHead = loopHead;
    this.id = id;
    Util.Debug("creating branch point " + this.toString());
  }

  public void addNewPath(IPathInfo path) {
    Util.Pre(path.isFeasible(), "shouldn't add infeasible paths to branch points");
    Util.Pre(path.getLastBlock() != null, "need last block to be set here");
    path.setAtBranchPoint(true);
    // Util.Pre(path.getCurrentBlock().equals(this.blk),
    // "current path is in blk " + path.getCurrentBlock() +
    // "; branch point blk is " + this.blk);
    // true branch is always the first one
    boolean trueBranch = this.ir.getControlFlowGraph().getNormalSuccessors(this.blk).iterator().next().equals(path.getLastBlock());
    Util.Debug("adding path " + path + " as " + trueBranch + " branch for " + id + ": " + this.instr);
    if (trueBranch) {
      IPathInfo.mergePathWithPathSet(path, truePaths);
    } else {
      IPathInfo.mergePathWithPathSet(path, falsePaths);
    }
  }

  public boolean addPathToLoopHead(IPathInfo path) {
    Util.Pre(path.isFeasible(), "shouldn't add infeasible paths to loop head");
    Util.Pre(path.getLastBlock() != null, "need last block to be set here");
    // true branch is always the first one
    Util.Debug("adding loop head path " + path + id + ": " + this.instr + "; have " + truePaths.size());

    return IPathInfo.mergePathWithPathSet(path, truePaths);
  }

  public boolean isLoopHead() {
    return loopHead;
  }

  public static String makeBranchPointKey(SSAInstruction instr, SSACFG.BasicBlock blk, CGNode node) {
    return blk + " " + instr + " " + node.toString();
  }

  public String getBranchPointKey() {
    return branchPointKey;
  }

  public Set<IPathInfo> getTruePaths() {
    return truePaths;
  }

  public Set<IPathInfo> getFalsePaths() {
    return falsePaths;
  }

  public SSACFG.BasicBlock getBlock() {
    return blk;
  }

  public CGNode getMethod() {
    return node;
  }

  public SymbolTable getSymbolTable() {
    return symbolTable;
  }

  public SSAConditionalBranchInstruction getInstr() {
    Util.Assert(instr instanceof SSAConditionalBranchInstruction,
        "should only call this on branch points triggered by conditionals!");
    return (SSAConditionalBranchInstruction) instr;
  }

  public IR getIR() {
    return ir;
  }

  public int getLineNum() {
    return lineNum;
  }

  public int getId() {
    return id;
  }

  public boolean isDummy() {
    return this.id == DUMMY_ID;
  }

  @Override
  public String toString() {
    return this.id + ": " + this.instr + " " + this.node;
  }

}

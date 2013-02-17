package edu.colorado.thresher;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.util.collections.Pair;

/**
 * path-sensitive symbolic executor that uses "branch points" optimization to
 * merge paths at conditional branches / loop heads
 * 
 * @author sam
 */
public class OptimizedPathSensitiveSymbolicExecutor extends PathSensitiveSymbolicExecutor {

  private final HashMap<String, IBranchPoint> branchPointMap;
  LinkedList<IBranchPoint> branchPointStack;
  // map from (CGNode, Block#) -> set of paths seen at block
  private final Map<Pair<CGNode, Integer>, Set<IPathInfo>> loopHeadSeenPaths;

  Set<PointsToEdge> refuted; // set of edges that were already refuted
  private static final Set<PointsToEdge> EMPTY_SET = new HashSet<PointsToEdge>(0);

  public OptimizedPathSensitiveSymbolicExecutor(CallGraph callGraph, Logger logger) {
    this(callGraph, logger, EMPTY_SET);
  }

  public OptimizedPathSensitiveSymbolicExecutor(CallGraph callGraph, Logger logger, Set<PointsToEdge> refuted) {
    super(callGraph, logger);
    this.branchPointMap = new HashMap<String, IBranchPoint>();
    this.branchPointStack = new LinkedList<IBranchPoint>();
    this.refuted = refuted;
    this.loopHeadSeenPaths = new HashMap<Pair<CGNode, Integer>, Set<IPathInfo>>();
  }

  @Override
  boolean handleLoopHead(IPathInfo info, SSAInstruction instr) {
    Util.Pre(WALACFGUtil.isLoopHead(info.getCurrentBlock(), info.getCurrentNode().getIR()), "only call this on paths at loop head!");
    if (Options.DEBUG) Util.Debug("at loop head on path " + info.getPathId());
    final String key = IBranchPoint.makeBranchPointKey(instr, info.getCurrentBlock(), info.getCurrentNode());
    IBranchPoint point = branchPointMap.get(key);
    final SSACFG.BasicBlock currentBlock = info.getCurrentBlock();
    final CGNode node = info.getCurrentNode();
    final IR ir = node.getIR();

    // normalize query w.r.t to loop produceable constraints in order to get
    // more mileage out of summaries
    info.removeLoopProduceableConstraints(currentBlock);
    if (info.foundWitness()) return true;

    // use summaries to avoid redundant exploration
    Pair<CGNode, Integer> loopKey = Pair.make(info.getCurrentNode(), info.getCurrentBlock().getNumber());
    Set<IPathInfo> seen = loopHeadSeenPaths.get(loopKey);
    if (seen == null) { // don't have a summary list for this loop head
      seen = new HashSet<IPathInfo>();// new TreeSet<IPathInfo>();
      loopHeadSeenPaths.put(loopKey, seen);
      seen.add(info);
    } else { // do have a summary list for this loop head
      if (Options.SUBSUMPTION_CHECK_AT_SUMMARIES) {
        List<IPathInfo> toRemove = new LinkedList<IPathInfo>();
        for (IPathInfo path : seen) {
          if (info.containsQuery(path)) { // have we seen a simpler path?
            if (Options.DEBUG)
              Util.Debug("refuted by loop summary: " + path + " simpler than " + info);
            info.refute();
            return false;
          } else if (path.containsQuery(info)) { // no; is this one simpler?
            if (Options.DEBUG)
              Util.Debug("this path simpler than one we've seen; swapping");
            toRemove.add(path);
          }
        }
        seen.removeAll(toRemove);
        seen.add(info);
      } else { // just do regular check
        // check if we've seen this path already
        if (!seen.add(info)) {
          if (Options.DEBUG)
            Util.Debug("refuted by loop summary");
          info.refute();
          return false;
        } // else, haven't seen it; continue execution as normal
      }
    }

    boolean seenLoopHead = false;
    // if (info.seenLoopHead(currentBlock)) {
    // TODO: hack to deal with stupid labeled break/continue control flow. in
    // reality, we want point != null <==> info.seenLoopHead()
    if (info.seenLoopHead(currentBlock) && (point != null)) {
      // info.removeLoopProduceableConstraints(currentBlock);
      if (Options.DEBUG)
        Util.Debug("already seen loop head");
      // Util.Assert(point != null, "should already have branch point!");
      // check if we've seen this path at the loop head before

      if (!point.addPathToLoopHead(info)) {
        if (Options.DEBUG)
          Util.Debug("already seen this path... stopping execution");
        // Thread.dumpStack();
        executeAllNonPhiInstructionsInCurrentBlock(info);
        if (Options.CHECK_ASSERTS)
          split = true;
        return false; // already seen this path at the loop head; don't keep
                      // executing
      }
      this.logger.logPathWithRelevantLoop(info);
      // else, haven't seen this path before; keep executing
      if (Options.DEBUG)
        Util.Debug("haven't seen this particular path at the loop head before - continuing");
      seenLoopHead = true;
    }
    if (Options.DEBUG)
      Util.Debug("haven't seen loop head before");
    if (!seenLoopHead) {
      if (Options.DEBUG)
        Util.Debug("adding loop merge indicator for block " + currentBlock);
      addLoopMergePlaceholder(currentBlock);
    }
    LinkedList<IPathInfo> splitPaths = new LinkedList<IPathInfo>(); // list to
                                                                    // hold list
                                                                    // of split
                                                                    // paths if
                                                                    // split
                                                                    // occurs
                                                                    // before
                                                                    // end of
                                                                    // block
    int pathCount = this.pathsToExplore.size();
    if (!executeAllInstructionsInLoopHeadSequence(info, splitPaths)) {
      if (Options.CHECK_ASSERTS)
        split = true; // split in loop head sequence
      return false;
    }
    if (Options.DEBUG) {
      Util.Assert(pathCount == this.pathsToExplore.size(), "should not have added or removed any paths here!");
      Util.Debug("done with loop head sequence");
      Util.Assert(!splitPaths.isEmpty(), "path should split after loop!");
    }
    if (point == null) {
      point = IBranchPoint.makeBranchPoint(instr, info.getCurrentLineNum(), currentBlock, node, true);
      pushBranchStack(point);
      branchPointMap.put(key, point);
    }

    // boolean seenEscape = false;
    // have already done path split; add to paths to explore and return
    for (IPathInfo choice : splitPaths) {
      if (choice.isFeasible()) {
        if (WALACFGUtil.isLoopEscapeBlock(choice.getCurrentBlock(), currentBlock, ir)) {
          if (Options.DEBUG)
            Util.Debug("loop escape block " + choice.getCurrentBlock());
          // seenEscape = true;
          // don't execute loop escape path until we've seen all paths through
          // the loop; stash it in branch point
          if (!seenLoopHead)
            point.addPathToLoopHead(choice);
        } else {
          // path through the loop - need to execute
          addPath(choice);
        }
      }
    }
    // Util.Assert(seenEscape, "can't find escape block for " + currentBlock);
    if (Options.CHECK_ASSERTS)
      split = true;
    return false; // don't want to continue executing here
  }

  /**
   * special branch point-creating visitor for conditional branch instructions
   */
  @Override
  boolean visitConditional(SSAConditionalBranchInstruction instr, IPathInfo info) {
    final SSACFG.BasicBlock currentBlock = info.getCurrentBlock();
    if (Options.DEBUG)
      Util.Debug("visiting cond " + instr + " current block is " + currentBlock);
    if (WALACFGUtil.isLoopHead(currentBlock, info.getCurrentNode().getIR())) {
      return handleLoopHead(info, instr);
    } // else, is not a loop head
    String key = IBranchPoint.makeBranchPointKey(instr, info.getCurrentBlock(), info.getCurrentNode());
    IBranchPoint point = branchPointMap.get(key);
    CGNode node = info.getCurrentNode();

    // is there already a branch point for this instruction?
    if (point == null) { // creating new branch point
      point = IBranchPoint.makeBranchPoint(instr, info.getCurrentLineNum(), currentBlock, node);
      branchPointMap.put(key, point);
      pushBranchStack(point);
    }
    point.addNewPath(info);
    if (Options.CHECK_ASSERTS)
      split = true;
    return false; // never want to continue execution after a conditional branch
                  // instruction - only after branch point is merged
  }

  /**
   * remove and return a path from paths to explore. override to change
   * exploration strategy. default is DFS
   * 
   * @return path removed from pathsToExplore
   */
  @Override
  public IPathInfo selectPath() {
    if (!pathsToExplore.isEmpty()) {
      IPathInfo path = pathsToExplore.removeFirst();
      if (path.isLoopMergeIndicator()) { // special case for merging loops; we
                                         // must do so eagerly or we will drop
                                         // too many constraints
        if (Options.DEBUG) Util.Debug("forcing loop merge");
        if (!branchPointStack.isEmpty())
          return mergeBranchPointForLoopHead(path.getCurrentBlock()); 
                                                                      
        else
          return this.selectPath(); // else do nothing
        // else Util.Assert(false, "couldn't find branch point for loop head " +
        // path.getCurrentBlock());
      }
      if (Options.DEBUG)
        Util.Assert(path != null, "path should never be null here!");
      return path; // "normal" case; return path on top of stack
    } else {
      if (!branchPointStack.isEmpty())
        return mergeNextBranchPoint(); // no paths left in stack; merge branch
                                       // points, if there are any
      else
        return null; // no paths left in stack and no branch points left to
                     // merge
    }
  }

  /**
   * returns null if we can't get a non-dummy path. should never return loop
   * merge indicator or dummy path
   * 
   * @return
   */
  public IPathInfo selectNonDummyPath() {
    IPathInfo path = null;
    if (pathsToExplore.peek().isDummy() && branchPointStack.peek().isDummy()) { // are
                                                                                // there
                                                                                // any
                                                                                // non-dummy
                                                                                // paths
                                                                                // or
                                                                                // branch
                                                                                // pts?
      path = null;
    } else if (!pathsToExplore.peek().isDummy()) { // there are non-dummy paths
      path = pathsToExplore.removeFirst();
      while (path.isLoopMergeIndicator()) {
        path = mergeBranchPointForLoopHead(path.getCurrentBlock());
        if (path == null)
          return selectNonDummyPath();
      }
      if (path.isDummy()) {
        if (Options.DEBUG)
          Util.Assert(this.branchPointStack.peek().isDummy(), "expect null branch point stack here!");
        this.pathsToExplore.addFirst(path); // replace path and return null;
                                            // we're done
        if (Options.DEBUG)
          Util.Debug("replacing dummy path on stack");
        path = null;
      }
      // else, can simply return path
    } else if (!branchPointStack.peek().isDummy()) { // no paths left to
                                                     // explore; need to merge
                                                     // branch point
      IBranchPoint point = branchPointStack.removeFirst();
      path = mergeBranchPoint(point);
      while (path.isLoopMergeIndicator()) {
        path = mergeBranchPointForLoopHead(path.getCurrentBlock());
        if (path == null)
          return selectNonDummyPath();
      }
      if (path.isDummy()) {
        if (Options.DEBUG)
          Util.Assert(this.branchPointStack.peek().isDummy(), "expect null branch point stack here!");
        this.pathsToExplore.addFirst(path); // replace path and return null;
                                            // we're done
        path = null;
      }

    } else
      Util.Assert(false, "impossible");
    /*
     * if (!pathsToExplore.isEmpty()) { IPathInfo path =
     * pathsToExplore.removeFirst(); if (path.isLoopMergeIndicator()) { //
     * special case for merging loops; we must do so eagerly or we will drop too
     * many constraints Util.Debug("forcing loop merge"); if
     * (!branchPointStack.isEmpty()) return
     * mergeBranchPointForLoopHead(path.getCurrentBlock()); // do merge else
     * return this.selectPath(); // else do nothing //else Util.Assert(false,
     * "couldn't find branch point for loop head " + path.getCurrentBlock()); }
     * Util.Assert(path != null, "path should never be null here!"); return
     * path; // "normal" case; return path on top of stack } else { if
     * (!branchPointStack.isEmpty()) return mergeNextBranchPoint(); // no paths
     * left in stack; merge branch points, if there are any else return null; //
     * no paths left in stack and no branch points left to merge }
     */
    if (Options.DEBUG)
      Util.Post(path == null || (!path.isDummy() && !path.isLoopMergeIndicator()), "bad path " + path);
    return path;
  }

  /**
   * 
   * @param truePaths
   *          - list of feasible paths skipping the loop
   * @param falsePaths
   *          - list of feasible paths entering the loop
   * @return
   */

  public IPathInfo mergeLoop(Set<IPathInfo> truePaths, Set<IPathInfo> falsePaths, SSACFG.BasicBlock loopHeadBlock) {
    if (Options.DEBUG)
      Util.Debug("merging loop");
    // commented out because not necessarily true... if we start in a loop, one
    // of the lists will be empty
    // Util.Assert(!truePaths.isEmpty() && !falsePaths.isEmpty(),
    // "both path lists should be non empty!");
    truePaths.addAll(falsePaths);

    // Util.Assert(!truePaths.isEmpty(), "true paths empty!");
    if (truePaths.isEmpty()) {
      if (Options.DEBUG)
        Util.Debug("no paths at loop head");
      return selectPath();
    }

    // TreeSet<IPathInfo> mergedPaths = new TreeSet<IPathInfo>();

    // boolean first = true;
    // IPathInfo base = null;

    List<IPathInfo> toAdd = new LinkedList<IPathInfo>(), toRemove = new LinkedList<IPathInfo>();
    if (Options.DEBUG)
      Util.Debug("seen " + truePaths.size() + " paths at loop head");
    for (IPathInfo path : truePaths) {
      if (Options.DEBUG)
        Util.Debug("PATH " + path);
    }

    for (IPathInfo info : truePaths) {
      info.setCurrentBlock(loopHeadBlock);
      info.setCurrentLineNum(loopHeadBlock.getAllInstructions().size() - 2); // start
                                                                             // before
                                                                             // the
                                                                             // branch
                                                                             // instr
      List<IPathInfo> cases = executeAllInstructionsInLoopHeadBlock(info);
      if (cases == IPathInfo.INFEASIBLE)
        toRemove.add(info);
      /*
       * else { for (IPathInfo path : cases) {
       * path.removeSeenLoopHead(loopHeadBlock); // forget that we saw this loop
       * head; needed for nested loops } }
       */
    }
    truePaths.addAll(toAdd);
    truePaths.removeAll(toRemove);

    for (IPathInfo info : truePaths) {
      if (!info.containsLoopProduceableConstraints(loopHeadBlock)) {
        info.removeSeenLoopHead(loopHeadBlock); // forget that we saw this loop
                                                // head; needed for nested loops
        addPath(info);
      }
    }
    // Util.Debug("starting with " + truePaths.size() + " paths");
    if (Options.DEBUG)
      Util.Debug("done merging loop; adding " + truePaths.size() + " paths");

    // TODO: if the LHS is a local and the right side is a local allocation site
    // that's not in this node, it's infeasible...

    // for (IPathInfo info : truePaths) mergedPaths.add(info);
    // Util.Debug("now " + mergedPaths.size() + " paths");
    // for (IPathInfo info : truePaths) Util.Debug("PATH " + info);
    // if (truePaths.size() > 10) Util.Unimp("why are there so many paths????");

    return selectPath();
    // at this point, base contains the path constraints that are common to all
    // paths in the loop
    /*
     * // for each query, replace constraints that could be produced in the loop
     * with their preconditions for (IPathInfo info : truePaths) {
     * info.intersectQuery(base); // drop path constraints by intersecting with
     * common constraints info.removeLoopProduceableConstraints(loopHeadBlock);
     * mergedPaths.add(info); // merge paths; removing loop produceable
     * constraints may have caused previously distinct paths to become the same
     * }
     * 
     * // run each path through the runup to the loop for (IPathInfo info :
     * mergedPaths) { info.setCurrentBlock(loopHeadBlock);
     * info.setCurrentLineNum(loopHeadBlock.getAllInstructions().size() - 2); //
     * start before the branch instr List<IPathInfo> cases =
     * executeAllInstructionsInLoopHeadBlock(info); Util.Assert(cases.isEmpty(),
     * "not expecting case split here!");
     * info.removeSeenLoopHead(loopHeadBlock); // forget that we saw this loop
     * head; needed for nested loops Util.Debug("Added loop path " + info);
     * addPath(info); } Util.Debug("done merging loop; added " +
     * mergedPaths.size() + " paths.");
     * 
     * // TODO: DEBUG only IPathInfo somePath = mergedPaths.iterator().next();
     * IR ir = somePath.getCurrentNode().getIR(); SSACFG.BasicBlock escapeBlock
     * = somePath.getCurrentBlock();
     * 
     * // loop apex is the block that is the sink of the back edge. I use the
     * term "loop head block" to refer to blocks in the loop head between the
     * loop apex // and the conditional branch instruction that actually
     * controls the loop. the loop apex is a loop head block, but not all loop
     * head blocks are the apex Collection<ISSABasicBlock> succs =
     * ir.getControlFlowGraph().getNormalSuccessors(escapeBlock);
     * Util.Assert(succs.size() == 1, "should be exactly one successor");
     * SSACFG.BasicBlock loopApex = (SSACFG.BasicBlock) succs.iterator().next();
     * // escape block should have one successor, and it should be the loop apex
     * Util.Assert(WALACFGUtil.isLoopEscapeBlock(escapeBlock, loopApex, ir),
     * "should be in loop escape block here! in block " +
     * somePath.getCurrentBlock() + " instead."); // TODO: end debug return
     * selectPath(); // return the path from the top of the path stack
     */
  }

  /*
   * public IPathInfo mergeLoop(Set<IPathInfo> truePaths, Set<IPathInfo>
   * falsePaths, SSACFG.BasicBlock loopHeadBlock) { Util.Log("merging loop"); //
   * commented out because not necessarily true... if we start in a loop, one of
   * the lists will be empty //Util.Assert(!truePaths.isEmpty() &&
   * !falsePaths.isEmpty(), "both path lists should be non empty!");
   * truePaths.addAll(falsePaths);
   * 
   * Util.Assert(!truePaths.isEmpty(), "true paths empty!");
   * 
   * boolean first = true; IPathInfo base = null; // take intersection of all
   * queries; that is, "drop" constraints that may be produced in the loop for
   * (IPathInfo info : truePaths) { Util.Debug("loop intersect path " + info);
   * Util.Assert(info.isFeasible(), "infeasible path at loop head!"); if (first)
   * { base = info.deepCopy(); first = false; } else {
   * base.intersectQuery(info); } }
   * 
   * Util.Debug("continuing on " + base);
   * 
   * IR ir = base.getCurrentNode().getIR(); // execute all instructions in loop
   * head, make sure loop escape block will be taken
   * base.setCurrentBlock(loopHeadBlock);
   * base.setCurrentLineNum(loopHeadBlock.getAllInstructions().size() - 2); //
   * start before the branch instr List<IPathInfo> cases =
   * executeAllInstructionsInLoopHeadBlock(base);
   * 
   * SSACFG.BasicBlock escapeBlock = base.getCurrentBlock(); // loop apex is the
   * block that is the sink of the back edge. I use the term "loop head block"
   * to refer to blocks in the loop head between the loop apex // and the
   * conditional branch instruction that actually controls the loop. the loop
   * apex is a loop head block, but not all loop head blocks are the apex
   * Collection<ISSABasicBlock> succs =
   * ir.getControlFlowGraph().getNormalSuccessors(escapeBlock);
   * Util.Assert(succs.size() == 1, "should be exactly one successor");
   * SSACFG.BasicBlock loopApex = (SSACFG.BasicBlock) succs.iterator().next();
   * // escape block should have one successor, and it should be the loop apex
   * Util.Assert(WALACFGUtil.isLoopEscapeBlock(escapeBlock, loopApex, ir),
   * "should be in loop escape block here! in block " + base.getCurrentBlock() +
   * " instead.");
   * 
   * for (IPathInfo info : cases) { info.removeSeenLoopHead(loopHeadBlock);
   * addPath(info); } base.removeSeenLoopHead(loopHeadBlock); // forget that we
   * saw this loop head; needed for nested loops return base; }
   */

  /**
   * execute all instructions, making the phi choice corresponding to the loop
   * escape block
   */
  List<IPathInfo> executeAllInstructionsInLoopHeadBlock(IPathInfo info) {
    final IR ir = info.getCurrentNode().getIR();
    final SSACFG cfg = ir.getControlFlowGraph();
    SSACFG.BasicBlock currentBlock = info.getCurrentBlock();
    int startLine = info.getCurrentLineNum();
    List<SSAInstruction> instrs = currentBlock.getAllInstructions();
    Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);
    List<IPathInfo> caseSplits = new LinkedList<IPathInfo>();

    // make sure this isn't an explicitly infinite loop (no branching).
    // otherwise, we would spin around the loop below forever
    if (WALACFGUtil.isExplicitlyInfiniteLoop(currentBlock, ir)) { // is this
                                                                  // loop
                                                                  // explicitly
                                                                  // infinite?
      if (Options.DEBUG)
        Util.Debug("explicitly infinite loop!");
      // yes; find the block that precedes the loop, and execute backwards from
      // there
      SSACFG.BasicBlock escapeBlk = WALACFGUtil.getEscapeBlockForLoop(currentBlock, ir);
      if (escapeBlk == null)
        return IPathInfo.INFEASIBLE; // no way out, refute
      info.setCurrentBlock(escapeBlk);
      info.setCurrentLineNum(escapeBlk.getAllInstructions().size() - 1);
      caseSplits.add(info);
      return caseSplits;
    }

    caseSplits.add(info);
    info = null; // should read info out of caseSplits hereafter

    for (;;) {
      for (int i = instrs.size() - 1; i > -1; i--) {
        SSAInstruction instr = instrs.get(i);
        if (i <= startLine) {
          if (Options.DEBUG)
            Util.Debug("INSTR " + instr);
          if (instr instanceof SSAPhiInstruction) {
            int phiIndex = preds.size() - 1; // the loop escape block is always
                                             // the last choice in the phi
            // we are leaving the loop, so choose the last item on the list of
            // possible phi's (always corresponds to the escape block)
            List<IPathInfo> toAdd = new LinkedList<IPathInfo>(), toRemove = new LinkedList<IPathInfo>();
            for (IPathInfo path : caseSplits) {
              path.setCurrentLineNum(i - 1);
              List<IPathInfo> cases = visitPhi((SSAPhiInstruction) instr, path, phiIndex);
              if (cases == IPathInfo.INFEASIBLE)
                toRemove.add(path);
              else
                toAdd.addAll(cases);
            }
            caseSplits.addAll(toAdd);
            caseSplits.removeAll(toRemove);
          } else if (instr instanceof SSAInvokeInstruction) {
            for (IPathInfo path : caseSplits) {
              visitCallInLoopHead((SSAInvokeInstruction) instr, path);
            }
          } else {
            if (Options.DEBUG)
              Util.Assert(!(instr instanceof SSAConditionalBranchInstruction), "should never execute branch instr's here!");
            // "normal" case
            List<IPathInfo> toAdd = new LinkedList<IPathInfo>(), toRemove = new LinkedList<IPathInfo>();
            for (IPathInfo path : caseSplits) {
              path.setCurrentLineNum(i - 1);
              List<IPathInfo> splits = path.visit(instr);
              if (splits == IPathInfo.INFEASIBLE)
                toRemove.add(path); // infeasible
              else
                toAdd.addAll(splits);
            }
            caseSplits.addAll(toAdd);
            caseSplits.removeAll(toRemove);
            // Util.Assert(visit(instr, path), "phi made path infeasible!");
          }
        }
      }

      if (preds.size() == 1) { // keep executing straight-line code
        currentBlock = (SSACFG.BasicBlock) preds.iterator().next();
        // Util.Assert(!caseSplits.isEmpty(), "no paths left to execute!");
        if (caseSplits.isEmpty())
          return IPathInfo.INFEASIBLE;
        for (IPathInfo path : caseSplits) {
          path.setCurrentBlock(currentBlock);
        }
        startLine = currentBlock.getAllInstructions().size() - 1;
        instrs = currentBlock.getAllInstructions();
        preds = cfg.getNormalPredecessors(currentBlock);
      } else { // we've reached the splitting point. find the loop escape block
        if (Options.DEBUG)
          Util.Assert(!preds.isEmpty(), "loop should split eventually!");
        // Util.Assert(!caseSplits.isEmpty(), "no paths left to execute!");
        if (caseSplits.isEmpty())
          return IPathInfo.INFEASIBLE;
        if (preds.isEmpty())
          return caseSplits;
        for (ISSABasicBlock pred : preds) {
          SSACFG.BasicBlock nextBlock = (SSACFG.BasicBlock) pred;
          if (WALACFGUtil.isLoopEscapeBlock(nextBlock, currentBlock, ir)) {
            for (IPathInfo path : caseSplits) {
              // Util.Debug("selecting loop escape block " + nextBlock + " for "
              // + path.getPathId());
              path.setCurrentBlock(nextBlock);
              path.setCurrentLineNum(nextBlock.getAllInstructions().size() - 1);
            }
            return caseSplits;
          }
        }
        // TODO: is this the right thing to do? or a non-termination bug? this
        // is triggered by nested for each loops
        Util.Unimp("couldn't find escape block for loop head " + currentBlock + " in\n" + ir);
      }
    }
  }

  /**
   * select the branch point on the top of the stack and merge it. if it does
   * not corresponds to the loop head contained in mergeBlock, replace the loop
   * placeholder
   * 
   * @param mergeBlock
   *          - block containing the loop head we need to merge
   * @return - top path in path stack if there is one, null otherwise
   */
  public IPathInfo mergeBranchPointForLoopHead(SSACFG.BasicBlock mergeBlock) {
    if (Options.DEBUG) Util.Pre(!branchPointStack.isEmpty(), "Trying to merge with no mergeable branch points!");
    if (branchPointStack.peek().isDummy()) return null;
    IBranchPoint point = branchPointStack.pop();
    branchPointMap.remove(point.getBranchPointKey());
    if (!point.getBlock().equals(mergeBlock)) {
      // this is the not the loop we are supposed to merge; replace the
      // placeholder
      addLoopMergePlaceholder(mergeBlock);
    } // else, this was the loop head we were supposed to merge; can merge and
      // then continue execution as normal
    return mergeBranchPoint(point);
  }

  /**
   * select the branch point on the top of the stack and merge it
   * 
   * @return - top path in path stack if there is one, null otherwise
   */
  public IPathInfo mergeNextBranchPoint() {
    if (Options.DEBUG)
      Util.Pre(!branchPointStack.isEmpty(), "Trying to merge with no mergeable branch points!");
    IBranchPoint point = branchPointStack.pop();
    branchPointMap.remove(point.getBranchPointKey()); // delete this branch
                                                      // point so we don't
                                                      // double merge
    return mergeBranchPoint(point);
  }

  /**
   * merge the given branch point's paths, add feasible ones to the path stack
   * 
   * @return - top path in path stack if there is one, null otherwise
   */
  public IPathInfo mergeBranchPoint(IBranchPoint point) {
    Set<IPathInfo> truePaths = point.getTruePaths();
    Set<IPathInfo> falsePaths = point.getFalsePaths();
    Set<IPathInfo> toRemove = new HashSet<IPathInfo>();

    // remove infeasible true paths
    for (IPathInfo info : truePaths) {
      if (Options.DEBUG)
        Util.Assert(info.isFeasible(), "infeasible path " + info);
      if (!info.isFeasible())
        toRemove.add(info);
    }
    for (IPathInfo removeMe : toRemove) {
      boolean removed = truePaths.remove(removeMe);
      if (Options.DEBUG)
        Util.Assert(removed, "can't remove path!");
    }
    toRemove.clear();
    // remove infeasible false paths
    for (IPathInfo info : falsePaths) {
      // Util.Assert(info.isFeasible(), "infeasible path " + info);
      if (!info.isFeasible())
        toRemove.add(info);
    }
    for (IPathInfo removeMe : toRemove) {
      boolean removed = falsePaths.remove(removeMe);
      if (Options.DEBUG)
        Util.Assert(removed, "can't remove path!");
    }

    // at this point, an empty true/false path set means no feasible paths on
    // true/false branch
    boolean truePathsEmpty = truePaths.isEmpty();
    boolean falsePathsEmpty = falsePaths.isEmpty();
    if (Options.DEBUG)
      Util.Debug("merging branch point " + point);

    if (point.isLoopHead()) {
      // Util.visualizeIR(Options.DEBUG_cha, point.getIR(), "TEST");
      return mergeLoop(truePaths, falsePaths, point.getBlock()); // loops are a
                                                                 // special case
                                                                 // here...may
                                                                 // need to drop
                                                                 // constraints
    }

    Set<IPathInfo> toAdd = new HashSet<IPathInfo>();
    if (truePathsEmpty && falsePathsEmpty) { // no paths are feasible
      if (Options.DEBUG)
        Util.Debug("no paths feasible");
    } else if (truePathsEmpty) { // no true paths are feasible
      if (Options.DEBUG)
        Util.Debug("no true paths feasible");
      for (IPathInfo info : falsePaths) {
        // add path constraints to each path in falsePaths and continue
        if (info.addConstraintFromBranchPoint(point, false)) {
          toAdd.add(info); // path is feasible after adding constraint
        }
      }
    } else if (falsePathsEmpty) { // no false paths are feasible
      if (Options.DEBUG)
        Util.Debug("no false paths feasible");
      for (IPathInfo info : truePaths) {
        // add path constraints to each path in truePaths and continue
        if (info.addConstraintFromBranchPoint(point, true))
          toAdd.add(info); // path is feasible after adding constraint
      }
    } else { // paths on both sides are feasible
      if (Options.DEBUG)
        Util.Debug("paths feasible on both sides");
      toRemove.clear();

      for (IPathInfo falsePath : falsePaths) {
        for (IPathInfo truePath : truePaths) {
          // Util.Debug(falsePath + "\n eq\n " + truePath + "?");
          if (falsePath.equals(truePath)) {
            // we can arrive at this path regardless of if we take true path or
            // false path; we can continue on a single path with no constraints
            // added
            // problem: if two paths have the same constraints, but one of the
            // paths has seen a loop head, we want to mark the other one as
            // having
            // seen it as well. this is an efficiency question; if the
            // constraints are the same whether we make one pass or two passes
            // through the
            // loop, we would prefer not to explore the loop another time
            if (falsePath.loopsSeen() > truePath.loopsSeen())
              toAdd.add(falsePath); // continue execution on the path that has
                                    // seen more loop heads
            else
              toAdd.add(truePath);
            toRemove.add(truePath); // we could also add falsePath here; they're
                                    // the same
          }
        }
      }
      // remove paths that are in both sets from each set; we've already added
      // them to the path manager
      for (IPathInfo removeMe : toRemove) {
        boolean removed = truePaths.remove(removeMe);
        if (Options.DEBUG)
          Util.Assert(removed, "couldn't remove " + removeMe);
      }
      for (IPathInfo removeMe : toRemove) {
        boolean removed = falsePaths.remove(removeMe);
        if (Options.DEBUG)
          Util.Assert(removed, "couldn't remove " + removeMe);
      }
      // now, each path that remains must have the appropriate constraint added
      // to it
      for (IPathInfo falsePath : falsePaths) {
        if (falsePath.addConstraintFromBranchPoint(point, false))
          toAdd.add(falsePath); // add path constraint and path to path manager
      }
      for (IPathInfo truePath : truePaths) {
        if (truePath.addConstraintFromBranchPoint(point, true))
          toAdd.add(truePath); // add path constraint and path to path manager
      }
    }

    for (IPathInfo path : toAdd) {
      path.setAtBranchPoint(false);
      addPath(path);
    }

    return selectPath();
    /*
     * if (!pathsToExplore.isEmpty()){ IPathInfo next =
     * pathsToExplore.removeFirst(); // return path on the top of the stack
     * Util.Assert(!next.isLoopMergeIndicator(),
     * "loop merge indicator is the next path! " + next); return next; } return
     * null; // no paths left to explore
     */
  }

  /**
   * special case for do...while loops, which can have non-phi instructions in
   * the loop head to run through the loop, we must execute these instructions
   * (but not the phi's, since they are always executed upon exiting the loop)
   */
  boolean executeAllNonPhiInstructionsInCurrentBlock(IPathInfo path) {
    SSACFG.BasicBlock currentBlock = path.getCurrentBlock();
    int startLine = path.getCurrentLineNum();
    List<SSAInstruction> instrs = currentBlock.getAllInstructions();

    for (int i = instrs.size() - 1; i > -1; i--) {
      SSAInstruction instr = instrs.get(i);
      if (i <= startLine) {
        if (instr instanceof SSAPhiInstruction)
          break; // phi's are always the first instr's in a block
        path.setCurrentLineNum(i - 1);
        if (!visit(instr, path))
          return false;
      }
    }
    return true;
  }

  /**
   * bubble this branch point up the stack until it dominates another
   * branchInstr in the stack
   * 
   * @param newPoint
   *          - IBranchPoint to bubble
   */
  void pushBranchStack(IBranchPoint newPoint) {
    // Util.Debug("pushing " + newPoint);
    SSACFG.BasicBlock newBlk = newPoint.getBlock();
    for (int i = branchPointStack.size() - 1; i > -1; i--) {
      IBranchPoint point = branchPointStack.get(i);
      SSACFG.BasicBlock blk = point.getBlock();
      if (newPoint.getIR().equals(point.getIR())) { // make sure IR's are equal,
                                                    // else dominator check may
                                                    // fail
        if (WALACFGUtil.isDominatedBy(blk, newBlk, newPoint.getIR())) {
          // Util.Debug(blk + "is dominated by " + newBlk + "adding " + newPoint
          // + " at " + i);
          if (i == branchPointStack.size() - 1)
            branchPointStack.addLast(newPoint);
          else
            branchPointStack.add(i + 1, newPoint);
          return;
        }
      } // else, IR's don't match, so these branch points are incomparable
    }
    // this branch doesn't dominate anything; just add it first
    branchPointStack.addFirst(newPoint);
  }

  /**
   * symbolic execution in fakeWorldClinit (WALA's model of the Java class
   * initializers) requires special handling. we do not attempt to model the
   * order that static initializers are invoked in, so we ask if each class
   * initializer can produce our constraints, and execute it if so
   */
  @Override
  boolean handleFakeWorldClinit(IPathInfo path) {
    if (Options.DEBUG) Util.Debug("trying to find witness in fakeWorldClinit");
    CGNode fakeWorldClinitNode = path.getCurrentNode();
    if (Options.CHECK_ASSERTS) {
      Util.Assert(fakeWorldClinitNode.equals(WALACFGUtil.getFakeWorldClinitNode(callGraph)), fakeWorldClinitNode
          + "should be fakeWorldClinit!");
    }
    // TODO: rather than iterating over the class initializers, be a little more selective?
    if (path.foundWitness()) return true;

    SSAInstruction[] instrs = fakeWorldClinitNode.getIR().getInstructions();
    addPathAndBranchPlaceholders();
    Set<SSAInstruction> alreadyTried = new HashSet<SSAInstruction>();
    while (path != null) {
      if (!path.getCurrentNode().equals(fakeWorldClinitNode)) {
        boolean hitProcBoundary = this.executeBackwardsPathIntraprocedural(path);
        if (path.foundWitness())
          return true;
        if (hitProcBoundary) {
          if (Options.DEBUG)
            Util.Debug("hit proc boundary");
          // if (path.getCurrentNode().equals(fakeWorldClinitNode)) continue; //
          // at proc boundary for fakeWorldClinit; witness not produced
          if (!path.isCallStackEmpty()) {
            // leaving callee and returning to called method
            if (path.returnFromCall()) continue;
          }
        }
      } else {
        boolean skipInitialization = false;
        for (SSAInstruction instr : instrs) { // for each class initializer
          if (!alreadyTried.add(instr)) continue;
          if (instr == null) continue;
          // this is an instruction, not an entrypoint
          if (!(instr instanceof SSAInvokeInstruction)) { 
            if (!super.visitIPathInfoWrapper(instr, path)) break; // refuted; try next path
            if (path.foundWitness()) return true;
            continue; // not refuted or witnessed; try next instr
          }
          SSAInvokeInstruction instruction = (SSAInvokeInstruction) instr;
          Set<CGNode> targets = callGraph.getPossibleTargets(fakeWorldClinitNode, instruction.getCallSite());
          if (Options.DEBUG) {
            Util.Assert(targets.size() == 1, "Not expecting dynamic dispatch in class inits; everything should be static");
          }
          CGNode classInitializer = targets.iterator().next();
          // ask the current path if this class initializer can produce any part
          // of its query
          Util.Debug("checking relevance of " + classInitializer);
          if (path.isCallRelevantToQuery(instruction, classInitializer, callGraph)) {
            if (Options.DEBUG)
              Util.Debug("Trying class init " + instr);
            IPathInfo copy = path.deepCopy();
            // yes; push the class init on the call stack and execute it
            copy.pushCallStack(instruction, classInitializer);
            addPath(copy);
            skipInitialization = true;
            break;
          }
        } // end for each class initializer
        if (!skipInitialization) {
          path.initializeStaticFieldsToDefaultValues();
          if (path.isFeasible()) path.removeAllLocalConstraintsFromQuery();
        }
        // last constraint was a static field pointing to its default value
        if (path.foundWitness()) return true; 
      }
      path = selectNonDummyPath();
    }
    // else, still haven't produced...
    if (Options.DEBUG) Util.Debug("witness not produced in class inits! refuted.");
    if (Options.CHECK_ASSERTS) split = true;
    cleanupPathAndBranchPlaceholders();
    return false;
  }

  /**
   * symbolic execution in fakeRootMethod (WALA's model of the Java class
   * initializers) requires special handling. we do not attempt to model the
   * order that static initializers are invoked in, so we ask if each class
   * initializer can produce our constraints, and execute it if so
   */

  @Override
  boolean handleFakeRootMethod(IPathInfo path, CGNode entrypoint) {
    if (Options.DEBUG)
      Util.Pre(path.getCurrentNode().equals(this.callGraph.getFakeRootNode()), "current node should be fakeRootNode at this point!");
    if (Options.DEBUG)
      Util.Debug("trying to find witness in fakeRootMethod");

    // path.removeAllLocalConstraintsFromQuery(); // can't reason about params
    // to entrypoints
    if (path.foundWitness())
      return true;
    Set<IPathInfo> toTryInFakeWorldClinit = new HashSet<IPathInfo>();

    CGNode fakeRootMethod = path.getCurrentNode();
    SSAInstruction[] instrs = fakeRootMethod.getIR().getInstructions();
    addPathAndBranchPlaceholders();
    Set<SSAInstruction> alreadyTried = new HashSet<SSAInstruction>();
    CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(callGraph);

    while (path != null) {
      if (!path.getCurrentNode().equals(fakeRootMethod)) {
        boolean hitProcBoundary = this.executeBackwardsPathIntraprocedural(path);
        if (path.foundWitness())
          return true;
        if (hitProcBoundary) {
          if (!path.isCallStackEmpty()) {
            // leaving callee and returning to called method
            if (path.returnFromCall())
              continue; // keep executing path if it is feasible
                        // //addPath(path); // add path if it is feasible
          }
        }
      } else {
        // path is in fakeRootNode, do special entrypoint handling
        boolean split = false;
        for (SSAInstruction instr : instrs) { // for each entrypoint
          if (Options.DEBUG)
            Util.Debug("trying entrypoint instr " + instr);
          if (!alreadyTried.add(instr))
            continue; // TODO: UNSOUND. we need to allow arbitrary, but somehow
                      // bounded re-execution of class entrypoints
          if (instr == null)
            continue;
          if (!(instr instanceof SSAInvokeInstruction)) { // this is an
                                                          // instruction, but
                                                          // not an entrypoint
            if (!super.visitIPathInfoWrapper(instr, path))
              break; // refuted; try next path
            if (path.foundWitness())
              return true;
            continue; // not refuted or witnessed; try next entrypoint
          }

          SSAInvokeInstruction instruction = (SSAInvokeInstruction) instr;
          Set<CGNode> targets = callGraph.getPossibleTargets(fakeRootMethod, instruction.getCallSite());
          for (CGNode target : targets) {
            if (target.equals(fakeWorldClinit))
              continue; // class inits are handled separately
            else if (target.equals(entrypoint))
              continue; // don't want to execute our same entrypoint again
            // ask the current path if this class initializer can produce any
            // part of its query
            if (path.isCallRelevantToQuery(instruction, target, callGraph)) {
              if (Options.DEBUG)
                Util.Debug("Trying entrypoint " + instr);
              IPathInfo copy = path.deepCopy();
              // yes; push the entrypoint on the call stack and execute it
              copy.pushCallStack(instruction, target);
              addPath(copy);
              split = true;
            }
          }
          if (split)
            break; // added all targets; proceed to executing paths
        }
        if (!split && path.isFeasible())
          toTryInFakeWorldClinit.add(path); // tried all entrypoints and no
                                            // witness found here; try
                                            // fakeWorldClinit
      }
      // else, path refuted or split; pick next one
      path = selectNonDummyPath();
    }

    if (Options.DEBUG)
      Util.Debug("witness not produced in fakeRootMethod! proceeding to fakeWorldClinit");
    cleanupPathAndBranchPlaceholders();
    for (IPathInfo info : toTryInFakeWorldClinit) {
      // info.removeAllLocalConstraintsFromQuery();
      if (info.foundWitness())
        return true;
      info.setCurrentNode(WALACFGUtil.getFakeWorldClinitNode(callGraph));
      if (handleFakeWorldClinit(info))
        return true;
    }
    // didn't produce a witness anywhere; return false
    return false;
  }

  public void addPathAndBranchPlaceholders() {
    if (Options.DEBUG)
      Util.Debug("adding path and branch placeholders");
    /*
     * DEBUG for (IPathInfo path : this.pathsToExplore) {
     * Util.Assert(!path.isDummy(),
     * "should not contain dummy paths if this is called!"); }
     * 
     * for (IBranchPoint point : branchPointStack) {
     * Util.Assert(!point.isDummy(),
     * "should not contain dummy points if this is called!"); }
     */

    this.pathsToExplore.addFirst(IPathInfo.makeDummyPath());
    this.branchPointStack.addFirst(IBranchPoint.makeDummyBranchPoint());
  }

  public void cleanupPathAndBranchPlaceholders() {
    if (Options.DEBUG)
      Util.Debug("cleaning up path and branch placeholders");
    IPathInfo poppedPath = this.pathsToExplore.pop();
    // DEBUG
    if (!poppedPath.isDummy()) {
      Util.Debug(pathsToExplore.size() + " paths");
      for (IPathInfo path : pathsToExplore) {
        Util.Debug("PATH " + path.getPathId());
      }
      Util.Assert(poppedPath.isDummy(), "popped non-dummy path! " + poppedPath);
    }

    IBranchPoint poppedBranch = this.branchPointStack.pop();
    // DEBUG
    if (!poppedBranch.isDummy()) {
      Util.Debug(branchPointStack.size() + " points");
      for (IBranchPoint point : branchPointStack) {
        Util.Debug("POINT " + point.id);
      }
      Util.Assert(poppedBranch.isDummy(), "popped non-dummy branch! " + poppedBranch);
    }

    if (!Options.PIECEWISE_EXECUTION) { // the piecwise symbolic executor
                                        // multi-stacks these; can't do this
                                        // check
      for (IPathInfo path : this.pathsToExplore) {
        Util.Assert(!path.isDummy(), "should not contain dummy paths anymore!");
      }

      for (IBranchPoint point : branchPointStack) {
        Util.Assert(!point.isDummy(), "should not contain dummy points anymore!");
      }
    }

  }

  @Override
  void end() {
    // DEBUG
    Util.Assert(this.pathsToExplore.isEmpty(), "paths to explore not empty!");
    Util.Assert(this.branchPointStack.isEmpty(), "branch point stack not empty!");
  } // do nothing

}

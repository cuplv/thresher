package edu.colorado.thresher;

import java.util.Collection;
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
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;

/**
 * interprocedural symbolic executor that precisely tracks correlations between
 * conditional branch outcomes and paths taken loops are unrolled once, though
 * all (non-looping) paths through the loop body are explored
 * 
 * @author sam
 */
public class PathSensitiveSymbolicExecutor extends BasicSymbolicExecutor {

  public PathSensitiveSymbolicExecutor(CallGraph callGraph, Logger logger) {
    super(callGraph, logger);
  }

  /**
   * @param preds
   *          - predecessors of current execution block
   * @param path
   *          - current path
   * @return - list of paths branching off of current path
   */
  void initializeSplitPaths(LinkedList<IPathInfo> splitPaths, Collection<ISSABasicBlock> preds, IPathInfo path) {
      //if (Options.DEBUG) Util.Pre(splitPaths.isEmpty(), "split path list should always be empty here! it's only to pass back");
    if (preds.size() < 2) { // sometimes, we need to add the exceptional
                            // predecessors here
      SSACFG cfg = path.getCurrentNode().getIR().getControlFlowGraph();
      Collection<ISSABasicBlock> newPreds = cfg.getExceptionalPredecessors(path.getCurrentBlock());
      preds.addAll(newPreds);
    }
    if (Options.DEBUG)
      Util.Assert(preds.size() > 1, "can't create split path lists with less than 2 preds!");

    // Util.Debug("initializing split paths; currentBlock is " +
    // path.getCurrentBlock());
    for (ISSABasicBlock blk : preds) {
      // Util.Debug("pred: " + blk);
      SSACFG.BasicBlock nextBlock = (SSACFG.BasicBlock) blk;
      IPathInfo copy = path.deepCopy();
      copy.setCurrentBlock(nextBlock);
      copy.setCurrentLineNum(nextBlock.getAllInstructions().size() - 1);
      splitPaths.push(copy);
    }
    if (Options.DEBUG)
      Util.Assert(!splitPaths.isEmpty(), "should never return empty split paths list!");
  }

  /**
   * run path through all of the instructions in the current block (backwards)
   * 
   * @param path
   *          - current path
   * @param splitPaths
   *          - list of splits the current path has taken so far
   * @param loopHead
   *          - null if the current block is not a loop head, the loop head
   *          otherwise
   * @return - true if path is feasible after executing all instructions, false
   *         otherwise
   */
  boolean executeAllInstructionsInCurrentBlock(IPathInfo path, LinkedList<IPathInfo> splitPaths, SSACFG.BasicBlock loopHead) {
    final boolean isLoopHead = (loopHead != null);
    final IR ir = path.getCurrentNode().getIR();
    final SSACFG cfg = ir.getControlFlowGraph();
    final SSACFG.BasicBlock currentBlock = path.getCurrentBlock();
    int startLine = path.getCurrentLineNum();
    List<SSAInstruction> instrs = currentBlock.getAllInstructions();
    Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);

    Map<Integer, List<IPathInfo>> phiIndexPathsMap = HashMapFactory.make();

    for (int i = instrs.size() - 1; i > -1; i--) {
      SSAInstruction instr = instrs.get(i);
      if (i <= startLine) {
        if (Options.DEBUG)
          Util.Debug("instr " + instr);
        if (instr instanceof SSAPhiInstruction) {
          // found a phi node; need to do path splitting early in order to
          // decide which value is assigned on which path
          int phiIndex = instr.getNumberOfUses() - 1;
          if (phiIndexPathsMap.isEmpty()) {
            if (splitPaths.isEmpty())
              initializeSplitPaths(splitPaths, preds, path);
            for (IPathInfo choice : splitPaths) {
              List<IPathInfo> list = new LinkedList<IPathInfo>();
              list.add(choice);
              phiIndexPathsMap.put(phiIndex, list);
              phiIndex--;
            }
            phiIndex = instr.getNumberOfUses() - 1; // reset phi index
          }

          for (; phiIndex >= 0; phiIndex--) {
            List<IPathInfo> toRemove = new LinkedList<IPathInfo>(), toAdd = new LinkedList<IPathInfo>();
            List<IPathInfo> choicesForIndex = phiIndexPathsMap.get(phiIndex);
            for (IPathInfo choice : choicesForIndex) {
              if (!isLoopHead || !WALACFGUtil.isLoopEscapeBlock(choice.getCurrentBlock(), loopHead, ir)) {
                if (Options.DEBUG)
                  Util.Debug("correlating phi index " + phiIndex + " with block " + choice.getCurrentBlock());
                List<IPathInfo> cases = visitPhi((SSAPhiInstruction) instr, choice, phiIndex);
                if (cases == IPathInfo.INFEASIBLE) {
                  // phi visit made path infeasible;
                  toRemove.add(choice);
                } else if (!cases.isEmpty()) {
                  // case split while visiting phi
                  toAdd.addAll(cases);
                }
              }
            }
            choicesForIndex.removeAll(toRemove);
            choicesForIndex.addAll(toAdd);
          }
        } else {
          // "normal" case. this should precede executing any phi instructions,
          // so we don't need to consider the case splits here
          path.setCurrentLineNum(i - 1);
          if (!visit(instr, path)) {
            // if (Options.CHECK_ASSERTS) Util.Assert(!path.isFeasible() ||
            // split,
            // "path should be marked infeasible here or we should have a split");
            return false;
          }
        }
      }
    }
    if (!phiIndexPathsMap.isEmpty()) { // push the content of the phi index map
                                       // back into split paths
      splitPaths.clear();
      for (List<IPathInfo> list : phiIndexPathsMap.values()) {
        splitPaths.addAll(list);
      }
    }
    return true;
  }

  /**
   * execute given path until it splits or reaches beginning of procedure after
   * calling this, should check if returned true, and if so, should check for
   * witness if false is returned, the next path in the list should be selected
   * and executed
   * 
   * @return true if procedure boundary is reached / witness is found, false if
   *         path splits or becomes infeasible
   */
  @Override
  public boolean executeBackwardsPathIntraprocedural(IPathInfo path) {
    if (Options.CHECK_ASSERTS) {
      boolean result = executeBackwardsPathIntraproceduralImpl(path);
      // true return => path feasible && (found witness || at procedure boundary
      // || no preds for current block)
      // can have no preds for current block but not be at an entry due to
      // exceptional control flow (we only get non-exceptional control flow)
      Util.Post(!result
          || (path.isFeasible() && (path.foundWitness() || path.getCurrentBlock().isEntryBlock() || path.getCurrentNode().getIR()
              .getControlFlowGraph().getNormalPredecessors(path.getCurrentBlock()).isEmpty())), "feasible?" + path.isFeasible()
          + " blk " + path.getCurrentBlock() + " witness " + path.foundWitness() + " path " + path);
      // false return => (path infeasible || path split)
      // TODO: this doesn't work because we'll sometimes get a false return for a feasible path
      Util.Post(result || (!path.isFeasible() || split), " post failure on  path " + path + " blk " + path.getCurrentBlock()
          + "IR " + path.getCurrentNode().getIR() + "result? " + result + "feasible? " + path.isFeasible());
      split = false;
      return result;
    }
    return executeBackwardsPathIntraproceduralImpl(path);
  }

  // wrapper to make it easy to write postcondition
  private boolean executeBackwardsPathIntraproceduralImpl(final IPathInfo path) {
    if (Options.CHECK_ASSERTS) {
      Util.Pre(!path.isDummy(), "can't execute dummy path!");
      Util.Pre(!path.isLoopMergeIndicator(), "can't execute loop merge indicator!");
    }

    final IR ir = path.getCurrentNode().getIR();
    final SSACFG cfg = ir.getControlFlowGraph();
    // until path splits into multiple paths
    for (;;) {
      // if the current block has multiple predecessors, we must choose which
      // one this path came from now in order to handle phi instructions
      // correctly.
      final SSACFG.BasicBlock currentBlock = path.getCurrentBlock();
      Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);
      // list to hold split paths if split occurs before end of block
      LinkedList<IPathInfo> splitPaths = new LinkedList<IPathInfo>();
      boolean loopHead = WALACFGUtil.isLoopHead(currentBlock, ir);
      SSACFG.BasicBlock loopHeadBlock = loopHead ? currentBlock : null;

      // execute all instructions in block
      if (!executeAllInstructionsInCurrentBlock(path, splitPaths, loopHeadBlock)) {
        return false; // path infeasible
      }

      if (path.foundWitness())
        return true;

      if (!splitPaths.isEmpty()) {
        // Util.Assert(preds.size() > 1, "expecting path split!");
        // have already done path split; add to paths to explore and return
        for (IPathInfo choice : splitPaths) {
          if (choice.isFeasible() &&
          // loopHead => (loop escape block or not seen loop head yet)
              (!loopHead || (WALACFGUtil.isLoopEscapeBlock(choice.getCurrentBlock(), currentBlock, ir) || !choice
                  .seenLoopHead(currentBlock)))) {
            addPath(choice);
          }
        }
        if (Options.CHECK_ASSERTS)
          split = true;
        return false; // path has split
      }

      if (!preds.isEmpty() && WALACFGUtil.isLoopHead(currentBlock, ir)) {
        // odd situation; in a loop head, but don't know what the conditional
        // controlling the loop is. this may happen either because we entered
        // the
        // loop head from a callee that precedes the conditional, or because
        // there's not conditional controlling the loop (it's explicitly
        // infinite)

        // if the loop is explicitly infinite, we should refute if our path
        // entered the loop from outside, but continue if we started in the loop
        // or
        // entered via a callee

        // TODO: support refuting infinite loops that we entered from outside
        if (Options.DEBUG)
          Util.Debug("in loop, but don't know conditional");
        if (Options.DEBUG)
          Util.Assert(splitPaths.isEmpty(), "expecting empty split paths here!");
        if (WALACFGUtil.isExplicitlyInfiniteLoop(currentBlock, ir)) { // is this
                                                                      // loop
                                                                      // explicitly
                                                                      // infinite?
          // yes; find the block that precedes the loop, and execute backwards
          // from there
          SSACFG.BasicBlock escapeBlk = WALACFGUtil.getEscapeBlockForLoop(currentBlock, ir);
          if (escapeBlk == null) {
            path.refute();
            return false; // no way out, refute
          }
          path.setCurrentBlock(escapeBlk);
          path.setCurrentLineNum(escapeBlk.getAllInstructions().size() - 1);
          // return true;
          continue; // keep executing in escape block
        }
        // else, this loop is not explicitly infinite; we just don't know the
        // conditional yet.
        return handleLoopHead(path, currentBlock.getLastInstruction());
      }

      /*
       * // if we reach this point the current block should NOT be a loop head
       * (unless we're leaving a proc whose first block is a loop head)
       * Util.Assert(preds.isEmpty() || !WALACFGUtil.isLoopHead(currentBlock,
       * ir), "not expecting loop head here! BLK " + currentBlock + "IR:\n" + ir
       * + "preds: " + preds.size());
       */

      // have executed all instructions in currentBlock. proceed to
      // predecessors, if there are any
      if (preds.isEmpty()) { // no preds;
        if (currentBlock.isEntryBlock())
          return true; // at proc boundary; return true
        Util.Debug("refuted by thrown exception");
        path.refute();
        return false; // else, means we're in a block with only exceptional
                      // predecessors
      } else if (preds.size() == 1) {
        // optimization: for the single predecessor case, can execute next block
        // directly (without any deep copying)
        SSACFG.BasicBlock nextBlock = (SSACFG.BasicBlock) preds.iterator().next();
        path.setCurrentBlock(nextBlock);
        path.setCurrentLineNum(nextBlock.getAllInstructions().size() - 1);
      } else {
        initializeSplitPaths(splitPaths, preds, path);
        for (IPathInfo newPath : splitPaths) {
          // check if we are branching into a loop
          SSACFG.BasicBlock possibleLoopHead = WALACFGUtil.getLoopHeadForBlock(newPath.getCurrentBlock(), ir);
          Util.Debug("branching into loop?");
          if (possibleLoopHead != null) {
            Util.Debug("true");
            addLoopMergePlaceholder(possibleLoopHead);
          }
          addPath(newPath);
        }
        if (Options.CHECK_ASSERTS)
          split = true;
        return false; // path has split
      }
    }
  }

  boolean handleLoopHead(IPathInfo info, SSAInstruction instr) {
    return true;
  }


  /**
   * special case for loop heads that are more than one block in length. keep
   * executing until we reach the sink of the back edge
   * @param justGetToLoopHead if true, only execute until we reach the loop head and then stop
   */
  boolean executeAllInstructionsInLoopHeadSequence(IPathInfo info, LinkedList<IPathInfo> splitPaths, 
      boolean justGetToLoopHead) {
    if (Options.DEBUG) Util.Pre(splitPaths.isEmpty(), "not expecting any split paths here!");
    // !justGetToLoopHead => path is not at loop head already
    Util.Pre(!justGetToLoopHead || 
        !WALACFGUtil.isLoopHead(info.getCurrentBlock(), info.getCurrentNode().getIR()));
    
    // list to handle case splits in straight-line code (i.e. many applicable rules)
    Set<IPathInfo> cases = HashSetFactory.make();
    cases.add(info);
    // run path through all of the instructions in the loop head sequence,
    // storing any case splits in splitPaths
    // do NOT add any paths to the path manager; add them to caseSplits instead.
    final CGNode startNode = info.getCurrentNode();
    final IR ir = startNode.getIR();
    final SSACFG cfg = ir.getControlFlowGraph();
    SSACFG.BasicBlock currentBlock = info.getCurrentBlock();
    int startLine = info.getCurrentLineNum();
    if (Options.DEBUG) Util.Debug("executing loop head sequence");
    Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);

    // map from phi index to paths corresponding to that phi index
    Map<Integer, List<IPathInfo>> phiIndexMap = null;
    for (;;) {
      List<SSAInstruction> instrs = currentBlock.getAllInstructions();
      for (int i = instrs.size() - 1; i > -1; i--) {
        SSAInstruction instr = instrs.get(i);
        if (Options.DEBUG) Util.Debug("loop head instr " + instr);
        if (i <= startLine) {
          if (instr instanceof SSAInvokeInstruction) {
            if (Options.DEBUG) Util.Assert(splitPaths.isEmpty(), "shouldn't have split yet!");
            Set<IPathInfo> extraPaths = HashSetFactory.make();
            for (IPathInfo path : cases) {
              path.setCurrentLineNum(i - 1);
              if (Options.SYNTHESIS) visitInvokeAsCallee((SSAInvokeInstruction) instr, path);
              else extraPaths.addAll(visitCallInLoopHead((SSAInvokeInstruction) instr, path));
            }
            if (!Options.SYNTHESIS) cases = extraPaths;
            //cases.clear();
            //cases.addAll(extraPaths);
            
            if (Options.DEBUG) {
              for (IPathInfo path : cases) {
                Util.Assert(path.isFeasible());
                Util.Assert(path.getCurrentNode().equals(startNode), 
                    "path " + path.getPathId() + " in node " + path.getCurrentNode() + " instead of " + startNode);
              }
            }
            
          } else if (instr instanceof SSAPhiInstruction) {
            // found a phi node; need to do path splitting early in order to
            // decide which value is assigned on which path
            if (phiIndexMap == null) {
              phiIndexMap = HashMapFactory.make();
              for (IPathInfo path : cases) {
                path.setCurrentLineNum(i - 1);
                splitPaths.clear();
                if (justGetToLoopHead) Util.Assert(preds.size() < 2, " bad IR " + ir);
                initializeSplitPaths(splitPaths, preds, path);
                int phiIndex = instr.getNumberOfUses() - 1;
                for (IPathInfo choice : splitPaths) {
                  List<IPathInfo> choices = new LinkedList<IPathInfo>();
                  choices.add(choice);
                  phiIndexMap.put(phiIndex, choices);
                  phiIndex--;
                }
              }
            }
            List<IPathInfo> toAdd = new LinkedList<IPathInfo>();
            List<IPathInfo> toRemove = new LinkedList<IPathInfo>();
            for (int key : phiIndexMap.keySet()) {
              List<IPathInfo> values = phiIndexMap.get(key);
              for (IPathInfo choice : values) {
                List<IPathInfo> phiCases = visitPhi((SSAPhiInstruction) instr, choice, key);
                if (phiCases == IPathInfo.INFEASIBLE) {
                  toRemove.add(choice); // phi visit made path infeasible
                } else if (!phiCases.isEmpty()) {
                  toAdd.addAll(phiCases);
                }
              }
              values.addAll(toAdd);
              values.removeAll(toRemove);
              toAdd.clear();
              toRemove.clear();
            }
          } else {
            // "normal" case
            if (Options.DEBUG)
              Util.Assert(!(instr instanceof SSAConditionalBranchInstruction), "should never be executing conditionals here!");
            if (Options.DEBUG)
              Util.Assert(splitPaths.isEmpty(), "shouldn't have split yet!");
            List<IPathInfo> toAdd = new LinkedList<IPathInfo>();
            List<IPathInfo> toRemove = new LinkedList<IPathInfo>();
            for (IPathInfo path : cases) {
              path.setCurrentLineNum(i - 1);
              List<IPathInfo> splits = path.visit(instr);
              if (splits == IPathInfo.INFEASIBLE)
                toRemove.add(path); // infeasible
              else
                toAdd.addAll(splits);
            }
            cases.addAll(toAdd);
            cases.removeAll(toRemove);
          }
        }
      }
      // keep executing straightline code
      if (preds.size() == 1) {
        currentBlock = (SSACFG.BasicBlock) preds.iterator().next();
        if (Options.DEBUG) Util.Assert(!cases.isEmpty(), "no paths left to execute!");
        if (Options.DEBUG) Util.Assert(phiIndexMap == null, 
             "phiIndex map should not be initialized!");
        // if we've made it to the loop head and that's our only goal, we're done.
        boolean returnNow = justGetToLoopHead && WALACFGUtil.isLoopHead(currentBlock, ir);
        
        for (IPathInfo choice : cases) {
          choice.setCurrentBlock(currentBlock);
          choice.setCurrentLineNum(currentBlock.getAllInstructions().size() - 1);
          if (returnNow) splitPaths.add(choice);
        }
        if (returnNow) return !splitPaths.isEmpty();
        
        startLine = currentBlock.getAllInstructions().size() - 1;
        preds = cfg.getNormalPredecessors(currentBlock);
      } else {
        if (Options.DEBUG)
          Util.Assert(preds.size() > 1, "loop should split at some point!");
        // Util.Assert(initSplitPaths, "split paths not initialized!");
        splitPaths.clear();
        if (phiIndexMap == null) { // phiIndexMap was never initialized. need to
                                   // split into a case for each pred
          if (Options.DEBUG) Util.Assert(splitPaths.isEmpty(), 
              "split paths should be empty here!");
          if (cases.isEmpty()) {
            Util.Debug("cases empty");
            info.refute();
            return false;
          }

          if (!justGetToLoopHead) {
            for (IPathInfo _case : cases) {
              initializeSplitPaths(splitPaths, preds, _case);
            }
          } else {
            splitPaths.addAll(cases);
            if (Options.DEBUG) {
              for (IPathInfo splitPath : splitPaths) {
                Util.Assert(WALACFGUtil.isLoopHead(splitPath.getCurrentBlock(), splitPath.getCurrentNode().getIR()),
                    splitPath + " not at loop head " + splitPath.getCurrentBlock() + " " + splitPath.getCurrentNode().getIR());
              }
            }
          }
          return true;
        } // else, phiIndexMap was already initialized
        Collection<List<IPathInfo>> lists = phiIndexMap.values();
        for (List<IPathInfo> list : lists) {
          splitPaths.addAll(list);
        }
        
        if (Options.DEBUG && justGetToLoopHead) {
          for (IPathInfo splitPath : splitPaths) {
            Util.Assert(WALACFGUtil.isLoopHead(splitPath.getCurrentBlock(), splitPath.getCurrentNode().getIR()),
                splitPath + " not at loop head " + splitPath.getCurrentBlock() + " " + splitPath.getCurrentNode().getIR());
          }
        }
        
        return !splitPaths.isEmpty();
      }
    }
  }

  // special case of instruction visiting for phi nodes
  List<IPathInfo> visitPhi(SSAPhiInstruction instr, IPathInfo info, int phiIndex) {
    if (Options.DEBUG)
      Util.Pre(phiIndex >= 0, "phi index should be non-negative!");
    if (Options.DEBUG)
      Util.Assert(instr.getNumberOfDefs() == 1, "only expecting one def in phi; found " + instr);
    if (Options.DEBUG)
      Util.Assert(phiIndex < instr.getNumberOfUses(),
          "index " + phiIndex + " out of bounds for # of uses " + instr.getNumberOfUses());
    if (Options.DEBUG)
      Util.Debug(instr.toString());
    return info.visitPhi(instr, phiIndex);
  }
  
  Set<IPathInfo> visitCallInLoopHead(SSAInvokeInstruction instr, IPathInfo path) {
    Util.Unimp("don't call this");
    return null;
  }
  

  public void addLoopMergePlaceholder(SSACFG.BasicBlock loopHeadToMerge) {
    IPathInfo mergeIndicator = IPathInfo.makeMergeIndicator(loopHeadToMerge);
    // Util.Assert(!pathsToExplore.contains(mergeIndicator),
    // "already have loop merge indicator for " + loopHeadToMerge);
    if (!pathsToExplore.contains(mergeIndicator)) {
      if (Options.DEBUG) {
        Util.Debug("adding loop merge indicator for block " + loopHeadToMerge);
      }
      this.pathsToExplore.push(mergeIndicator);
    }
  }
}

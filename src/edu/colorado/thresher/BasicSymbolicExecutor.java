package edu.colorado.thresher;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;

/**
 * a very simple symbolic executor. interprocedurally explores all program paths
 * in DFS fashion. conditional branch instructions are treated as
 * nondeterministic choices loops are unrolled once, though all (non-looping)
 * paths through the loop body are explored
 * 
 * @author sam
 */
public class BasicSymbolicExecutor implements ISymbolicExecutor {
  // call graph for the program to be executed
  protected final CallGraph callGraph;
  // paths to be executed
  protected final LinkedList<IPathInfo> pathsToExplore;

  // optimization: map from CGNode -> paths seen in order to avoid redundant
  // exploration
  protected final Map<CGNode, Set<IPathInfo>> seenPaths;
  protected final Logger logger;

  public BasicSymbolicExecutor(CallGraph callGraph, Logger logger) {
    this.callGraph = callGraph;
    this.logger = logger;
    this.pathsToExplore = new LinkedList<IPathInfo>();
    this.seenPaths = HashMapFactory.make();//new HashMap<CGNode, Set<IPathInfo>>();
  }

  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   * @return false if query is refuted on all paths, true otherwise
   */
  @Override
  public boolean executeBackward(CGNode startNode, IQuery query) {
    final SSACFG.BasicBlock exit = startNode.getIR().getControlFlowGraph().exit();
    return executeBackward(startNode, exit, exit.getAllInstructions().size() - 1, query);
  }

  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   * @return false if query is refuted on all paths, true otherwise
   */
  @Override
  public boolean executeBackward(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query) {
    // Util.Print(startNode.getIR().toString());
    final IPathInfo path = makePath(startNode, startBlk, startLine, query);
    this.pathsToExplore.add(path);
    // Util.visualizeIR(Options.DEBUG_cha, startNode.getIR(), "TEST"); // DEBUG
    // only; can get a view of weird IR if it's giving us trouble
    return executeBackward();
  }

  /**
   * main execution loop - keep exploring until no paths are left
   * 
   * @return false if query is refuted on all paths, true otherwise
   */
  @Override
  public boolean executeBackward() {
    int pathCount = 0;
    for (;;) {
      // also timeout if we use too much memory
      boolean oom = false;
      if (Runtime.getRuntime().freeMemory() / Runtime.getRuntime().totalMemory() >= 0.95)
        oom = true;

      if (++pathCount > Options.PATH_EXPLORE_LIMIT || oom) {
        logger.logTimeout();
        Util.Print("TIMEOUT");
        Util.Print("oom? " + oom);
        Util.Print("Had " + pathsToExplore.size() + " paths left to explore");
        logger.logPathCount(pathCount);
        return true;
      }
      final IPathInfo path = selectPath();
      if (path == null) {
        end();
        logger.logPathCount(pathCount);
        return false; // have executed all paths without finding a witness
      }
      // if (path.isDummy() || path.isLoopMergeIndicator()) continue;
      Util.Assert(!path.isLoopMergeIndicator(), "shouldn't get a loop merge indicator here!");
      Util.Assert(!path.isDummy(), "shouldn't get a dummy path here!");
      // if (path.getPathId() != lastPath) { // prevent printing except when we
      // pick a new path (logging parsimony issue, not correctness issue)
      if (Options.DEBUG)
        Util.Debug("executing path " + path.getPathId() + "X");
      if (Options.DEBUG)
        Util.Debug(path.toString());
      // } else Util.Debug("executing path " + path.getPathId() + "X");
      boolean hitProcBoundary = executeBackwardsPathIntraprocedural(path);
      if (path.foundWitness()) {
        logger.logPathCount(pathCount);
        logger.logWitnessList(path.getWitnessList());
        return true;
      }
      // if (!path.isFeasible()) continue; // refuted. this case shouldn't be
      // needed; executeBWPath should never return true for an infeasible path.
      if (hitProcBoundary) {
        // path hit procedure boundary, perform interprocedural execution
        if (handleInterproceduralExecution(path)) {
          logger.logPathCount(pathCount);
          logger.logWitnessList(path.getWitnessList());
          return true;
        }
      } // else, path is infeasible, either because it split or because it was
        // refuted. execute next path
    }
  }

  void end() {
  } // do nothing

  /**
   * symbolic execution in fakeWorldClinit (WALA's model of the Java class
   * initializers) requires special handling. we do not attempt to model the
   * order that static initializers are invoked in, so we just (soundly) punt
   * here... fancier symbolic executors can override and do better
   */
  boolean handleFakeWorldClinit(IPathInfo path) {
    path.declareFakeWitness(); // concede a witness
    return true;
  }

  // punt!
  boolean handleFakeRootMethod(IPathInfo path, CGNode entrypoint) {
    return true;
  }

  /**
   * perform summary check to avoid redundant exploration
   * 
   * @param path
   * @return true if some summary makes this path redundant, false otherwise
   */
  boolean isPathInSummary(IPathInfo path) {
    Set<IPathInfo> seen = seenPaths.get(path.getCurrentNode());
    if (seen == null) {
      // create seen and add this path to it
      // seen = new TreeSet<IPathInfo>();
      seen = HashSetFactory.make();//new HashSet<IPathInfo>();
      seenPaths.put(path.getCurrentNode(), seen);
      seen.add(path);
    } else {
      if (Options.SUBSUMPTION_CHECK_AT_SUMMARIES) {
        List<IPathInfo> toRemove = new LinkedList<IPathInfo>();
        for (IPathInfo seenPath : seen) {
          if (path.containsQuery(seenPath)) { // have we seen a simpler path?
            if (Options.DEBUG)
              Util.Debug("refuted by function summary;\n" + seenPath + "\nsimpler than\n" + path);
            path.refute();
            return true;
          } else if (seenPath.containsQuery(path)) { // no; is this one simpler?
            if (Options.DEBUG)
              Util.Debug("this path simpler than one we've seen; swapping");
            toRemove.add(seenPath);
          }
        }
        seen.removeAll(toRemove);
        seen.add(path);
      } else { // just do regular check
        // check if we've seen this path already
        if (!seen.add(path)) {
          if (Options.DEBUG)
            Util.Debug("refuted by function summary");
          path.refute();
          return true;
        } // else, haven't seen it; continue execution as normal
      }
    }
    return false;
  }

  /**
   * exposed to allow the inclusion of heuristics for not exploring certain
   * callers. this implementation uses no heuristics and simply returns all
   * callers
   */
  
  @Override
  public Iterator<CGNode> getCallers(IPathInfo path, Graph<CGNode> graph) {
    /* TODO: determinize
    List<CGNode> callers = new LinkedList<CGNode>();
    
    Iterator<CGNode> preds = graph.getPredNodes(path.getCurrentNode());
    while (preds.hasNext()) {
      callers.add(preds.next());
    }
      
    if (callers.size() > 1) {
      Collections.sort(callers, new Comparator<CGNode>() {
        public int compare(CGNode node1, CGNode node2) {
          // TODO: are graph node Id's consistent across different runs?
          return node1.getGraphNodeId() - node2.getGraphNodeId();
        }
      });
    }
    */
    
    return graph.getPredNodes(path.getCurrentNode());
  }

  /**
   * find possible callers for current path and add a new path for each
   * 
   * @param info
   *          - path that has reached a procedure boundary
   * @return - true if we have found a witness, false otherwise
   */
  @Override
  public boolean handleInterproceduralExecution(IPathInfo path) {
    if (!path.isCallStackEmpty()) {
      // leaving callee and returning to called method
      if (path.returnFromCall())
        addPath(path); // add path if it is feasible
      return false;
    } // else, call stack is empty; we are branching backwards into caller
    if (Options.DEBUG) Util.Debug("at function boundary for path " + path.getCurrentNode());

    if (isPathInSummary(path)) return false; // summary makes path redundant

    CGNode callee = path.getCurrentNode();

    // if this is an entrypoint and the only call is FakeRootNode
    if (this.callGraph.getEntrypointNodes().contains(callee) && this.callGraph.getPredNodeCount(callee) == 1) {
      if (Options.DEBUG) Util.Debug("reached entrypoint!");
      // Util.Print(callers.next().getIR().toString());
      CGNode entrypoint = path.getCurrentNode();

      IPathInfo easyWitness = path.deepCopy();
      easyWitness.setCurrentNode(WALACFGUtil.getFakeWorldClinitNode(callGraph));
      // first, try getting easy witness by going straight from entrypoint to
      // fakeWorldClinit
      if (Options.DEBUG) Util.Debug("trying to get easy witness in fakeWorldClinit");
      if (handleFakeWorldClinit(easyWitness)) {
        if (Options.DEBUG) Util.Debug("got easy witness in fakeWorldClinit");
        easyWitness.declareFakeWitness();
        return true;
      }
      // didn't work; try the other entrypoints

      path.setCurrentNode(this.callGraph.getFakeRootNode());
      if (handleFakeRootMethod(path, entrypoint)) {// iif
                                                   // (handleFakeWorldClinit(path))
                                                   // {
        path.declareFakeWitness(); // TODO: this is not a fake witness. the
                                   // problem is that newPath can split into
                                   // multiple paths and we can find a witness
                                   // on a different one
        return true; // found witness in fakeWorldClinit; done
      }
      return false; // refuted
    }

    if (path.getCurrentNode().getMethod().isClinit()) {
      path.setCurrentNode(WALACFGUtil.getFakeWorldClinitNode(callGraph));
      // current node is a class initializer... our only caller can be
      // fakeWorldClinit. handling this is a special case
      if (handleFakeWorldClinit(path)) {
        // this is not a fake witness. the problem is that newPath can split
        // into multiple paths and we can find a witness on a different one
        path.declareFakeWitness();
        return true; // found witness in fakeWorldClinit; done
      }
      return false;
    }

    Iterator<CGNode> callers = getCallers(path, this.callGraph);// new
                                                                // LinkedList<CGNode>();
    if (!callers.hasNext()) {
      Util.Debug("no callers found! refuted.");
      return false;
    }
    // Util.Assert(callers.hasNext(), "no callers found!");

    int callCount = 1;
    // for (CGNode caller : callerList) {
    while (callers.hasNext()) {
      CGNode caller = callers.next();
      if (Options.DEBUG)
        Util.Debug("trying caller " + caller + " " + (callCount++));// + " of "
                                                                    // +
                                                                    // callerList.size()
                                                                    // + ";\n" +
                                                                    // path);

      IR callerIR = caller.getIR();
      SSACFG callerCFG = callerIR.getControlFlowGraph();
      SSAInstruction[] instrs = callerIR.getInstructions();
      Iterator<CallSiteReference> sites = callGraph.getPossibleSites(caller, callee);
      while (sites.hasNext()) { // for each each caller
        CallSiteReference possibleCaller = sites.next();
        // caller may call callee multiple times. consider each call site
        IntSet indices = callerIR.getCallInstructionIndices(possibleCaller);
        IntIterator indexIter = indices.intIterator();
        Util.Assert(indexIter.hasNext(), "no call sites found in method " + possibleCaller);
        Util.Debug(indices.size() + " possible call instrs in this caller.");
        while (indexIter.hasNext()) { // for each (caller, callee) pair
          int callIndex = indexIter.next();
          SSAInstruction instr = instrs[callIndex];
          if (Options.DEBUG)
            Util.Debug("Trying call instr " + instr);
          Util.Assert(instr instanceof SSAInvokeInstruction, "Expecting a call instruction, found " + instr);

          SSACFG.BasicBlock callBlk = callerCFG.getBlockForInstruction(callIndex);
          int callLine = callBlk.getAllInstructions().size() - 1;
          Util.Assert(callBlk.getAllInstructions().get(callLine).equals(instr), "calls " + instr + " and "
              + callBlk.getAllInstructions().get(callLine).equals(instr) + " don't match");
          IPathInfo newPath = path.deepCopy();
          if (caller.equals(callee)) { // is this a recursive call?
            if (Options.DEBUG)
              Util.Debug("skipping recursive call " + callee.getMethod().toString() + " and dropping produced constraints");
            // this is both a recursive call and relevant. overapproximate its
            // effects by dropping constraints
            // that it could possibly produce
            newPath.skipCall((SSAInvokeInstruction) instr, this.callGraph, caller);
            // query.dropConstraintsProduceableInCall(instr,
            // this.getCurrentNode(), callee);
            if (newPath.foundWitness())
              return true; // if dropping constraints led to fake witness, we're
                           // done
            addPath(newPath); // add path and try next caller
            continue;
          }

          newPath.setCurrentNode(caller);
          if (WALACFGUtil.isFakeWorldClinit(caller, this.callGraph)) {
            if (handleFakeWorldClinit(newPath)) {
              // this is not a fake witness. the problem is that newPath can
              // split into multiple paths and we can find a witness on a
              // different one
              newPath.declareFakeWitness();
              return true; // found witness in fakeWorldClinit; done
            }
            continue; // else, path refuted; try another
          }
          newPath.setCurrentBlock(callBlk);

          if (visitInvokeAsCaller((SSAInvokeInstruction) instr, callee, newPath)) { // execute
                                                                                    // call
                                                                                    // instruction
            if (Options.DEBUG)
              Util.Debug("done visiting caller\n" + newPath);
            if (newPath.foundWitness())
              return true; // check for witness
            /*
             * if (WALACFGUtil.isFakeWorldClinit(caller, this.callGraph)) { if
             * (handleFakeWorldClinit(newPath)) { // this is not a fake witness.
             * the problem is that newPath can split into multiple paths and we
             * can find a witness on a different one
             * newPath.declareFakeWitness(); return true; // found witness in
             * fakeWorldClinit; done } continue; // else, path refuted; try
             * another }
             */

            /*
             * // skip to callers of caller if this call can't change the query
             * if (!path.isCallRelevantToQuery((SSAInvokeInstruction) instr,
             * callee, this.callGraph)) { Util.Debug("caller " + caller +
             * " not relevant; skipping to beginning of method");
             * newPath.setCurrentNode(caller);
             * newPath.setCurrentBlock(caller.getIR
             * ().getControlFlowGraph().entry()); newPath.setCurrentLineNum(-1);
             * addPath(newPath); continue; } // else, caller is potentially
             * important
             */

            newPath.setCurrentLineNum(callLine - 1); // start from line before
                                                     // the call
            addPath(newPath); // path is feasible, add to paths to explore
          } else if (Options.DEBUG)
            Util.Debug("visiting caller yielded infeasible path; refuting");// else
                                                                            // path
                                                                            // infeasible,
                                                                            // don't
                                                                            // copy
                                                                            // or
                                                                            // add
        }
      }
    }
    return false;
  }

  List<IPathInfo> propagateBackwardToCallers(IPathInfo path) {
    Util.Pre(path.isCallStackEmpty());
    List<IPathInfo> callerCaseSplits = new LinkedList<IPathInfo>();
    CGNode callee = path.getCurrentNode();
    Iterator<CGNode> callers = this.callGraph.getPredNodes(path.getCurrentNode());

    // if this is an entrypoint and the only call is FakeRootNode
    if (this.callGraph.getEntrypointNodes().contains(callee) && this.callGraph.getPredNodeCount(callee) == 1) {
      Util.Assert(false, "callee " + callee + " is entrypoint!");
    }

    if (path.getCurrentNode().getMethod().isClinit()) {
      path.setCurrentNode(WALACFGUtil.getFakeWorldClinitNode(callGraph));
      // current node is a class initializer... our only caller can be
      // fakeWorldClinit. handling this is a special case
      if (handleFakeWorldClinit(path)) {
        // this is not a fake witness. the problem is that newPath can split
        // into multiple paths and we can find a witness on a different one
        path.declareFakeWitness();
        return null; // found witness in fakeWorldClinit; done
      }
      return callerCaseSplits; // refuted
    }

    List<CGNode> callerList = new LinkedList<CGNode>();
    while (callers.hasNext()) {
      CGNode caller = callers.next();
      if (Options.DEBUG)
        Util.Debug("CALLER " + caller);
      callerList.add(caller);
    }

    int callCount = 1;
    for (CGNode caller : callerList) { // for each potential caller
      if (Options.DEBUG)
        Util.Debug("trying caller " + caller + " " + (callCount++) + " of " + callerList.size() + ";\n" + path);

      IR callerIR = caller.getIR();
      SSACFG callerCFG = callerIR.getControlFlowGraph();
      SSAInstruction[] instrs = callerIR.getInstructions();
      Iterator<CallSiteReference> sites = callGraph.getPossibleSites(caller, callee);
      while (sites.hasNext()) { // for each each caller
        CallSiteReference possibleCaller = sites.next();
        // caller may call callee multiple times. consider each call site
        IntSet indices = callerIR.getCallInstructionIndices(possibleCaller);
        IntIterator indexIter = indices.intIterator();
        Util.Assert(indexIter.hasNext(), "no call sites found in method " + possibleCaller);
        Util.Debug(indices.size() + " possible call instrs in this caller.");
        while (indexIter.hasNext()) { // for each (caller, callee) pair
          int callIndex = indexIter.next();
          SSAInstruction instr = instrs[callIndex];
          if (Options.DEBUG)
            Util.Debug("Trying call instr " + instr);
          Util.Assert(instr instanceof SSAInvokeInstruction, "Expecting a call instruction, found " + instr);

          SSACFG.BasicBlock callBlk = callerCFG.getBlockForInstruction(callIndex);
          int callLine = callBlk.getAllInstructions().size() - 1;
          Util.Assert(callBlk.getAllInstructions().get(callLine).equals(instr), "calls " + instr + " and "
              + callBlk.getAllInstructions().get(callLine).equals(instr) + " don't match");
          IPathInfo newPath = path.deepCopy();
          if (caller.equals(callee)) { // is this a recursive call?
            if (Options.DEBUG)
              Util.Debug("skipping recursive call " + callee.getMethod().toString() + " and dropping produced constraints");
            // this is both a recursive call and relevant. overapproximate its
            // effects by dropping constraints
            // that it could possibly produce
            newPath.skipCall((SSAInvokeInstruction) instr, this.callGraph, caller);
            // query.dropConstraintsProduceableInCall(instr,
            // this.getCurrentNode(), callee);
            if (newPath.foundWitness())
              return null; // if dropping constraints led to fake witness, we're
                           // done
            addPath(newPath); // add path and try next caller
            continue;
          }

          newPath.setCurrentNode(caller);

          // TODO: check on this. should this be allowed?
          if (WALACFGUtil.isFakeWorldClinit(caller, this.callGraph)) {
            Util.Assert(false, "shouldn't be clinit here!");
            /*
             * newPath.setCurrentNode(WALACFGUtil.getFakeWorldClinitNode(this.
             * callGraph)); if (handleFakeWorldClinit(newPath)) {
             * newPath.declareFakeWitness(); // TODO: this is not a fake
             * witness. the problem is that newPath can split into multiple
             * paths and we can find a witness on a different one return null;
             * // found witness in fakeWorldClinit; done } continue; // else,
             * path refuted; try another
             */
          }
          newPath.setCurrentBlock(callBlk);

          if (visitInvokeAsCaller((SSAInvokeInstruction) instr, callee, newPath)) { // execute
                                                                                    // call
                                                                                    // instruction
            if (Options.DEBUG)
              Util.Debug("done visiting caller\n" + newPath);
            if (newPath.foundWitness())
              return null; // check for witness
            if (WALACFGUtil.isFakeWorldClinit(caller, this.callGraph)) {
              Util.Assert(false, "shouldn't be clinit here!");
              /*
               * if (handleFakeWorldClinit(newPath)) {
               * newPath.declareFakeWitness(); // TODO: this is not a fake
               * witness. the problem is that newPath can split into multiple
               * paths and we can find a witness on a different one return null;
               * // found witness in fakeWorldClinit; done } continue; // else,
               * path refuted; try another
               */
            }

            newPath.setCurrentLineNum(callLine - 1); // start from line before
                                                     // the call
            // addPath(newPath); // path is feasible, add to paths to explore
            callerCaseSplits.add(newPath);
          } else if (Options.DEBUG)
            Util.Debug("visiting caller yielded infeasible path; refuting");// else
                                                                            // path
                                                                            // infeasible,
                                                                            // don't
                                                                            // copy
                                                                            // or
                                                                            // add
        }
      }
    }
    return callerCaseSplits;
  }

  /**
   * remove and return a path from paths to explore. override to change
   * exploration strategy. default is DFS selectPath() should return null if and
   * only if there are no paths left to execute
   * 
   * @return next path to execute, or null if there are none left
   */
  @Override
  public IPathInfo selectPath() {
    if (!pathsToExplore.isEmpty())
      return pathsToExplore.removeFirst();
    return null;
  }

  /**
   * add a path to the paths to explore. override to change exploration
   * strategy. default is DFS override to change exploration strategy. default
   * is DFS
   */
  @Override
  public void addPath(IPathInfo path) {
    if (Options.CHECK_ASSERTS) {
      Util.Pre(path.isFeasible(), "Should not add infeasible paths to paths to explore! " + path + " is infeasible.");
      Util.Pre(!path.atBranchPoint(), "path should not be at branch point");
      for (IPathInfo contained : pathsToExplore) {
        Util.Assert(contained.getPathId() != path.getPathId(), "toExplore already contains " + path);
      }
    }
    // DEBUG for (IPathInfo info : pathsToExplore) Util.Assert(info.getPathId()
    // != path.getPathId(), "path list already contains path " + path);
    if (Options.DEBUG)
      Util.Debug("adding path " + path.getPathId() + "X " + path.getCurrentNode() + " " + path.getCurrentBlock() + " line "
          + path.getCurrentLineNum());
    int stackSize = pathsToExplore.size() + 1;
    if (Options.DEBUG)
      Util.Debug("have " + stackSize + " paths to explore.");
    logger.logPathStackSize(stackSize);

    // Thread.dumpStack();
    this.pathsToExplore.addFirst(path);
  }

  /**
   * execute given path until it splits or reaches beginning of procedure.
   * explore all paths, but don't keep track of which conditions lead to paths
   * being taken
   * 
   * @return true if procedure boundary is reached, false if path splits
   */
  @Override
  public boolean executeBackwardsPathIntraprocedural(IPathInfo path) {
    final IR ir = path.getCurrentNode().getIR();
    // Util.Print(path.getCurrentNode().getIR().toString());

    while (true) { // until path splits into multiple paths
      // if the current block has multiple predecessors, we must choose which
      // one this path came from now in order to handle phi instructions
      // correctly.
      SSACFG.BasicBlock currentBlock = path.getCurrentBlock();
      int startLine = path.getCurrentLineNum();
      List<SSAInstruction> instrs = currentBlock.getAllInstructions();
      Util.Assert(startLine < instrs.size(), "index " + startLine + " out of range for instr list of size " + instrs.size());
      for (int i = instrs.size() - 1; i > -1; i--) {
        SSAInstruction instr = instrs.get(i);
        if (i <= startLine) {
          path.setCurrentLineNum(i - 1);
          if (!visit(instr, path))
            return false; // path is infeasible or has split
          else if (path.foundWitness())
            return true; // found at witness after executing this instr - return
                         // now
        }
      }
      // have executed all instructions in currentBlock. proceed to predecessors
      Collection<ISSABasicBlock> preds = ir.getControlFlowGraph().getNormalPredecessors(currentBlock);
      if (preds.size() == 0)
        return true; // path has reached beginning of procedure
      else if (preds.size() == 1) {
        // optimization: for the single predecessor case, can execute next block
        // directly (without any deep copying)
        SSACFG.BasicBlock nextBlock = (SSACFG.BasicBlock) preds.iterator().next();
        path.setCurrentBlock(nextBlock);
        path.setCurrentLineNum(nextBlock.getAllInstructions().size() - 1);
      } else {
        if (Options.DEBUG)
          Util.Debug("Forking execution: " + preds.size() + " choices.");
        boolean loop = false;
        if (WALACFGUtil.isLoopHead(currentBlock, ir) && path.seenLoopHead(currentBlock))
          loop = true; // we've seen this loop head before

        // make copies of current path for each predecessor and add to list of
        // paths to explore
        for (ISSABasicBlock blk : preds) {
          SSACFG.BasicBlock nextBlock = (SSACFG.BasicBlock) blk;
          if (loop && !WALACFGUtil.isLoopEscapeBlock(nextBlock, currentBlock, ir))
            continue; // avoid infinite looping by skipping "loop taken" paths
          IPathInfo copy = path.deepCopy();
          copy.setCurrentBlock(nextBlock);
          copy.setCurrentLineNum(nextBlock.getAllInstructions().size() - 1);

          // check if we are branching into a loop
          SSACFG.BasicBlock loopHead = WALACFGUtil.getLoopHeadForBlock(nextBlock, ir);
          if (loopHead != null)
            addLoopMergePlaceholder(loopHead);

          // copy.findAndPushNextBranchInstruction();
          addPath(copy);
        }
        return false; // path has split
      }
    }
  }

  /**
   * visit instruction and add new paths from case splits if appropriate
   * 
   * @return - true if path is feasible after visiting instruction, false
   *         otherwise
   */
  @Override
  public final boolean visit(SSAInstruction instr, IPathInfo info) {
    if (Options.DEBUG)
      Util.Debug(instr.toString());
    if (instr instanceof SSAAbstractInvokeInstruction) {
      return visitInvokeAsCallee((SSAAbstractInvokeInstruction) instr, info);
    } else if (instr instanceof SSAConditionalBranchInstruction) {
      return visitConditional((SSAConditionalBranchInstruction) instr, info);
    } else {
      return visitIPathInfoWrapper(instr, info);
    }
  }

  /**
   * wrapper to handle slightly unorthodox return behavior of IPathInfo's
   * visit()
   */
  boolean visitIPathInfoWrapper(SSAInstruction instr, IPathInfo info) {
    List<IPathInfo> caseSplits = info.visit(instr);
    if (caseSplits == IPathInfo.INFEASIBLE)
      return false; // infeasible
    for (IPathInfo path : caseSplits)
      addPath(path);
    return true;
  }

  /**
   * wrapper to handle slightly unorthodox return behavior of IPathInfo's
   * returnFromCall
   */
  boolean visitCallerWrapper(SSAAbstractInvokeInstruction instr, CGNode callee, IPathInfo info) {
    Util.Assert(instr instanceof SSAInvokeInstruction, "expecting invoke here");
    List<IPathInfo> caseSplits = info.returnFromCall((SSAInvokeInstruction) instr, callee);
    if (caseSplits == null)
      return false; // infeasible
    for (IPathInfo path : caseSplits)
      addPath(path);
    return true;
  }

  /**
   * visit invoke instruction as caller (i.e., we have executed the call and are
   * now returning to the caller) note that the CGNode of info should be the
   * caller node, NOT the callee
   * 
   * @param callee
   *          - method we are returning from
   * @return - true if query is feasible after call, false otherwise
   */
  boolean visitInvokeAsCaller(SSAAbstractInvokeInstruction instr, CGNode callee, IPathInfo info) {
    Util.Assert(instr instanceof SSAInvokeInstruction, "not sure how to handle non-invokes!");
    if (Options.DEBUG)
      Util.Debug(instr.toString());
    return visitCallerWrapper((SSAInvokeInstruction) instr, callee, info);
  }

  /**
   * wrapper to handle slightly unorthodox return behavior of IPathInfo's
   * visit()
   */
  boolean visitCalleeWrapper(SSAAbstractInvokeInstruction instr, CGNode callee, IPathInfo info) {
    Util.Assert(instr instanceof SSAInvokeInstruction, "expecting invoke here");
    // if (callee.getIR() != null) Util.Print(callee.getIR().toString());
    List<IPathInfo> caseSplits = info.enterCall((SSAInvokeInstruction) instr, callGraph, callee);
    if (caseSplits == null)
      return false; // infeasible
    for (IPathInfo path : caseSplits)
      addPath(path);
    return true;
  }

  // DEBUG only
  boolean split = false;

  /**
   * visit invoke instruction as callee (i.e. we are entering the call)
   * 
   * @return - false if query is infeasible or path split, true otherwise
   */
  boolean visitInvokeAsCallee(SSAAbstractInvokeInstruction instr, IPathInfo info) {
    Set<CGNode> callees = callGraph.getPossibleTargets(info.getCurrentNode(), instr.getCallSite());
    // we get empty call sites when we don't have stubs for something
    // Util.Assert(!callees.isEmpty(), "Invoke instr " + instr +
    // " doesn't resolve to any call sites from caller " +
    // info.getCurrentNode());
    if (callees.isEmpty()) {
      Util.Debug("callees empty...skipping call");

      // TODO: hack! encode that size returns a value >= 0 and less than max
      // collection size
      if (instr.getCallSite().getDeclaredTarget().toString().contains("size()")) {
        return info.addSizeConstraint((SSAInvokeInstruction) instr, info.getCurrentNode());
      }

      return true;
    }
    if (callees.size() == 1) { // normal case
      CGNode callee = callees.iterator().next();
      if (WALACFGUtil.isFakeWorldClinit(instr.getDeclaredTarget(), this.callGraph)) { // special
                                                                                      // handling
                                                                                      // for
                                                                                      // fakeWorldClinit
        info.pushCallStack((SSAInvokeInstruction) instr, callee);
        if (handleFakeWorldClinit(info)) {
          info.declareFakeWitness(); // TODO: this isn't actually a fake
                                     // witness. the problem is that info can
                                     // split and we can find a witness on a
                                     // different path
          return true; // found witness in fakeWorldClinit
        }
        return false; // path refuted
      }
      if (!visitCalleeWrapper(instr, callee, info))
        return false; // refuted by parameter binding
      // else, ordinary call
      addPath(info);
      if (Options.CHECK_ASSERTS)
        split = true;
      return false; // don't want to continue executing instructions that occur
                    // before call in caller, so return false
    } else { // dynamic dispatch case
      Util.Debug("dynamic dispatch!");
      for (CGNode callee : callees) { // consider case for each potential callee
        // Util.Debug("skipping callee " + callee " due to dynamic dispatch");
        info.skipCall((SSAInvokeInstruction) instr, this.callGraph, callee); // hack:
                                                                             // don't
                                                                             // consider
                                                                             // dynamic
                                                                             // dispatch
        /*
         * IPathInfo copy = info.deepCopy(); if
         * (info.isCallRelevantToQuery(instr, callee, this.callGraph)) continue;
         * if (visitCalleeWrapper(instr, callee, copy)) { added = true;
         * addPath(copy); // don't want to continue executing instructions that
         * occur before call in caller, so return false } // else, refuted by
         * parameter binding } if (!added) return true; // no callees relevant;
         * continue executing on current path
         */
      }
      return true;
    }
  }

  /**
   * override to customize conditional visiting
   */
  boolean visitConditional(SSAConditionalBranchInstruction instr, IPathInfo info) {
    return true;
  }

  /**
   * override to use different kind of PathInfo during execution
   */
  @Override
  public IPathInfo makePath(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query) {
    return new IPathInfo(startNode, startBlk, startLine, query);
  }

  // forward execution... a feature for the future

  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   */
  @Override
  public void executeForward(CGNode startNode, IQuery query) {
    final SSACFG.BasicBlock entry = startNode.getIR().getControlFlowGraph().entry();
    executeForward(startNode, entry, 0, query);
  }

  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   */
  @Override
  public void executeForward(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query) {
    Util.Unimp("forward execution");
  }

  // should be overriden by fancier symbolic executors
  public void addLoopMergePlaceholder(SSACFG.BasicBlock loopHeadToMerge) {
  }

}

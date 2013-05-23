package edu.colorado.thresher;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import z3.java.Z3AST;
import z3.java.Z3Context;
import z3.java.Z3Model;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.impl.GraphInverter;
import com.ibm.wala.util.graph.traverse.BFSIterator;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;
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

  // optimization: map from CGNode -> paths seen in order to avoid redundant exploration
  protected final Map<CGNode, Set<IPathInfo>> seenPaths;
  protected final Logger logger;
  
  private Collection<String> synthesizedClasses;

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
  public final boolean executeBackward(CGNode startNode, IQuery query) {
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
  public final boolean executeBackward(CGNode startNode, SSACFG.BasicBlock startBlk, int startLine, IQuery query) {
    // Util.Print(startNode.getIR().toString());
    final IPathInfo path = makePath(startNode, startBlk, startLine, query);
    this.pathsToExplore.add(path);
    // Util.visualizeIR(Options.DEBUG_cha, startNode.getIR(), "TEST"); // DEBUG
    // only; can get a view of weird IR if it's giving us trouble
    boolean result = executeBackward();
    query.dispose(); // clear theorem prover contexts and other resources used by the query
    return result;
  }
  
  /**
   * @param startNode
   *          - CGNode from which to begin
   * @param query
   *          - fact that symbolic execution will witness or refute
   * @return false if query is refuted on all paths, true otherwise
   */
  @Override
  public final boolean executeBackward(IPathInfo path) {
    // Util.Print(startNode.getIR().toString());
    //final IPathInfo path = makePath(startNode, startBlk, startLine, query);
    final IQuery query = path.query;
    this.pathsToExplore.add(path);
    // Util.visualizeIR(Options.DEBUG_cha, startNode.getIR(), "TEST"); // DEBUG
    // only; can get a view of weird IR if it's giving us trouble
    boolean result = executeBackward();
    query.dispose(); // clear theorem prover contexts and other resources used by the query
    return result;
  }

  /**
   * main execution loop - keep exploring until no paths are left
   * 
   * @return false if query is refuted on all paths, true otherwise
   */
  @Override
  public final boolean executeBackward() {
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
        if (Options.LOG_WITNESSES) logger.logWitnessList(path.getWitnessList());
        return true;
      }
      // if (!path.isFeasible()) continue; // refuted. this case shouldn't be
      // needed; executeBWPath should never return true for an infeasible path.
      if (hitProcBoundary) {
        // path hit procedure boundary, perform interprocedural execution
        if (handleInterproceduralExecution(path)) {
          logger.logPathCount(pathCount);
          if (Options.LOG_WITNESSES) logger.logWitnessList(path.getWitnessList());
          this.witnessQuery = path.query;
          return true;
        }
      } // else, path is infeasible, either because it split or because it was
        // refuted. execute next path
    }
  }
  
  private IQuery witnessQuery;
  IQuery witnessQuery() { return witnessQuery; }
  

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
    if (path.getCallStackDepth() != 0) return false; // TODO: match call stack?
    if (!Options.USE_SUMMARIES) return false;
    Set<IPathInfo> seen = seenPaths.get(path.getCurrentNode());
    if (seen == null) {
      // create seen and add this path to it
      seen = HashSetFactory.make();
      seenPaths.put(path.getCurrentNode(), seen);
      seen.add(path);
    } else {
      return !IPathInfo.mergePathWithPathSet(path, seen);
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
    
    // TMP
    /*
    Graph<CGNode> reversed = GraphInverter.invert(this.callGraph);
    // assume single entrypoint node
    BFSPathFinder<CGNode> finder = new BFSPathFinder<CGNode>(reversed, path.getCurrentNode(), this.callGraph.getFakeRootNode());
    List<CGNode> cgPath = finder.find();
    Util.Debug("Path to root " + Util.printCollection(cgPath));
    Util.Debug(cgPath.size() + " nodes in shortest path.");
    
    int count = 0;
    BFSIterator<CGNode> iter = new BFSIterator<CGNode>(reversed, path.getCurrentNode());
    while (iter.hasNext()) {
      CGNode next = iter.next();
      Util.Debug("node is " + next);
      count++;
    }
    Util.Debug(count + " nodes in UP set.");
    
    Map<Constraint,Set<CGNode>> constraintModMap = path.query.getRelevantNodes();//path.getModifiersForQuery();
    // get potential producers for constraints
    Set<CGNode> producers = Util.flatten(constraintModMap.values());
    if (Options.DEBUG) {
      Util.Debug("MAP: ");
      for (Constraint constraint : constraintModMap.keySet()) {
        Util.Debug(constraint + " ===>\n" + Util.printCollection(constraintModMap.get(constraint)));
      }
      
      for (CGNode producer : producers) {
        Util.Debug("producer: " + producer);
      }

    }
    */
    // END TMP
    

    CGNode callee = path.getCurrentNode();

    if (Options.DEBUG) Util.Debug(this.callGraph.getPredNodeCount(callee) + " callers.");
    
    // if this is an entrypoint and the only call is FakeRootNode
    if (this.callGraph.getEntrypointNodes().contains(callee) && this.callGraph.getPredNodeCount(callee) == 1) {
      if (Options.DEBUG) Util.Debug("reached entrypoint!");
      
      if (Options.SYNTHESIS) {
        CombinedPathAndPointsToQuery qry = (CombinedPathAndPointsToQuery) path.query;
        if (qry.constraints.isEmpty()) {
          // don't need any external constraints for witness; "definite" (up to imprecision) assertion failure
          // TODO: printsome sort of witness
          return true;
        }
        
        Util.Print("Beginning synthesis");
        Z3Context ctx = qry.ctx;
        // map from free variables in our representation to free variables in the theorem prover
        Map<SimplePathTerm,Z3AST> termVarMap = HashMapFactory.make();
        
        // prune irrelevant constraints
        // TODO: handle this in a more principled way
        for (AtomicPathConstraint constraint : qry.constraints) {
          if (!constraint.getLhs().isIntegerConstant() && 
              !constraint.getRhs().isIntegerConstant()) {
            // nothing for the SMT solver to generate a model for;
            // likely a constraint on heap locations. drop it.
          }
        }
        
        Util.Print("Constraints:");
        for (AtomicPathConstraint constraint : qry.constraints) {
          Util.Print(constraint);
          for (SimplePathTerm term : constraint.getTerms()) {
            if (!term.isIntegerConstant()) termVarMap.put(term, term.toZ3AST(ctx, false));
          }
          // give constraints to the prover
          Z3AST ast = constraint.toZ3AST(ctx);
          ctx.assertCnstr(ast);
        }

        Z3Model model = qry.ctx.mkModel();
        // get assignments for the free environment variables from the theorem prover
        if (qry.ctx.checkAndGetModel(model)) { // sat
          // map from free variables -> the value they should be assigned according to the prover
          Map<SimplePathTerm,String> termValMap = HashMapFactory.make();
          for (SimplePathTerm term : termVarMap.keySet()) {
            termValMap.put(term, "" + model.evalAsInt(termVarMap.get(term))); // convert to string 
          }
          
          IClassHierarchy cha = qry.depRuleGenerator.getClassHierarchy();
          ClassSynthesizer synth = new ClassSynthesizer(cha);

          // call synthesizer with method signatures and values to assign
          this.synthesizedClasses = synth.synthesize(termValMap);
        } else Util.Unimp("Constraint system unsat! Can't synthesize"); // unsat

        return true;
      }
      
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
      if (Options.DEBUG) Util.Debug("trying caller " + caller + " " + (callCount++));
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
        while (indexIter.hasNext()) { 
          int callIndex = indexIter.next();
          SSAInstruction instr = instrs[callIndex];
          if (Options.DEBUG) Util.Debug("Trying call instr " + instr);
          Util.Assert(instr instanceof SSAInvokeInstruction, "Expecting a call instruction, found " + instr);

          SSACFG.BasicBlock callBlk = callerCFG.getBlockForInstruction(callIndex);
          int callLine = callBlk.getAllInstructions().size() - 1;
          Util.Assert(callBlk.getAllInstructions().get(callLine).equals(instr), "calls " + instr + " and "
              + callBlk.getAllInstructions().get(callLine).equals(instr) + " don't match");
          IPathInfo newPath = path.deepCopy();
          if (caller.equals(callee)) { // is this a recursive call?
            if (Options.DEBUG)
              Util.Debug("skipping recursive call " + callee.getMethod().toString() + " and remvoing produced constraints, if any.");
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
            if (newPath.foundWitness()) return true; // check for witness
  
            newPath.setCurrentLineNum(callLine - 1); // start from line before
                                                     // the call
            addPath(newPath); // path is feasible, add to paths to explore
          } else if (Options.DEBUG)
            // else, path infeasible; don't copy or add
            Util.Debug("visiting caller yielded infeasible path; refuting");
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
            // else, path infeasible; don't copy or add
            Util.Debug("visiting caller yielded infeasible path; refuting");
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
      if (!path.isFeasible()) return; // HACK!
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
    if (Options.DEBUG) {
      Util.Debug("have " + stackSize + " paths to explore.");
    }
    logger.logPathStackSize(stackSize);

    this.pathsToExplore.addFirst(path);
    /*
    if (Options.DEBUG) {
      for (IPathInfo thePath : this.pathsToExplore) {
        Util.Debug(thePath.getPathId() + " " + thePath.getCurrentBlock());
      }
    }
    */
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
    } else if (instr instanceof SSASwitchInstruction) {
      return visitSwitch((SSASwitchInstruction) instr, info);
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
    if (caseSplits == null) return false; // infeasible
    for (IPathInfo path : caseSplits) {
      addPath(path);
    }
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
    if (callees.isEmpty()) {
      if (Options.SYNTHESIS) {
        // replace with <base obj>.<call>
        info.visit(instr);
      } else {
        Util.Debug("callees empty...skipping call");
        info.skipCall((SSAInvokeInstruction) instr, callGraph, null); 
      }
      return true;
    }
    if (callees.size() == 1) { // normal case
      CGNode callee = callees.iterator().next();
      if (WALACFGUtil.isFakeWorldClinit(instr.getDeclaredTarget(), this.callGraph)) { 
        info.pushCallStack((SSAInvokeInstruction) instr, callee);
        if (handleFakeWorldClinit(info)) {
          // TODO: this isn't actually a fake witness. the problem is that info can
          // split and we can find a witness on a different path
          info.declareFakeWitness(); 
          return true; // found witness in fakeWorldClinit
        }
        return false; // path refuted
      }
      if (!visitCalleeWrapper(instr, callee, info)) return false; // refuted by parameter binding
      // else, ordinary call
      addPath(info);
      if (Options.CHECK_ASSERTS) split = true;
      // don't want to continue executing instructions that occur before call in caller, so return false
      return false; 
    } else { // dynamic dispatch case
      Util.Debug("dynamic dispatch!");
      boolean allRefuted = true;
      SSAInvokeInstruction invoke = (SSAInvokeInstruction) instr;
      for (CGNode callee : callees) { // consider case for each potential callee
        // make sure callee is feasible w.r.t to constraints
        if (!info.isDispatchFeasible(invoke, info.getCurrentNode(), callee)) {
          if (!info.isFeasible()) return false; // can be refuted by dispatch on null
          continue;
        }
        
        if (Options.SKIP_DYNAMIC_DISPATCH) {
          // heuristic: skip any dynamic dispatch. exploration cost is not worth it
          info.skipCall((SSAInvokeInstruction) instr, this.callGraph, callee);
          if (info.foundWitness()) return true;
          allRefuted = false;
        } else {
          IPathInfo copy = info.deepCopy();
          if (visitCalleeWrapper(instr, callee, copy)) {
            if (copy.foundWitness()) {
              info.declareFakeWitness();
              return true;
            }
            addPath(copy);
            allRefuted = true;
            if (Options.CHECK_ASSERTS) split = true;
          } // else, refuted by parameter binding
        }
      }
      return !allRefuted;
    }
  }

  /**
   * override to customize conditional visiting
   */
  boolean visitConditional(SSAConditionalBranchInstruction instr, IPathInfo info) {
    return true;
  }
  
  /**
   * override to customize switch visiting
   */
  boolean visitSwitch(SSASwitchInstruction instr, IPathInfo info) {
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
  
  
  
  @Override
  public Collection<String> getSynthesizedClasses() {
    if (!Options.SYNTHESIS) return null;
    else return synthesizedClasses;
  }

}

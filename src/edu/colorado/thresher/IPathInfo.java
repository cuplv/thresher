package edu.colorado.thresher;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;

/**
 * abstraction of single (non-disjunctive) path during symbolic execution
 * contains program point information, a query, and utility methods for
 * interacting with symbolic executor and query
 * 
 * @author sam
 * 
 */
public class IPathInfo { // implements Comparable {

  // empty list means feasible to the visit() method
  public static final List<IPathInfo> FEASIBLE = Collections.unmodifiableList(new LinkedList<IPathInfo>());
  // null means infeasible to the visit() method
  public static final List<IPathInfo> INFEASIBLE = null;
  // path id for all dummy (non-executable) paths
  private static final int DUMMY_ID = -1;
  private static final int MERGE_ID = -2;
  private static int pathIdCounter = 1;

  // unique identifier
  private final int pathId;

  // program point information
  private CGNode currentNode;
  // the block we are currently in
  private SSACFG.BasicBlock currentBlock;
  // the block we previously came from
  private SSACFG.BasicBlock lastBlock;
  // index into into the current block corresponding to next instruction to
  // execute
  private int currentLineNum;

  private final LinkedList<IStackFrame> callStack;
  // set of loop heads that we have already seen and should not visit again
  private final Set<Pair<CGNode, SSACFG.BasicBlock>> loopHeadSet;
  // set of CGNode's that we've already explored during piecewise execution
  private final PiecewiseGraph piecewiseGraph;

  // fact we are trying to prove on this path; if false, path must be killed
  final IQuery query;

  // query we started with; if it reappears in our set, we can kill the path
  final IQuery initialQuery;

  // hack to allow us to give up early when it suits our purposes
  boolean fakeWitness = false;

  // flag to allow query to be refuted from the outside (i.e., by summaries)
  boolean externallyRefuted = false;

  boolean atBranchPoint = false;

  /**
   * create and return "dummy" IPathInfo (can be used as placeholder on branch
   * stack)
   */
  public static IPathInfo makeDummyPath() {
    return new IPathInfo();
  }

  public static IPathInfo makeMergeIndicator(SSACFG.BasicBlock toMerge) {
    return new IPathInfo(toMerge);
  }

  // empty constructor only to be used in creating dummy PathInfo's
  private IPathInfo(SSACFG.BasicBlock toMerge) {
    this.pathId = MERGE_ID;
    this.currentBlock = toMerge;
    this.callStack = null;
    this.currentNode = null;
    this.loopHeadSet = null;
    this.query = null;
    this.initialQuery = null;
    this.lastBlock = null;
    this.piecewiseGraph = null;
  }

  // empty constructor only to be used in creating dummy PathInfo's
  private IPathInfo() {
    this.pathId = DUMMY_ID;
    this.callStack = null;
    this.currentNode = null;
    this.loopHeadSet = null;
    this.query = null;
    this.initialQuery = null;
    this.lastBlock = null;
    this.piecewiseGraph = null;
  }

  // constructor for building PathInfo from scratch
  public IPathInfo(CGNode currentNode, SSACFG.BasicBlock currentBlock, int currentLineNum, IQuery query) {
    Util.Pre(currentBlock != null, "current block should not be null!");
    this.pathId = pathIdCounter++;
    this.currentNode = currentNode;
    this.currentBlock = currentBlock;
    this.lastBlock = null;
    this.currentLineNum = currentLineNum;
    this.callStack = new LinkedList<IStackFrame>();
    // this.branchStack = new LinkedList<Pair<IBranchPoint,Boolean>>();
    this.loopHeadSet = HashSetFactory.make();//new HashSet<Pair<CGNode, SSACFG.BasicBlock>>();
    this.query = query;
    this.initialQuery = query.deepCopy();
    this.piecewiseGraph = new PiecewiseGraph();
    Util.Assert(query instanceof CombinedPathAndPointsToQuery, "found bad query type " + query.getClass());
    addContextualConstraints(currentNode);
  }

  // constructor to be used only for deep copying
  private IPathInfo(CGNode currentNode, SSACFG.BasicBlock currentBlock, SSACFG.BasicBlock lastBlock, int currentLineNum,
      LinkedList<IStackFrame> callStack, Set<Pair<CGNode, SSACFG.BasicBlock>> loopHeadSet, IQuery query, IQuery initialQuery,
      PiecewiseGraph piecewiseGraph) {
    Util.Pre(currentBlock != null, "current block should not be null!");
    this.pathId = pathIdCounter++;
    this.currentNode = currentNode;
    this.currentBlock = currentBlock;
    this.lastBlock = lastBlock;
    this.currentLineNum = currentLineNum;
    this.callStack = callStack;
    // this.branchStack = branchStack;
    this.loopHeadSet = loopHeadSet;
    this.query = query;
    this.initialQuery = initialQuery;
    this.piecewiseGraph = piecewiseGraph;
    // TODO: TMP; debug only
    Util.Assert(query instanceof CombinedPathAndPointsToQuery, "found bad query type " + query.getClass());
  }

  public IPathInfo deepCopy() {
    Util.Pre(!atBranchPoint);
    return new IPathInfo(this.currentNode, this.currentBlock, this.lastBlock, this.currentLineNum,
        Util.deepCopyStackList(this.callStack), Util.deepCopySet(loopHeadSet), query.deepCopy(), this.initialQuery,
        this.piecewiseGraph.deepCopy());
  }

  /**
   * copy the current path, but replace the current query with a newQuery NOTE:
   * newQuery should be deep copied before it is passed
   */
  public IPathInfo deepCopyWithQuery(IQuery newQuery) {
    return new IPathInfo(this.currentNode, this.currentBlock, this.lastBlock, this.currentLineNum,
        Util.deepCopyStackList(this.callStack), Util.deepCopySet(loopHeadSet), newQuery, this.initialQuery, this.piecewiseGraph);
  }

  /**
   * wrapper for the query method
   * 
   * @return - true if the query is feasible after adding the constraint, false
   *         otherwise
   */
  public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranch) {
    return query.addConstraintFromBranchPoint(point, trueBranch);
  }

  public boolean simulateQueryReturnFromCall(SSAInvokeInstruction instruction, CGNode callee) {
    // Util.Debug("simulating return from callee " + callee + " via call instr "
    // + instruction);
    List<IQuery> caseSplits = this.query.returnFromCall(instruction, callee, this);
    return caseSplits == IQuery.INFEASIBLE ? false : true;
  }

  // TODO: hack!
  public boolean addSizeConstraint(SSAInvokeInstruction instr, CGNode caller) {
    if (query instanceof CombinedPathAndPointsToQuery) {
      CombinedPathAndPointsToQuery combined = (CombinedPathAndPointsToQuery) query;
      if (instr.hasDef()) {
        int MAX_COLLECTION_SIZE = 1073741824; // taken from HashMap
        PointerVariable returnValue = new ConcretePointerVariable(caller, instr.getDef(), combined.depRuleGenerator.getHeapModel());
        if (combined.pathVars.contains((returnValue))) {
          // bypass constraint limits for these
          combined.constraints.add(new AtomicPathConstraint(new SimplePathTerm(returnValue), new SimplePathTerm(0),
              ConditionalBranchInstruction.Operator.GE));
          combined.constraints.add(new AtomicPathConstraint(new SimplePathTerm(returnValue),
              new SimplePathTerm(MAX_COLLECTION_SIZE), ConditionalBranchInstruction.Operator.LT));
          return combined.isFeasible();
          // substituteExpForVar(new
          // SimplePathTerm(Util.makeReturnValuePointer(instr.getDeclaredTarget())),
          // returnValue);
          // substituteExpForVar(new
          // SimplePathTerm(Util.makeReturnValuePointer(callee,
          // this.depRuleGenerator.getHeapModel())), returnValue);
          // return isFeasible();
        }
      }
    }
    return true;
  }

  /**
   * pop the call stack and restore the state from the caller. this should only
   * be called when returning from a callee (i.e. the call stack is empty)
   * 
   * @return true if query is feasible after return from call, false otherwise
   */
  public boolean returnFromCall() {
    Util.Pre(!callStack.isEmpty(), "Can't pop an empty call stack!");
    IStackFrame frame = callStack.pop();
    CGNode callee = currentNode;
    if (Options.DEBUG)
      Util.Debug("returning from " + callee + " to " + frame.getCGNode());
    // MethodReference calleeMethod = callee.getMethod().getReference();

    // cleanup: forget which loop heads we saw in the callee, in case we come
    // back to the callee later
    List<Pair<CGNode, SSACFG.BasicBlock>> toRemove = new LinkedList<Pair<CGNode, SSACFG.BasicBlock>>();
    for (Pair<CGNode, SSACFG.BasicBlock> pair : loopHeadSet) {
      if (pair.fst.equals(callee))
        toRemove.add(pair);
    }
    /*
     * for (SSACFG.BasicBlock loopHead : loopHeadSet) { if
     * (loopHead.getMethod().getReference().equals(calleeMethod))
     * toRemove.add(loopHead); } for (SSACFG.BasicBlock removeMe : toRemove)
     * loopHeadSet.remove(removeMe);
     */
    for (Pair<CGNode, SSACFG.BasicBlock> pair : toRemove) {
      boolean removed = loopHeadSet.remove(pair);
      Util.Assert(removed, "couldn't remove " + pair);
    }

    // reset caller state
    this.currentNode = frame.getCGNode();
    this.currentBlock = frame.getBlock();
    this.currentLineNum = frame.getLineNum();
    // reflect return in query
    List<IQuery> caseSplits = this.query.returnFromCall(frame.getCallInstr(), callee, this);
    // we should never have case splits here because the arguments to the callee
    // were already known before we entered it
    Util.Post(caseSplits == IQuery.INFEASIBLE || caseSplits.isEmpty(), "Shouldn't have case splits after leaving callee!");
    return caseSplits == IQuery.INFEASIBLE ? false : true;
  }

  /**
   * special case; should be called ONLY when returning from a call and our call
   * stack is empty (i.e. branching backwards to a new method
   * 
   * @param callee
   *          - method we are returning from
   */
  public List<IPathInfo> returnFromCall(SSAInvokeInstruction instr, CGNode callee) {
    Util.Pre(this.callStack.isEmpty(), "Should only call this method with empty call stack!");
    // cleanup: forget which loop heads we have seen. otherwise, if we come back
    // to this method later, we will neglect to execute loops we've already seen
    loopHeadSet.clear();
    // have query reflect return from call
    List<IQuery> caseSplits = query.returnFromCall(instr, callee, this);
    return handleQueryCaseSplitReturn(caseSplits);
  }

  /**
   * push the current state onto the call stack and set the state to the callee
   * state
   * 
   * @param callInstr
   *          - the call instr in the caller that forced this call stack push
   * @param callee
   *          - CGNode for the callee method
   */
  void pushCallStack(SSAInvokeInstruction callInstr, CGNode callee) {
    Util.Pre(callee.getIR() != null, "no IR for " + callee);
    Util.Pre(callee.getIR().getExitBlock() != null, "no exit block!");
    // if
    // (this.currentNode.getMethod().toString().equals(callee.getMethod().toString()))
    // {
    if (this.currentNode.equals(callee)) {
      // Util.Print("Recursion detected; bailing out! method is " +
      // callee.getMethod().getName().toString());
      Util.Unimp("recursion");
    }

    // Util.Debug("pushing " + this.currentNode +
    // " onto call stack and entering " + callee);
    IStackFrame newFrame = new IStackFrame(callInstr, this.currentNode, this.currentBlock, this.currentLineNum);
    callStack.push(newFrame);
    this.currentNode = callee;
    // Util.Assert(addContextualConstraints(currentNode),
    // "refuted by contextual constraints!");
    this.currentBlock = callee.getIR().getExitBlock();
    this.currentLineNum = this.currentBlock.getLastInstructionIndex();
  }

  /**
   * mark a loop head as seen so we do not visit again
   * 
   * @return true if we have already seen the loop head, false otherwise
   */
  public boolean seenLoopHead(SSACFG.BasicBlock loopHead) {
    Pair<CGNode, SSACFG.BasicBlock> pair = Pair.make(this.currentNode, loopHead);
    return !loopHeadSet.add(pair);
    // return !loopHeadSet.add(loopHead);
  }

  /**
   * remove a loop head from the loops we have seen already... important for
   * nested loops
   * 
   * @param loopHead
   *          - a loop head we have just merged
   */
  public void removeSeenLoopHead(SSACFG.BasicBlock loopHead) {
    Pair<CGNode, SSACFG.BasicBlock> pair = Pair.make(this.currentNode, loopHead);
    // boolean removed = loopHeadSet.remove(loopHead);
    boolean removed = loopHeadSet.remove(pair);
    Util.Assert(removed, "couldn't remove loop head " + pair);
  }

  public int loopsSeen() {
    return loopHeadSet.size();
  }

  /**
   * change this path's query to be the intersection of the current query and
   * other's query
   * 
   * @param other
   *          - path whose query we will intersect
   */
  public void intersectQuery(IPathInfo other) {
    this.query.intersect(other.query);
  }

  List<IPathInfo> handleQueryCaseSplitReturn(List<IQuery> caseSplits) {
    if (caseSplits == IQuery.INFEASIBLE)
      return IPathInfo.INFEASIBLE;
    else if (caseSplits.equals(IQuery.FEASIBLE))
      return IPathInfo.FEASIBLE;
    else {
      List<IPathInfo> paths = new LinkedList<IPathInfo>();
      for (IQuery query : caseSplits) {
        if (query != initialQuery) {
          // if (!query.contains(initialQuery)) { // don't want to allow inital
          // query to be re-added; should be considered during separate
          // execution
          paths.add(this.deepCopyWithQuery(query));
        }
      }
      if (paths.isEmpty())
        return IPathInfo.INFEASIBLE;
      Util.Assert(!paths.isEmpty(), "should be nonempty here!");
      return paths;
    }
  }

  public List<IPathInfo> visit(SSAInstruction instr) {
    List<IQuery> caseSplits = query.visit(instr, this);
    return handleQueryCaseSplitReturn(caseSplits);
  }

  public List<IPathInfo> visitPhi(SSAPhiInstruction instr, int phiIndex) {
    List<IQuery> caseSplits = query.visitPhi(instr, phiIndex, this); // query.visitPhi(instr,
                                                                     // phiIndex,
                                                                     // this);
    return handleQueryCaseSplitReturn(caseSplits);
  }

  public List<IPathInfo> skipCall(SSAInvokeInstruction instr, CallGraph cg, CGNode callee) {
    return enterCall(instr, cg, callee, true);
  }

  // wrapper
  public List<IPathInfo> enterCall(SSAInvokeInstruction instr, CallGraph cg, CGNode callee) {
    return enterCall(instr, cg, callee, false);
  }
  
  /**
   * alter constraints to reflect that we are entering callee. note that
   * currentNode is still the caller node here
   * 
   * @param instr
   *          - invoke instruction making call to callee
   * @param callee
   *          - method being called
   * @return - list of paths to be executed (in addition to this one) if case
   *         split occurs during visit
   */
  private List<IPathInfo> enterCall(SSAInvokeInstruction instr, CallGraph cg, CGNode callee, boolean skip) {
    String calleeName = null;
    if (callee != null) calleeName = callee.getMethod().toString();
    else Util.Assert(skip);
    // if this call is relevant
    if (skip || callee.getIR() == null || calleeName.contains("equals") || calleeName.contains("hashCode")
        || calleeName.contains("indexOf") || calleeName.contains("Iterator") || !isCallRelevantToQuery(instr, callee, cg)) { 
      // heuristic: want to avoid executing equals(), hashCode() e.t.c because they're a time sink and are unlikely to lead to refutation
      query.dropConstraintsProduceableInCall(instr, this.getCurrentNode(), callee);
      if (Options.DEBUG) Util.Debug("skipping call " + instr + " and dropping produced constraints");
      return IPathInfo.FEASIBLE;
    } else if (callee.equals(this.currentNode)) { // is this a recursive call?
      if (Options.DEBUG) {
        Util.Debug("skipping recursive call " + callee.getMethod().toString() + " and dropping produced constraints");
      }
      // this is both a recursive call and relevant. overapproximate its effects by dropping constraints 
      // that it could possibly produce
      query.dropConstraintsProduceableInCall(instr, this.getCurrentNode(), callee);
      return IPathInfo.FEASIBLE;
    } else { 
      if (Options.DEBUG) Util.Debug("call stack size is " + callStack.size());
      // else, we should enter the call...if our call stack is not already too deep
      if (callStack.size() > Options.MAX_CALLSTACK_DEPTH) { // is our call stack too deep?
        if (Options.DEBUG)
          Util.Debug("skipping ordinary call " + callee + " due to call stack depth and dropping produced constraints");
        query.dropConstraintsProduceableInCall(instr, this.getCurrentNode(), callee);
        return IPathInfo.FEASIBLE;
      }
    }

    if (Options.DEBUG) {
      Util.Debug("entering call " + callee.getMethod().toString() + " from " + currentNode.getMethod().toString());
    }
    // push caller onto call stack and set current node to callee for the
    // current path
    List<IQuery> caseSplits = query.enterCall(instr, callee, this);
    this.pushCallStack(instr, callee);
    return handleQueryCaseSplitReturn(caseSplits);
  }

  /**
   * inspect call stack and determine if callee is part of a mutually recursive
   * sequence
   * 
   * @param callee
   *          - node we want to push on the call stack, but are scared is
   *          mutually recursive.
   * @param offendingIndex
   *          - index of previous occurence of callee in call stack
   * @return true if callee is part of mutually recursive sequence, false
   *         otherwise
   */
  boolean isMutuallyRecursive(CGNode callee, int offendingIndex) {
    Util.Pre(callStack.get(offendingIndex).getCGNode().equals(callee), "callstack should contain callee at the specified index!");
    // let the callee be X. say that we suspect X is part of a mutually
    // recursive sequence X C1 C2 ... X
    // we first record the sequence C1 C2 ... X, then check backwards from the
    // first occurence of X in the call stack to see if the sequence is matched
    LinkedList<CGNode> sequence = new LinkedList<CGNode>(); // the sequence of
                                                            // calls from the
                                                            // first occurrence
                                                            // of X to the top
                                                            // of the call stack
    for (int i = offendingIndex + 1; i < callStack.size(); i++) {
      sequence.push(callStack.get(i).getCGNode());
    }
    Util.Assert(!sequence.isEmpty(), "non-mutual recursion should have been caught by the regular recursion case!");
    if (offendingIndex == 0)
      return false; // no sequence leading up to the first call...not confirmed
                    // mutual recursion
    // see if the sequence of calls leading up to this occurrence of X matches
    // the previous sequence
    for (int i = offendingIndex - 1; i > -1; i++) {
      if (!sequence.pop().equals(callStack.get(i).getCGNode()))
        return false;
    }
    Util.Assert(false, "mutual recursion: " + callee + " " + Util.printCollection(callStack));
    // entire sequence compared equal; we have mutual recursion
    return true;
  }

  /**
   * special case for piecewise execution; need to do indirect parameter binding
   */
  public void enterCallFromJump(CGNode callee) {
    if (Options.DEBUG) Util.Debug("entering call " + callee + " from jump");
    query.enterCallFromJump(callee);
  }

  /**
   * drop all constraints that contain locals from the query
   */
  public void removeAllLocalConstraintsFromQuery() {
    query.removeAllLocalConstraints();
  }

  /**
   * get all methods that could potentially produce some part of the query
   */
  public Map<Constraint, Set<CGNode>> getModifiersForQuery() {
    return query.getModifiersForQuery();
  }

  /**
   * if we have context-sensitive CGNode's, make that contextual constraints
   * (such as receiver constraints explicit) in the query
   */
  public boolean addContextualConstraints(CGNode node) {
    return query.addContextualConstraints(node, this);
    // return true;
  }

  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead) {
    Util.Debug("dropping loop produceable constraints");
    query.removeLoopProduceableConstraints(loopHead, this.currentNode);
  }

  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead) {
    return query.containsLoopProduceableConstraints(loopHead, this.currentNode);
  }

  /**
   * search backwards in CFG until we find a branch instr; push it onto the
   * branch stack
   */
  /*
   * void findAndPushNextBranchInstruction(IR ir) { //final IR ir =
   * this.getCurrentNode().getIR(); SSACFG.BasicBlock currentBlock =
   * this.getCurrentBlock(); SSACFG.BasicBlock lastBlock = this.getLastBlock();
   * int startLine = this.getCurrentLineNum();
   * 
   * while (true) { // until we find a branch instr or reach the end of the
   * procedure List<SSAInstruction> instrs = currentBlock.getAllInstructions();
   * for (int i = instrs.size() - 1; i > -1; i--) { SSAInstruction instr =
   * instrs.get(i); if (i <= startLine) { if (instr instanceof
   * SSAConditionalBranchInstruction) { IBranchPoint point =
   * IBranchPoint.makeBranchPoint((SSAConditionalBranchInstruction) instr, i,
   * currentBlock, ir); this.pushBranchStack(point, lastBlock); return; } } } //
   * don't look at instructions in current block; we will never find the branch
   * instruction we are looking for there Collection<ISSABasicBlock> preds =
   * ir.getControlFlowGraph().getNormalPredecessors(currentBlock); if
   * (preds.size() == 0) return; // path has reached beginning of procedure else
   * if (preds.size() == 1) { // optimization: for the single predecessor case,
   * can go to next block directly SSACFG.BasicBlock nextBlock =
   * (SSACFG.BasicBlock) preds.iterator().next(); lastBlock = currentBlock;
   * currentBlock = nextBlock; startLine =
   * currentBlock.getAllInstructions().size() - 1; } else return; // the path
   * has split; will find the branch instr's corresponding to this split when we
   * reach it during execution } }
   */

  public boolean isCallStackEmpty() {
    return callStack.isEmpty();
  }

  public static int getPathIdCounter() {
    return pathIdCounter;
  }

  public CGNode getCurrentNode() {
    return currentNode;
  }

  public void setCurrentNode(CGNode currentNode) {
    this.currentNode = currentNode;
    addContextualConstraints(currentNode); // TODO: is this information
                                           // reflected elsewhere?
  }

  public SSACFG.BasicBlock getCurrentBlock() {
    return currentBlock;
  }

  /**
   * set currentBlock and store old currentBlock as lastBlock
   */
  public void setCurrentBlock(SSACFG.BasicBlock currentBlock) {
    if (Options.DEBUG)
      Util.Pre(currentBlock != null, "can't set block to null!");
    this.lastBlock = this.currentBlock;
    this.currentBlock = currentBlock;
  }

  public SSACFG.BasicBlock getLastBlock() {
    return lastBlock;
  }

  public int getCurrentLineNum() {
    return currentLineNum;
  }

  public void setCurrentLineNum(int currentLineNum) {
    this.currentLineNum = currentLineNum;
  }

  public int getPathId() {
    return pathId;
  }

  public boolean foundWitness() {
    return query.foundWitness();
  }

  public boolean isCallRelevantToQuery(SSAInvokeInstruction instr, CGNode callee, CallGraph cg) {
    Util.Debug("checking call relevance");
    return query.isCallRelevant(instr, this.currentNode, callee, cg);
  }

  public void declareFakeWitness() {
    if (Options.DEBUG)
      Util.Debug("declaring fake witness");
    query.declareFakeWitness();
  }

  public boolean containsConstraint(Constraint constraint) {
    return query.containsConstraint(constraint);
  }

  // only to be used in regression tests
  public static void resetPathIdCounter() {
    pathIdCounter = 1;
  }

  // has query been refuted?
  public boolean isFeasible() {
    if (externallyRefuted)
      return false; // refutation by external forces takes precedence over query
                    // feasability
    return query != null && // null query means that this is a dummy path (i.e.
                            // branch placeholder)
        query.isFeasible();
  }

  public boolean isDummy() {
    return this.pathId == DUMMY_ID;
  }

  public boolean isLoopMergeIndicator() {
    return this.pathId == MERGE_ID;
  }

  public boolean containsQuery(IPathInfo other) {
    return this.query.contains(other.query);
  }

  /**
   * call to force refutation of path even when query is not explicitly
   * contradictory for example, if we have some mechanism for summaries, we
   * should call refute() when a path is refuted by a summary
   */
  public void refute() {
    this.externallyRefuted = true;
  }

  public boolean addSeen(CGNode seenNode) {
    return piecewiseGraph.addSeen(this, seenNode);
  }

  public void setAtBranchPoint(boolean bool) {
    this.atBranchPoint = bool;
  }

  public boolean atBranchPoint() {
    return atBranchPoint;
  }

  public void initializeStaticFieldsToDefaultValues() {
    query.intializeStaticFieldsToDefaultValues();
  }

  public List<DependencyRule> getWitnessList() {
    return query.getWitnessList();
  }
  
  boolean startedInLoop = false;
  public void setStartedInLoop() {
    startedInLoop = true;
  }
  public void clearStartedInLoop() { startedInLoop = false; }

  // TODO: possibly use program point information in hash code as well
  @Override
  public int hashCode() {
    return query.hashCode();
  }

  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IPathInfo))
      return false;
    IPathInfo otherInfo = (IPathInfo) other;
    if (query == null && otherInfo.query == null) {
      if (this.isLoopMergeIndicator() && otherInfo.isLoopMergeIndicator()) {
        return this.currentBlock.equals(otherInfo.currentBlock);
      } // else, we have two at least one dummy path
      return false;
    } else if ((query == null) != (otherInfo.query == null))
      return false; // one query is null and the other isn't
    if (this.pathId == otherInfo.getPathId())
      return true; // optimization; save cost of comparing queries when id's are
                   // equal
    return query.equals(otherInfo.query);
    // return false;
  }

  // @Override
  /*
   * public int compareTo(Object other) { if (!(other instanceof IPathInfo))
   * Util.Unimp("comparing pathInfo to non-pathInfo"); IPathInfo otherPath =
   * (IPathInfo) other; if (query == null && otherPath.query == null) return 0;
   * if (query == null) return -1; if (otherPath.query == null) return 1; return
   * query.compareTo(otherPath.query); }
   */

  @Override
  public String toString() {
    if (query == null) {
      if (pathId == DUMMY_ID) return "DUMMY";// this.getPathId() + "";
      else if (pathId == MERGE_ID) return "MERGE";
    }
    return this.getPathId() + " " + query.toString();
  }

  static class PiecewiseGraph {
    private final Set<Pair<CGNode, CGNode>> traversedEdges;
    private final Set<Pair<CGNode, CGNode>> skippedEdges;
    private final Set<CGNode> seenNodes;

    public PiecewiseGraph() {
      this.traversedEdges = HashSetFactory.make();//new HashSet<Pair<CGNode, CGNode>>();
      this.skippedEdges = HashSetFactory.make();//new HashSet<Pair<CGNode, CGNode>>();
      this.seenNodes = HashSetFactory.make();//new HashSet<CGNode>();
    }

    private PiecewiseGraph(Set<Pair<CGNode, CGNode>> traversedEdges, Set<Pair<CGNode, CGNode>> skippedEdges, Set<CGNode> seenNodes) {
      this.traversedEdges = traversedEdges;
      this.skippedEdges = skippedEdges;
      this.seenNodes = seenNodes;
    }

    public PiecewiseGraph deepCopy() {
      return new PiecewiseGraph(Util.deepCopySet(traversedEdges), Util.deepCopySet(skippedEdges), Util.deepCopySet(seenNodes));
    }

    public boolean addSeen(IPathInfo path, CGNode caller) {
      boolean seen = seenNodes.add(caller);
      if (seen)
        addTraversedEdge(path.getCurrentNode(), caller);
      else
        addSkippedEdge(path.getCurrentNode(), caller);
      return seen;
    }

    private void addTraversedEdge(CGNode src, CGNode snk) {
      traversedEdges.add(Pair.make(src, snk));
    }

    private void addSkippedEdge(CGNode src, CGNode snk) {
      skippedEdges.add(Pair.make(src, snk));
    }

  }

}

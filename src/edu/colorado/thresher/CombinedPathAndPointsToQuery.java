package edu.colorado.thresher;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.util.intset.OrdinalSet;

/**
 * Path and points-to query that share information to make each more precise.
 * 
 * @author sam
 */

// PathQuery is the base class because it takes most of the info from the
// points-to query
public class CombinedPathAndPointsToQuery extends PathQuery {

  final PointsToQuery pointsToQuery;
  boolean fakeWitness = false;

  public CombinedPathAndPointsToQuery(PointsToQuery pointsToQuery) {// ,
                                                                    // Z3Context
                                                                    // ctx) {
    super(pointsToQuery.depRuleGenerator);// , ctx);
    this.pointsToQuery = pointsToQuery;
  }

  CombinedPathAndPointsToQuery(PointsToQuery pointsToQuery, PathQuery pathQuery) {
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator); // pathQuery.ctx);
    this.pointsToQuery = pointsToQuery;
  }

  /**
   * @return true if the query has been successfully witnessed, false otherwise
   */
  public boolean foundWitness() {
    return fakeWitness || (super.foundWitness() && pointsToQuery.foundWitness());
  }

  @Override
  public CombinedPathAndPointsToQuery deepCopy() {
    return new CombinedPathAndPointsToQuery(pointsToQuery.deepCopy(), super.deepCopy());
  }

  @Override
  public boolean isFeasible() {
    return super.isFeasible() && pointsToQuery.isFeasible();
  }

  @Override
  public void intersect(IQuery other) {
    Util.Assert(other instanceof CombinedPathAndPointsToQuery, "Not sure how to deal with query type " + other.getClass());
    CombinedPathAndPointsToQuery query = (CombinedPathAndPointsToQuery) other;
    // this.pointsToQuery.intersect(query.pointsToQuery);
    super.intersect((PathQuery) query);
  }

  @Override
  public List<IQuery> visitPhi(SSAPhiInstruction instr, int phiIndex, IPathInfo currentPath) {
    List<IQuery> pathResults = super.visitPhi(instr, phiIndex, currentPath);
    if (pathResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    List<IQuery> ptResults = pointsToQuery.visitPhi(instr, phiIndex, currentPath);
    if (ptResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Debug("CONS " + this.toString());
    return combinePathAndPointsToQueries(ptResults, pathResults);
    // return ptResults;
  }

  @Override
  boolean visit(SSANewInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable local = new ConcretePointerVariable(node, instr.getDef(), this.depRuleGenerator.getHeapModel());
    if (pathVars.contains(local)) {
      if (instr.getNewSite().getDeclaredType().isArrayType()) { // special case
                                                                // for arrays
        // may need to update path constraints with the length of this array
        SimplePathTerm arrLength;
        if (tbl.isConstant(instr.getUse(0)))
          arrLength = new SimplePathTerm(tbl.getIntValue(instr.getUse(0)));
        else
          arrLength = new SimplePathTerm(new ConcretePointerVariable(node, instr.getUse(0), this.depRuleGenerator.getHeapModel()));
        substituteExpForFieldRead(arrLength, local, SimplePathTerm.LENGTH);
      }

      boolean found = false;

      InstanceKey key = depRuleGenerator.getHeapModel().getInstanceKeyForAllocation(node, instr.getNewSite());
      if (key != null) {
        PointerVariable newVar = Util.makePointerVariable(key);
        substituteExpForVar(new SimplePathTerm(newVar), local);
      }
      /*
       * for (PointsToEdge edge : this.pointsToQuery.constraints) {
       * Util.Debug("constraint pt edge " + edge); if
       * (edge.getSource().equals(local)) { // does the points-to analysis hold
       * a ref to this allocation site? substituteExpForVar(new
       * SimplePathTerm(edge.getSink()), local); found = true; } } // if not
       * found, no ref in points constraints; all a new() instr can do for us is
       * resolve a constraint of the form "x != null"
       * 
       * for (PointsToEdge edge : this.pointsToQuery.produced) {
       * Util.Debug("produced pt edge " + edge); if
       * (edge.getSource().equals(local)) { // does the points-to analysis hold
       * a ref to this allocation site? substituteExpForVar(new
       * SimplePathTerm(edge.getSink()), local); found = true; } } // if not
       * found, no ref in points constraints; all a new() instr can do for us is
       * resolve a constraint of the form "x != null"
       */
      // if (!found) substituteExpForVar(SimplePathTerm.NON_NULL, local);
      return isFeasible();
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath, Set<PointsToEdge> refuted) {
    // visit path constraints first, since they can't cause case-splits
    List<IQuery> pathResults = super.visit(instr, currentPath, refuted);
    if (pathResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    List<IQuery> ptResults = pointsToQuery.visit(instr, currentPath, this.pathVars, refuted);
    if (ptResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    if (Options.DEBUG)
      Util.Debug("CONS " + this.toString());
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) {
    /*
     * // visit path constraints first, since they can't cause case-splits
     * List<IQuery> pathResults = super.visit(instr, currentPath); if
     * (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
     * Util.Assert(pathResults.isEmpty(),
     * "should never be case splits on path constraints!");
     */

    List<IQuery> ptResults = pointsToQuery.visit(instr, currentPath, this.pathVars, new HashSet<PointsToEdge>());
    if (ptResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    if (Options.DEBUG)
      Util.Debug("CONS " + this.toString());

    // visit path constraints first, since they can't cause case-splits
    List<IQuery> pathResults = super.visit(instr, currentPath);
    if (pathResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  @Override
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    List<IQuery> ptResults = pointsToQuery.enterCall(instr, callee, currentPath, this.pathVars);
    if (ptResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Assert(ptResults.isEmpty(), "Unimp: handling case splits at calls!");
    List<IQuery> pathResults = super.enterCall(instr, callee, currentPath);
    if (pathResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  /**
   * if we are entering a call from a jump, we cannot do parameter binding
   * directly, as we do normally instead, we must be a a bit more clever and use
   * the dependency rules to help us make relevant bindings
   */
  @Override
  public void enterCallFromJump(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    this.pointsToQuery.enterCallFromJump(instr, callee, currentPath);
    // if params were bound, they will be in the produced set. apply these param
    // bindings to the path constraints
    for (PointsToEdge constraint : pointsToQuery.produced) {
      if (this.pathVars.contains(constraint.getSink())) {
        substituteExpForVar(new SimplePathTerm(constraint.getSource()), constraint.getSink());

      }
    }
    /*
     * Set<DependencyRule> rulesProducedByCall =
     * depRuleGenerator.getRulesForInstr(instr, currentPath.getCurrentNode());
     * Util.Assert(rulesProducedByCall != null, "no rules for call " + instr +
     * " from " + currentPath.getCurrentNode()); for (DependencyRule rule :
     * rulesProducedByCall) { Util.Debug("rule produced by call " + rule);
     * PointsToEdge shown = rule.getShown(); PointerVariable snk =
     * shown.getSink(); if (this.pathVars.contains(snk)) { // sub heap loc for
     * its local pointer Util.Debug("enter call: subbing " + shown.getSource() +
     * " for " + snk); substituteExpForVar(new
     * SimplePathTerm(shown.getSource()), snk); } }
     */
  }

  @Override
  public void declareFakeWitness() {
    if (Options.DEBUG)
      Util.Debug("declaring fake witness");
    this.fakeWitness = true;
  }

  @Override
  public boolean containsStaleConstraints(CGNode currentNode) {
    return pointsToQuery.containsStaleConstraints(currentNode) || super.containsStaleConstraints(currentNode);
  }

  @Override
  public List<IQuery> returnFromCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    List<IQuery> ptResults = pointsToQuery.returnFromCall(instr, callee, currentPath);
    if (ptResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    List<IQuery> pathResults = super.returnFromCall(instr, callee, currentPath);
    if (pathResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  /**
   * @return - cartesian product of two lists of case splits; one points-to and
   *         one path
   */
  List<IQuery> combinePathAndPointsToQueries(List<IQuery> pointsToQueries, List<IQuery> pathQueries) {
    boolean ptEmpty = pointsToQueries == IQuery.FEASIBLE, pathEmpty = pathQueries == IQuery.FEASIBLE;
    if (ptEmpty && pathEmpty)
      return IQuery.FEASIBLE;
    List<IQuery> combinedQuery = new LinkedList<IQuery>();
    if (!ptEmpty && !pathEmpty) {
      Util.Unimp("case split in path and points-to");
      // TODO: would need to mix in current query here as well, which would get
      // messy...
      for (IQuery ptQuery : pointsToQueries) {
        for (IQuery pathQuery : pathQueries) {
          ptQuery.deepCopy();
          pathQuery.deepCopy();
          combinedQuery.add(new CombinedPathAndPointsToQuery((PointsToQuery) ptQuery.deepCopy(), (PathQuery) pathQuery.deepCopy()));
        }
      }
    } else if (!pathEmpty) {
      for (IQuery pathQuery : pathQueries) {
        combinedQuery.add(new CombinedPathAndPointsToQuery(pointsToQuery.deepCopy(), (PathQuery) pathQuery.deepCopy()));
      }
    } else if (!ptEmpty) {
      for (IQuery ptQuery : pointsToQueries) {
        combinedQuery.add(new CombinedPathAndPointsToQuery((PointsToQuery) ptQuery, super.deepCopy()));
      }
    }
    return combinedQuery;
  }

  @Override
  public boolean addContextualConstraints(CGNode node, IPathInfo currentPath) {
    return pointsToQuery.addContextualConstraints(node, currentPath) && super.addContextualConstraints(node, currentPath);
  }

  @Override
  public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) {
    return pointsToQuery.isCallRelevant(instr, caller, callee, cg)
        || this.doesCallWriteToHeapLocsInPathConstraints(instr, caller, callee, cg);
  }

  @Override
  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    if (!Options.LOOP_INVARIANT_INFERENCE)
      pointsToQuery.removeLoopProduceableConstraints(loopHead, currentNode);
    // else, only need to drop path constraints; we're computing a fixed point
    // over pt-constraints
    // super.removeLoopProduceableConstraints(loopHead, currentNode);
    // we only need to remove path constraints produceable in the loop... we
    // don't want to remove pts-to constraints; we are computing a fixed point
    // over those
    // dropConstraintsProuceableByRuleSet(Util.getRulesForLoop(loopHead,
    // currentNode, depRuleGenerator, depRuleGenerator.getCallGraph()));
    dropPathConstraintsWrittenInLoop(loopHead, currentNode);
  }

  private void dropPathConstraintsWrittenInLoop(SSACFG.BasicBlock loopHead, CGNode node) {
    if (this.constraints.isEmpty())
      return;
    Set<DependencyRule> loopRules = new TreeSet<DependencyRule>();
    Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(node); // get
                                                                        // all
                                                                        // rules
                                                                        // for
                                                                        // node
    if (rules != null) {
      for (DependencyRule rule : rules) { // keep only rules produced in loop
        // Util.Debug("rule shown " + rule.getShown());
        Util.Assert(rule.getBlock() != null, "no basic block for rule " + rule);
        if (WALACFGUtil.isInLoopBody(rule.getBlock(), loopHead, node.getIR())) {
          // Util.Debug("rule is loop rule");
          loopRules.add(rule);
        }
      }
      dropConstraintsProuceableByRuleSet(loopRules); // remove all constraints
                                                     // produceable by one of
                                                     // these rules
    }

    // check for additional relevant keys by consulting the points-to analysis
    ClassHierarchy cha = depRuleGenerator.getClassHierarchy();
    HeapModel hm = depRuleGenerator.getHeapModel();
    /*
     * Set<PointerKey> keys = new HashSet<PointerKey>(); for
     * (AtomicPathConstraint constraint : this.constraints) {
     * keys.addAll(constraint.getPointerKeys()); Set<SimplePathTerm> terms =
     * constraint.getTerms(); for (SimplePathTerm term : terms) { if
     * (term.getObject() != null && term.getFields() != null) { PointerVariable
     * pointedTo = term.getObject(); if (pointedTo != null && pointedTo
     * instanceof InstanceKey) { PointerKey key =
     * hm.getPointerKeyForInstanceField((InstanceKey)
     * pointedTo.getInstanceKey(), cha.resolveField(term.getFirstField())); if
     * (key != null) keys.add(key); } } } }
     */

    // the loop may also contain callees. drop any constraint containing vars
    // that these callees can write to
    Set<CGNode> targets = WALACFGUtil.getCallTargetsInLoop(loopHead, node, depRuleGenerator.getCallGraph());
    Set<AtomicPathConstraint> toDrop = new HashSet<AtomicPathConstraint>();
    for (CGNode callNode : targets) { // drop all vars that can be written by a
                                      // call in the loop body
      OrdinalSet<PointerKey> callKeys = depRuleGenerator.getModRef().get(callNode);

      for (AtomicPathConstraint constraint : constraints) {
        for (PointerKey key : constraint.getPointerKeys()) {
          if (callKeys.contains(key)) {
            toDrop.add(constraint);
            break;
          }
          // else, check for refs in pts-to constraints
          Set<SimplePathTerm> terms = constraint.getTerms();
          for (SimplePathTerm term : terms) {
            if (term.getObject() != null && term.getFields() != null) {
              PointerVariable pointedTo = this.pointsToQuery.getPointedTo(term.getObject());
              if (pointedTo != null && pointedTo.getInstanceKey() instanceof InstanceKey) {
                FieldReference fieldRef = term.getFirstField();
                if (fieldRef == null)
                  continue;
                IField fld = cha.resolveField(fieldRef);
                if (fld == null)
                  continue;
                PointerKey fieldKey = hm.getPointerKeyForInstanceField((InstanceKey) pointedTo.getInstanceKey(), fld);
                if (fieldKey == null)
                  continue;
                if (callKeys.contains(fieldKey)) {
                  toDrop.add(constraint);
                  break;
                }
              }
            }
          }
        }
      }

    }
    for (AtomicPathConstraint dropMe : toDrop) {
      if (Options.DEBUG)
        Util.Debug("dropping loop constraint " + dropMe);
      // constraints.remove(dropMe);
      removeConstraint(dropMe);
    }
  }

  @Override
  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    return pointsToQuery.containsLoopProduceableConstraints(loopHead, currentNode)
        || super.containsLoopProduceableConstraints(loopHead, currentNode);
  }

  @Override
  public boolean contains(IQuery other) {
    if (!(other instanceof CombinedPathAndPointsToQuery))
      return false;
    CombinedPathAndPointsToQuery otherQuery = (CombinedPathAndPointsToQuery) other;
    // return this.pointsToQuery.contains(otherQuery.pointsToQuery);
    return this.pointsToQuery.contains(otherQuery.pointsToQuery) && super.symbContains(otherQuery);
    // && super.constraints.containsAll(otherQuery.constraints);
  }

  @Override
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    this.pointsToQuery.dropConstraintsProduceableInCall(instr, caller, callee);
    this.dropPathConstraintsProduceableByCall(instr, caller, callee);
    if (this.foundWitness())
      Util.Debug("dropping constraints led to FAKE witness!");
    // Util.Assert(!this.foundWitness(),
    // "dropping constraints led to fake witness!");
  }

  void dropConstraintsProuceableByRuleSet(Set<DependencyRule> rules) {
    Set<PointerVariable> toDrop = new HashSet<PointerVariable>();
    Set<PointerVariable> relevantVars = new HashSet<PointerVariable>();
    for (PointerVariable var : this.pathVars) {
      if (!var.isLocalVar())
        relevantVars.add(var);
      else { // this is a local
        // try to use pts-to constraints to determine which heap loc this local
        // corresponds to
        PointerVariable pointedTo = this.pointsToQuery.getPointedTo(var);
        if (pointedTo == null) {
          // can't find this var in our points-to constraints; no telling what
          // it might point to. must drop it.
          toDrop.add(var);
        }
        relevantVars.add(pointedTo);
      }
    }
    for (PointerVariable var : toDrop)
      dropConstraintsContaining(var);
    relevantVars.removeAll(toDrop);

    Set<AtomicPathConstraint> toRemove = new HashSet<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : this.constraints) {
      // Util.Debug("constraint is " + constraint);
      Set<PointerVariable> vars = constraint.getVars();
      Set<FieldReference> fields = constraint.getFields();
      // see if a dependency rules can write to one of the heap loc's in the
      // path constraints
      for (DependencyRule rule : rules) {
        PointerVariable src = rule.getShown().getSource(); // snk =
                                                           // rule.getShown().getSink();
        // FieldReference field = rule.getShown().getFieldRef().getReference();
        if (vars.contains(src))
          toRemove.add(constraint);
        if (rule.getShown().getFieldRef() != null && fields.contains(rule.getShown().getFieldRef().getReference()))
          toRemove.add(constraint);
        // || vars.contains(snk)) toRemove.add(constraint);
      }
    }
    for (AtomicPathConstraint constraint : toRemove) {
      if (Options.DEBUG)
        Util.Debug("dropping constraint produceable by rule set" + constraint);
      removeConstraint(constraint);
    }
    super.rebuildZ3Constraints();
  }

  void dropPathConstraintsProduceableByCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    ConcretePointerVariable retval = null;
    if (instr.hasDef()) {
      retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      dropConstraintsContaining(retval);
    }
    // Set<DependencyRule> rulesProducedByCall =
    // Util.getRulesProducableByCall(callee, depRuleGenerator.getCallGraph(),
    // depRuleGenerator);
    // dropConstraintsProuceableByRuleSet(rulesProducedByCall);

    List<AtomicPathConstraint> toDrop = new LinkedList<AtomicPathConstraint>();
    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerKey key : constraint.getPointerKeys()) {
        if (keys.contains(key)) {
          toDrop.add(constraint);
          break;
        }
      }
    }
    for (AtomicPathConstraint dropMe : toDrop)
      removeConstraint(dropMe); // constraints.remove(dropMe);
  }

  boolean doesCallWriteToHeapLocsInPathConstraints(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) {
    // do constraints contain retval of this call?
    if (instr.hasDef()) {
      ConcretePointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      if (this.pathVars.contains(retval))
        return true; // constraints contain retval; definitely relevant
    }

    // do constraints contain a param passed to this function?
    SymbolTable tbl = caller.getIR().getSymbolTable();
    for (int i = 0; i < instr.getNumberOfParameters(); i++) {
      if (!tbl.isConstant(instr.getUse(i))) {
        PointerVariable arg = new ConcretePointerVariable(caller, instr.getUse(i), this.depRuleGenerator.getHeapModel());
        if (this.pathVars.contains(arg))
          return true; // constraints contain a non-constant param that's passed
                       // to this function; possibly relevant
      }
    }

    // does this call modify our path constraints according to its precomputed
    // mod set?
    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerKey key : constraint.getPointerKeys()) {
        if (keys.contains(key)) return true; // mod set says yes
        IClass declaringClass = null;
        if (key instanceof StaticFieldKey) {
          declaringClass = ((StaticFieldKey) key).getField().getDeclaringClass();
        } else if (key instanceof InstanceFieldKey) {
          declaringClass = ((InstanceFieldKey) key).getField().getDeclaringClass();
        }
        if (declaringClass != null) {
          // if this is an <init>/<clinit>, might initialize field to default values
          if (declaringClass.equals(callee.getMethod().getDeclaringClass())
              && (callee.getMethod().isClinit() || callee.getMethod().isInit())) {
            return true;
          }
        }
      }
    }

    return false;
  }

  /**
   * substitute actuals for formals in our constraint set (i.e., when returning
   * from call)
   * 
   * @param callerSymbolTable
   *          - symbol table for the caller
   */
  /*
   * boolean substituteActualsForFormals(SSAInvokeInstruction instr, CGNode
   * callerMethod, CGNode calleeMethod, SymbolTable callerSymbolTable) {
   * Util.Pre(!calleeMethod.equals(callerMethod),
   * "recursion should be handled elsewhere");
   * Util.Debug("substituting actuals for formals in path query"); for (int i =
   * 0; i < instr.getNumberOfParameters(); i++) { int use = instr.getUse(i);
   * PointerVariable formal = new ConcretePointerVariable(calleeMethod, i + 1,
   * this.depRuleGenerator.getHeapModel());
   * 
   * SimplePathTerm actual = null; if (callerSymbolTable.isIntegerConstant(use))
   * { Util.Debug("integer const"); actual = new
   * SimplePathTerm(callerSymbolTable.getIntValue(use)); } else if
   * (callerSymbolTable.isNullConstant(use)) { actual = SimplePathTerm.NULL; //
   * check for formal in pts-to constraints for (PointsToEdge edge :
   * pointsToQuery.constraints) { Util.Debug(edge.getSource() + " eq " +
   * formal); if (edge.getSource().equals(formal)) { Util.Debug("refuted! " +
   * formal + " must point to " + edge.getSink() + ", but it points to null.");
   * this.feasible = false; return false; } } } else if
   * (callerSymbolTable.isStringConstant(use)) actual = SimplePathTerm.NON_NULL;
   * // the only modeling we do of strings is that they are non-nul else if
   * (callerSymbolTable.isConstant(use)) Util.Unimp("other kinds of constants");
   * // TODO: support other constants else actual = new SimplePathTerm(new
   * ConcretePointerVariable(callerMethod, instr.getUse(i),
   * this.depRuleGenerator.getHeapModel()));
   * 
   * 
   * 
   * Util.Debug("subbing " + actual + " for " + formal);
   * substituteExpForVar(actual, formal); } return isFeasible(); }
   */

  @Override
  public void removeAllLocalConstraints() {
    this.removeAllLocalPathConstraints(); // IMPORTANT! must do this first,
                                          // otherwise we lose the local pts-to
                                          // info!
    pointsToQuery.removeAllLocalConstraints();
  }

  /**
   * take advantage of pts-to information to sub out locals for their heap
   * value, if known
   */
  public void removeAllLocalPathConstraints() {
    // first, sub out all locals for their corresponding heap locations, if we
    // know them
    for (PointsToEdge edge : pointsToQuery.constraints) {
      PointerVariable src = edge.getSource();
      if (src.isLocalVar() && this.pathVars.contains(src)) {
        if (Options.DEBUG)
          Util.Debug("subbing out for " + src + "; replacing with " + edge.getSink());
        // do substitution for snk of edge
        this.substituteExpForVar(new SimplePathTerm(edge.getSink()), src);
      }
    }

    for (PointsToEdge edge : pointsToQuery.produced) {
      PointerVariable src = edge.getSource();
      if (src.isLocalVar() && this.pathVars.contains(src)) {
        if (Options.DEBUG)
          Util.Debug("subbing out for " + src + "; replacing with " + edge.getSink());
        // do substitution for snk of edge
        this.substituteExpForVar(new SimplePathTerm(edge.getSink()), src);
      }
    }

    // now, can remove all local constraints
    List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerVariable var : constraint.getVars()) {
        if (var.isLocalVar())
          toRemove.add(constraint);
        break;
      }
    }
    for (AtomicPathConstraint constraint : toRemove)
      removeConstraint(constraint);// constraints.remove(constraint);
  }

  @Override
  public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranchFeasible) {
    return this.addConstraintFromBranchPointAndCheckForNull(point, trueBranchFeasible)
        && pointsToQuery.addConstraintFromBranchPoint(point, trueBranchFeasible);
  }

  public boolean addConstraintFromBranchPointAndCheckForNull(IBranchPoint point, boolean trueBranchFeasible) {
    SSAConditionalBranchInstruction instruction = point.getInstr();
    CGNode method = point.getMethod();
    SymbolTable tbl = point.getSymbolTable();
    // is this a comparison of constants?
    // if (instruction.isIntegerComparison() &&
    // tbl.isConstant(instruction.getUse(0)) &&
    // tbl.isConstant(instruction.getUse(1))) {
    if (tbl.isConstant(instruction.getUse(0)) && tbl.isConstant(instruction.getUse(1))) {
      // yes, so we can determine immediately whether this branch can be taken
      // (no need to add path constraints).
      return evaluateGuard(instruction, tbl, !trueBranchFeasible); // we should
                                                                   // negate the
                                                                   // path
                                                                   // constraint
                                                                   // if the
                                                                   // true
                                                                   // branch is
                                                                   // infeasible
    } else { // no. extract the path constraint from the branch condition
      AtomicPathConstraint constraint = getPathConstraintFromGuard(instruction, tbl, method, !trueBranchFeasible);
      if (constraint == null)
        return true; // null return means its a string comparison or something
                     // else we don't support. bail outc

      // check for null comparison against something that's already in the
      // pts-to constraints
      if (constraint.getLhs() instanceof SimplePathTerm && constraint.getRhs() instanceof SimplePathTerm) {
        SimplePathTerm lhs = (SimplePathTerm) constraint.getLhs(), rhs = (SimplePathTerm) constraint.getRhs();
        PointerVariable comparedToNull = null;
        if (lhs.isIntegerConstant() && lhs.getIntegerConstant() == 0)
          comparedToNull = rhs.getObject();
        else if (rhs.isIntegerConstant() && rhs.getIntegerConstant() == 0)
          comparedToNull = lhs.getObject();
        if (comparedToNull != null) {
          ConditionalBranchInstruction.Operator op = constraint.getOp();
          // this is a null comparison; see if this appears in the pts-to
          // constraints
          for (PointsToEdge edge : pointsToQuery.produced) {
            if (edge.getSource().equals(comparedToNull)) {
              if (op == ConditionalBranchInstruction.Operator.EQ) {
                if (Options.DEBUG)
                  Util.Debug("refuted by comparsion to null; pts-to constraints require var " + comparedToNull + " to be non-null!");
                this.feasible = false;
                return false;
              } else if (op == ConditionalBranchInstruction.Operator.NE) {
                // already know this can't be null; constraint is satisfied
                return true;
              }
            }
          }

          for (PointsToEdge edge : pointsToQuery.constraints) {
            if (edge.getSource().equals(comparedToNull)) {
              if (op == ConditionalBranchInstruction.Operator.EQ) {
                if (Options.DEBUG)
                  Util.Debug("refuted by comparsion to null; pts-to constraints require var " + comparedToNull + " to be non-null!");
                this.feasible = false;
                return false;
              } else if (op == ConditionalBranchInstruction.Operator.NE) {
                // already know this can't be null; constraint is satisfied
                return true;
              }
            }
          }
        }
      }

      if (addConstraint(constraint))
        return isFeasible();
      return true; // else, constraint already in set; no need to check
                   // feasibility
    }
  }

  @Override
  public void intializeStaticFieldsToDefaultValues() {
    pointsToQuery.intializeStaticFieldsToDefaultValues();
    super.intializeStaticFieldsToDefaultValues();
  }

  /**
   * @return - set of *all* pointer keys associated with constraint, including
   *         the ones related according to the points-to analysis
   */
  private Set<PointerKey> getPointerKeysForPathConstraint(AtomicPathConstraint constraint) {
    /*
     * Set<PointerKey> keysForConstraint = new HashSet<PointerKey>();
     * ClassHierarchy cha = depRuleGenerator.getClassHierarchy(); HeapModel hm =
     * depRuleGenerator.getHeapModel(); // add pointer keys already known to be
     * associated with this constraint
     * keysForConstraint.addAll(constraint.getPointerKeys());
     * Set<SimplePathTerm> terms = constraint.getTerms(); for (SimplePathTerm
     * term : terms) { if (term.getObject() != null && term.getFields() != null)
     * { PointerVariable pointedTo = term.getObject(); if (pointedTo != null &&
     * pointedTo instanceof InstanceKey) { PointerKey key =
     * hm.getPointerKeyForInstanceField((InstanceKey)
     * pointedTo.getInstanceKey(), cha.resolveField(term.getFirstField())); if
     * (key != null) keysForConstraint.add(key); } } } return keysForConstraint;
     */

    ClassHierarchy cha = depRuleGenerator.getClassHierarchy();
    HeapModel hm = depRuleGenerator.getHeapModel();
    Set<PointerKey> keysForConstraint = new HashSet<PointerKey>();
    // add pointer keys already known to be associated with this constraint
    keysForConstraint.addAll(constraint.getPointerKeys());

    // check for refs in pts-to constraints
    Set<SimplePathTerm> terms = constraint.getTerms();
    for (SimplePathTerm term : terms) {
      if (term.getObject() != null && term.getFields() != null) {
        PointerVariable pointedTo = term.getObject();// this.pointsToQuery.getPointedTo(term.getObject());
        if (pointedTo != null && pointedTo.getInstanceKey() instanceof InstanceKey) {
          FieldReference fieldRef = term.getFirstField();
          if (fieldRef == null)
            continue;
          IField fld = cha.resolveField(fieldRef);
          if (fld == null)
            continue;
          PointerKey fieldKey = hm.getPointerKeyForInstanceField((InstanceKey) pointedTo.getInstanceKey(), fld);
          if (fieldKey == null)
            continue;
          keysForConstraint.add(fieldKey);
        }
      }
    }
    return keysForConstraint;
  }

  private Map<Constraint, Set<CGNode>> getModifiersForQueryHelper() {
    Map<PointerKey, Set<CGNode>> reversedModRef = this.depRuleGenerator.getReversedModRef();
    Map<Constraint, Set<CGNode>> constraintModMap = new HashMap<Constraint, Set<CGNode>>();
    for (AtomicPathConstraint constraint : this.constraints) {
      Set<CGNode> nodes = new HashSet<CGNode>();
      // addClassInitsForConstraintFields(constraint, nodes); // add class init
      // if it may write to the constraint
      for (PointerKey key : getPointerKeysForPathConstraint(constraint)) {
        Set<CGNode> modRefNodes = reversedModRef.get(key);
        if (modRefNodes == null)
          continue; // this can happen when var is the this param for a class
                    // with no fields
        // Util.Assert(modRefNodes != null, "no mod ref set for " + key);
        for (CGNode node : modRefNodes) {
          // add to mapping *only* if node modifies pointer key directly (not
          // via callees)
          // this is because the use of the reversed mod/ref is to jump directly
          // to
          // the node that might modify our key of interest
          if (Util.writesKeyLocally(node, key, this.depRuleGenerator.getHeapModel(), this.depRuleGenerator.getHeapGraph(),
              this.depRuleGenerator.getClassHierarchy())) {
            nodes.add(node);
          }
        }
        // nodes.addAll(modRefNodes);
      }
      constraintModMap.put(constraint, nodes);
    }
    return constraintModMap;
  }

  /**
   * add the class init for each field to the set of relevant nodes need to do
   * this because class inits can write to fields by writing their default
   * values. this implicit write is not reflected in the normal mod/ref analysis
   * 
   * @param constraint
   * @param nodes
   */
  /*
   * private void addClassInitsForConstraintFields(AtomicPathConstraint
   * constraint, Set<CGNode> nodes) {
   * Util.Debug("adding clinits for constraint " + constraint); for (PointerKey
   * key :constraint.getPointerKeys()) { IField fieldKey; if (key instanceof
   * InstanceFieldKey) fieldKey = ((InstanceFieldKey) key).getField(); else if
   * (key instanceof StaticFieldKey) fieldKey = ((StaticFieldKey)
   * key).getField(); else continue; fieldKey.getDeclaringClass(); IMethod clit
   * = fieldKey.getDeclaringClass().getClassInitializer();
   * Util.Debug("classInit is " + clit); MethodReference classInit =
   * fieldKey.getDeclaringClass().getClassInitializer().getReference();
   * Set<CGNode> classInitNodes =
   * this.depRuleGenerator.getCallGraph().getNodes(classInit);
   * Util.Assert(classInitNodes.size() == 1); // should only be one class init
   * nodes.add(classInitNodes.iterator().next()); } }
   */

  @Override
  public Map<Constraint, Set<CGNode>> getModifiersForQuery() {
    Map<Constraint, Set<CGNode>> mods = pointsToQuery.getModifiersForQuery();
    mods.putAll(getModifiersForQueryHelper());
    return mods;
  }

  @Override
  public boolean containsConstraint(Constraint constraint) {
    if (constraint instanceof PointsToEdge)
      return pointsToQuery.containsConstraint(constraint);
    return super.containsConstraint(constraint);
  }

  @Override
  public List<DependencyRule> getWitnessList() {
    return pointsToQuery.getWitnessList();
  }

  /*
   * @Override public int compareTo(Object other) { if (!(other instanceof
   * CombinedPathAndPointsToQuery))
   * Util.Unimp("comparing with different kind of query");
   * CombinedPathAndPointsToQuery otherQuery = (CombinedPathAndPointsToQuery)
   * other; int ptComparison =
   * pointsToQuery.compareTo(otherQuery.pointsToQuery); if (ptComparison != 0)
   * return ptComparison; int pathComparison = super.compareTo((PathQuery)
   * otherQuery); return pathComparison; }
   */

  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CombinedPathAndPointsToQuery))
      return false;
    CombinedPathAndPointsToQuery otherQuery = (CombinedPathAndPointsToQuery) other;
    return this.pointsToQuery.equals(otherQuery.pointsToQuery) && super.equals((PathQuery) otherQuery);
  }

  @Override
  public int hashCode() {
    // /Util.Unimp("don't hash this query!");
    // return 5;
    return 37 * this.pointsToQuery.hashCode() + super.hashCode();
  }

  @Override
  public String toString() {
    return pointsToQuery.toString() + "\n" + super.toString();
  }

}

package edu.colorado.thresher;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.Context;
import com.ibm.wala.ipa.callgraph.ContextItem;
import com.ibm.wala.ipa.callgraph.ContextKey;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAGetCaughtExceptionInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.intset.BitVectorIntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.OrdinalSet;

/**
 * query regarding feasability of heap state involving points-to edges
 * 
 * @author sam
 */
public class PointsToQuery implements IQuery {

  private static final Set<PointerVariable> EMPTY_PV_VAR_SET = new HashSet<PointerVariable>();
  private static final Set<PointsToEdge> EMPTY_PT_EDGE_SET = new HashSet<PointsToEdge>();

  final AbstractDependencyRuleGenerator depRuleGenerator;
  // final TreeSet<PointsToEdge> constraints; // constraints that have not been
  // produced yet; these need to be ordered for comparison
  final Set<PointsToEdge> constraints; // constraints that have not been
                                       // produced yet
  // constraints with local LHS's that have already been produced. these do not
  // need to be ordered for comparison
  final Set<PointsToEdge> produced;
  // the constraints produced, in the order they were produced
  private final List<DependencyRule> witnessList;
  private List<PointsToEdge> unsatCore = new LinkedList<PointsToEdge>();

  private boolean feasible = true; // this is just a sanity check to make sure
                                   // that refuted queries are not re-used

  private int hash;

  // public PointsToQuery(Set<PointsToEdge> startConstraints, PointsToEdge
  // producedEdge, AbstractDependencyRuleGenerator depRuleGenerator) {
  public PointsToQuery(DependencyRule startRule, AbstractDependencyRuleGenerator depRuleGenerator) {
    // create a tree set out of the input set; typically, the input set is
    // immutable (comes from toShow set of a dep rule), so we cannot use it as
    // our constraint set
    // this.constraints = new TreeSet<PointsToEdge>();
    this.constraints = new HashSet<PointsToEdge>();
    constraints.addAll(startRule.getToShow());
    this.depRuleGenerator = depRuleGenerator;
    this.produced = new HashSet<PointsToEdge>();
    PointsToEdge producedEdge = startRule.getShown();
    if (producedEdge.getSource().isLocalVar())
      this.produced.add(producedEdge);
    this.witnessList = new LinkedList<DependencyRule>();
    this.witnessList.add(startRule);
  }

  public PointsToQuery(PointsToEdge startEdge, AbstractDependencyRuleGenerator depRuleGenerator) {
    // this.constraints = new TreeSet<PointsToEdge>();
    this.constraints = new HashSet<PointsToEdge>();
    addConstraint(startEdge);
    this.depRuleGenerator = depRuleGenerator;
    this.produced = new HashSet<PointsToEdge>();
    this.witnessList = new LinkedList<DependencyRule>();
  }

  // constructor for deep copies
  PointsToQuery(Set<PointsToEdge> constraints, Set<PointsToEdge> produced, List<DependencyRule> witnessList,
      AbstractDependencyRuleGenerator depRuleGenerator) {
    this.constraints = constraints;
    this.produced = produced;
    this.witnessList = witnessList;
    this.depRuleGenerator = depRuleGenerator;
  }

  @Override
  public PointsToQuery deepCopy() {
    return new PointsToQuery(Util.deepCopyPointsToEdgeSet(constraints), Util.deepCopySet(produced), Util.deepCopyList(witnessList),
        depRuleGenerator);
  }

  @Override
  public boolean foundWitness() {
    return constraints.isEmpty(); // we have a witness when there are no
                                  // constraints left to produce
  }

  @Override
  public boolean isFeasible() {
    return feasible;
  }

  @Override
  public void intersect(IQuery other) {
    Util.Assert(other instanceof PointsToQuery, "Unimp: intersecting with other kind of query");
    PointsToQuery otherQuery = (PointsToQuery) other;
    this.constraints.retainAll(otherQuery.constraints);
    this.produced.retainAll(otherQuery.produced);
  }

  @Override
  public boolean containsStaleConstraints(CGNode node) {
    for (PointsToEdge edge : constraints) {
      // do any constraints have a local var from node on the LHS?
      if (edge.getSource().isLocalVar() && edge.getSource().getNode().equals(node)) {
        if (Options.DEBUG)
          Util.Debug("found stale constraint " + edge + "\nfor method " + node + "\nin " + this);
        this.feasible = false;
        return true;
      }
    }
    return false;
  }

  private Set<DependencyRule> getRulesForInstr(SSAInstruction instr, IPathInfo currentPath) {
    Set<DependencyRule> rules = depRuleGenerator.getRulesForInstr(instr, currentPath.getCurrentNode());
    return rules == null ? null : Collections.unmodifiableSet(rules);
  }

  @Override
  public List<IQuery> visitPhi(SSAPhiInstruction instr, int phiIndex, IPathInfo currentPath) {
    Set<DependencyRule> rules = getRulesForInstr(instr, currentPath);
    if (rules == null)
      return IQuery.FEASIBLE;
    PointerVariable matchingPhiVar = new ConcretePointerVariable(currentPath.getCurrentNode(), instr.getUse(phiIndex),
        this.depRuleGenerator.getHeapModel());
    Set<DependencyRule> matchingRules = new TreeSet<DependencyRule>();
    // prune rules that don't match our phiIndex
    for (DependencyRule rule : rules) {
      Set<PointsToEdge> toShow = rule.getToShow();
      for (PointsToEdge edge : toShow) {
        if (edge.getSource().equals(matchingPhiVar)) {
          matchingRules.add(rule);
        }
      }
    }
    // won't get a match if one of the phi terms is a null
    if (matchingRules.isEmpty())
      return IQuery.FEASIBLE;
    List<IQuery> splits = visitInternal(instr, currentPath, matchingRules, EMPTY_PV_VAR_SET, EMPTY_PT_EDGE_SET);
    if (Options.DEBUG)
      Util.Debug("after phi visit " + this);
    if (splits == IQuery.INFEASIBLE) {
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    // Util.Assert(splits.isEmpty(), "shouldn't have caseSplits for phi's!");
    return splits;
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) {
    Util.Assert(!(instr instanceof SSAInvokeInstruction) && !(instr instanceof SSAPhiInstruction), "instr " + instr
        + " should be handled elsewhere");
    return visit(instr, currentPath, EMPTY_PV_VAR_SET, EMPTY_PT_EDGE_SET);
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath, Set<PointsToEdge> refuted) {
    // what are the dependency rules generated by this instruction?
    Set<DependencyRule> rulesAtLine = getRulesForInstr(instr, currentPath);
    return visitInternal(instr, currentPath, rulesAtLine, EMPTY_PV_VAR_SET, refuted);
  }

  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath, Set<PointerVariable> extraVars, Set<PointsToEdge> refuted) {
    // what are the dependency rules generated by this instruction?
    Set<DependencyRule> rulesAtLine = getRulesForInstr(instr, currentPath);
    return visitInternal(instr, currentPath, rulesAtLine, extraVars, refuted);
  }

  /**
   * @param extraVars
   *          - list of pointer variables in another kind of constraint (such as
   *          path constraint) whose relevance we are also concerned with
   * @return
   */
  private List<IQuery> visitInternal(SSAInstruction instr, IPathInfo currentPath, Set<DependencyRule> rulesAtLine,
      Set<PointerVariable> extraVars, Set<PointsToEdge> refuted) {
    if (instr instanceof SSAGetCaughtExceptionInstruction) {
      if (Options.DEBUG)
        Util.Debug("refuted by exceptional path"); // we assume all thrown
                                                   // exception bubble to the
                                                   // top level
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    // DEBUGGING SANITY CHECK
    /*
     * if (Options.CHECK_ASSERTS) { if (Options.DEBUG) Util.Debug("CONS " +
     * this); for (PointsToEdge edge1 : this.constraints) { if
     * (!edge1.getSource().isLocalVar()) continue; for (PointsToEdge edge2 :
     * this.constraints) { if (edge2.getSource().equals(edge1.getSource()) &&
     * edge1.getSink() != edge2.getSink()) {
     * Util.Unimp("two occurences of local " + edge1.getSource() + " in " +
     * this); } } } }
     */
    // END DEBUG

    if (rulesAtLine == null || rulesAtLine.isEmpty()) {
      Util.Debug("No rules at line...returning");
      return IQuery.FEASIBLE;
    }
    // Util.Assert(!rulesAtLine.isEmpty(),
    // "non-null list should always contain rules");

    List<DependencyRule> applicableRules = new LinkedList<DependencyRule>();
    // TODO: track irrelevant rules? not doing so for now because it's
    // inefficient to check the consistency of irrelevant rules in every case...
    // may be important to keep track of irrelevant rules because we can still
    // get a refutation in the case where no rules are relevant, but none are
    // consistent either
    Set<DependencyRule> irrelevantRules = new TreeSet<DependencyRule>();

    int inconsistentRules = 0;

    int ruleCounter = 0; // debug only
    for (DependencyRule rule : rulesAtLine) {
      if (Options.DEBUG)
        Util.Debug("rule " + ++ruleCounter + " of " + rulesAtLine.size() + ": " + rule);
      // see if this rule is relevant w.r.t our points-to constraints
      if (isRuleRelevant(rule, currentPath, extraVars)) {
        Set<DependencyRule> newRules = isRuleConsistent(rule, this, irrelevantRules, unsatCore, refuted,
            currentPath.getCurrentNode());
        if (newRules != null) {
          if (Options.DEBUG)
            Util.Debug("consistent: " + newRules.size());
          applicableRules.addAll(newRules);
          unsatCore.clear();
        } else
          inconsistentRules++;
      }
    }

    List<IQuery> caseSplits = new LinkedList<IQuery>();
    if (applicableRules.isEmpty()) {
      if (inconsistentRules != 0) {// && caseSplits.isEmpty()) {
        Util.Debug("refuted by pts-to constraint! " + currentPath);
        this.feasible = false;
        return IQuery.INFEASIBLE;
      } else
        return IQuery.FEASIBLE; // else the current path is feasible as a
                                // "rule not applied" path or no applicable
                                // rules were found
    } else if (applicableRules.size() == 1) {
      DependencyRule rule = applicableRules.get(0);
      // PointsToQuery copy = this.deepCopy();
      if (!Options.ABSTRACT_DEPENDENCY_RULES)
        caseSplits.add(this.deepCopy()); // add "rule not applied" path. this is
                                         // now done elsewhere, no longer needed
      applyRule(rule, this);
      return caseSplits;
    } else { // many applicable rules
      LinkedList<IQuery> cases = new LinkedList<IQuery>();
      boolean first = true;
      PointsToQuery copy = this.deepCopy(); // need to make copy to make other
                                            // copies of
      if (Options.DEBUG)
        Util.Debug(applicableRules.size() + " applicable rules");
      if (Options.DEBUG)
        for (DependencyRule rule : applicableRules) {
          Util.Debug("rule " + rule);
        }
      if (!Options.ABSTRACT_DEPENDENCY_RULES)
        caseSplits.add(copy); // add "rule not applied" path
      // many applicable rules; case split!
      for (DependencyRule rule : applicableRules) {
        if (first) {
          applyRule(rule, this);
          first = false;
          continue; // first query will be the path we continue on (not added to
                    // case split array)
        }
        PointsToQuery curQuery = copy.deepCopy(); // create copy for this case
                                                  // and add it to case split
                                                  // array)
        applyRule(rule, curQuery);
        cases.addLast(curQuery);
      }
      if (Options.DEBUG)
        Util.Debug("returning " + cases.size() + " cases.");
      return cases;
    }
  }

  /**
   * purge produced set of all constraints with locals from callee on LHS
   * 
   * @param instr
   *          - call instruction that we have just finished executing
   * @param callee
   *          - target of call instruction that we have just finished executing
   */
  @Override
  public List<IQuery> returnFromCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    List<IQuery> caseSplits;
    if (currentPath.isCallStackEmpty()) { // special case; entering entirely new
                                          // node rather than returning to node
                                          // we were already in
      if (Options.GEN_DEPENDENCY_RULES_EAGERLY)
        depRuleGenerator.generateRulesForNode(currentPath.getCurrentNode());
      // enter call from perspective of caller node
      // TODO: need special case of visiting?
      bindActualsToFormals(instr, currentPath.getCurrentNode(), callee);
      if (!isFeasible())
        return IQuery.INFEASIBLE; // check for refutation--can refute based on
                                  // null bindings in the above
    } else
      caseSplits = IQuery.FEASIBLE;

    // we need to do this in case there were rules that we didn't apply when
    // entering the call because they weren't relevant, but they are relevant
    // now
    // TODO: is this heavy-handed? maybe we can just intellegently drop
    // constraints rather than re-entering the call...
    caseSplits = enterCall(instr, callee, currentPath);
    if (caseSplits == IQuery.INFEASIBLE) {
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    if (Options.CHECK_ASSERTS)
      Util.Assert(caseSplits.isEmpty(), "shouldn't case split here because the arguments to the call are known!");

    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
    for (PointsToEdge edge : produced) {
      if (edge.getSource().getNode().equals(callee))
        toRemove.add(edge);
    }
    for (PointsToEdge edge : toRemove) {
      boolean removed = produced.remove(edge);
      if (Options.CHECK_ASSERTS)
        Util.Assert(removed, "couldn't remove edge " + edge);
    }

    if (this.containsStaleConstraints(callee)) {
      if (Options.PIECEWISE_EXECUTION) {
        // TODO: hack! can make piecewise execution a bit more careful about
        // adding/removing local constraints
        removeAllLocalConstraints();
        return IQuery.FEASIBLE;
      }
      // Util.Unimp("refuting on stale constraints!");
      if (Options.DEBUG)
        Util.Debug("refuted by stale constraints!");
      return IQuery.INFEASIBLE;
    }
    // Util.Post(!this.con tainsStaleConstraints(callee),
    // "should not contain stale constraints after substitution!");
    return IQuery.FEASIBLE;
  }

  /**
   * bind formals to actuals that appear in the LHS of our current constraints,
   * and add resulting constraint to produced set
   * 
   * @return - list of formals that we added new constraints for
   */
  Set<PointerVariable> bindActualsToFormals(SSAInvokeInstruction instr, CGNode callerMethod, CGNode calleeMethod) {
    Util.Assert(!calleeMethod.equals(callerMethod), "recursion should be handled elsewhere");
    Util.Debug("binding actuals to formals: callee " + calleeMethod + "; caller: " + callerMethod + " instr " + instr);
    SymbolTable tbl = callerMethod.getIR().getSymbolTable();
    Set<PointsToEdge> toAdd = new TreeSet<PointsToEdge>(), toRemove = new TreeSet<PointsToEdge>();
    Set<PointerVariable> formalsAssigned = new HashSet<PointerVariable>();
    MutableIntSet argsSeen = new BitVectorIntSet();
    Set<PointerVariable> possiblyAliased = new HashSet<PointerVariable>();
    for (int i = 0; i < instr.getNumberOfParameters(); i++) {
      int argUse = instr.getUse(i);
      PointerVariable arg = new ConcretePointerVariable(callerMethod, argUse, this.depRuleGenerator.getHeapModel());
      PointerVariable formal = new ConcretePointerVariable(calleeMethod, i + 1, this.depRuleGenerator.getHeapModel());

      // necessary for cases when we pass the same value as two parameters i.e.
      // Object o; foo(o, o).
      if (!argsSeen.add(argUse))
        possiblyAliased.add(arg);

      for (PointsToEdge edge : constraints) {
        PointerVariable src = edge.getSource();
        if (src.equals(formal)) {
          if (tbl.isNullConstant(instr.getUse(i))) {
            if (Options.DEBUG)
              Util.Debug("refuted! " + formal + " must point to " + edge.getSink() + ", but it points to null.");
            this.feasible = false;
            return formalsAssigned;
          }

          PointsToEdge newEdge = new PointsToEdge(arg, edge.getSink());
          toAdd.add(newEdge);
          toRemove.add(edge);
          formalsAssigned.add(formal);
        }
      }
    }

    for (PointsToEdge edge : toRemove) {
      boolean removed = constraints.remove(edge);
      if (!removed)
        Util.Assert(removed, "couldn't remove edge " + edge + " from " + Util.printCollection(constraints));
    }
    for (PointsToEdge addMe : toAdd) {
      PointerVariable lhs = addMe.getSource();
      // check for multiple bindings for single LHS
      for (PointsToEdge edge : this.constraints) {
        if (lhs.equals(edge.getSource()) && !addMe.equals(edge)) {
          if (Options.DEBUG)
            Util.Debug("refuted by multiple binding! " + edge + " and " + addMe);
          this.feasible = false;
          return formalsAssigned;
        }
      }
      addConstraint(addMe);
    }

    if (!possiblyAliased.isEmpty()) { // handle case where aliasing relationship
                                      // may be created by param passing
      if (Options.DEBUG)
        Util.Debug("potential aliasing!");
      for (PointerVariable var : possiblyAliased) {
        Set<PointsToEdge> aliasedEdges = new TreeSet<PointsToEdge>(); // set of
                                                                      // edges
                                                                      // with
                                                                      // var as
                                                                      // LHS
        for (PointsToEdge edge1 : this.constraints) {
          if (edge1.getSource().isLocalVar() && edge1.getSource().equals(var))
            aliasedEdges.add(edge1);
        }
        toRemove.clear();
        toAdd.clear();
        for (PointsToEdge edge1 : aliasedEdges) { // for each edge with the same
                                                  // LHS
          for (PointsToEdge edge2 : aliasedEdges) {
            PointerVariable edge1Sink = edge1.getSink(), edge2Sink = edge2.getSink();
            if (edge1Sink.equals(edge2Sink)) {
              // sinks are the same; just pick one edge to remove
              toRemove.add(edge1);
              continue;
            }

            if (!edge1Sink.isSymbolic() && !edge2Sink.isSymbolic()) { // both
                                                                      // concrete
              // they can't be equal; we already checked for equality
              if (Options.DEBUG)
                Util.Debug("refuted by parameter binding! " + edge1 + " " + edge2);
              this.feasible = false;
              return formalsAssigned;
            } else if (edge1Sink.isSymbolic() && edge2Sink.isSymbolic()) { // both
                                                                           // symbolic
              // pick the smaller set of abstract locations, remove the other
              // set
              if (edge1Sink.symbContains(edge2Sink))
                toRemove.add(edge1);
              else if (edge2Sink.symbContains(edge1Sink))
                toRemove.add(edge2);
              else if (Util.intersectionNonEmpty(edge1Sink.getPossibleValues(), edge2Sink.getPossibleValues())) {
                // neither contains the other; weaken to their intersection
                toRemove.add(edge1);
                toRemove.add(edge2);
                Set<InstanceKey> intersectedValues = Util.deepCopySet(edge1Sink.getPossibleValues());
                intersectedValues.retainAll(edge2Sink.getPossibleValues());
                toAdd.add(new PointsToEdge(edge1.getSource(), SymbolicPointerVariable.makeSymbolicVar(intersectedValues)));// new
                                                                                                                           // SymbolicPointerVariable(intersectedValues)));
              } else {
                // intersection is empty; refuted
                if (Options.DEBUG)
                  Util.Debug("refuted by parameter binding! " + edge1 + " " + edge2);
                this.feasible = false;
                return formalsAssigned;
              }
            } else if (edge1Sink.isSymbolic()) {
              if (edge1Sink.getPossibleValues().contains(edge2Sink.getInstanceKey())) {
                toRemove.add(edge1); // constraint to concrete value;
              } else {
                // intersection is empty; refuted
                if (Options.DEBUG)
                  Util.Debug("refuted by parameter binding! " + edge1 + " " + edge2);
                this.feasible = false;
                return formalsAssigned;
              }
            } else { // edge2 sink is symbolic
              if (edge2Sink.getPossibleValues().contains(edge1Sink.getInstanceKey())) {
                toRemove.add(edge2); // constraint to concrete value;
              } else {
                // intersection is empty; refuted
                if (Options.DEBUG)
                  Util.Debug("refuted by parameter binding! " + edge1 + " " + edge2);
                this.feasible = false;
                return formalsAssigned;
              }
            }
          }
        }

        for (PointsToEdge edge : toRemove) {
          boolean removed = constraints.remove(edge);
          if (!removed)
            Util.Assert(removed, "couldn't remove edge " + edge + " from " + Util.printCollection(constraints));
        }
        for (PointsToEdge edge : toAdd)
          addConstraint(edge);
      }
    }

    return formalsAssigned;
  }

  /**
   * bind formals to actuals that appear in the LHS of our current constraints,
   * and add resulting constraint to produced set
   * 
   * @return - list of formals that we added new constraints for
   */
  Set<PointerVariable> bindFormalsToActuals(SSAInvokeInstruction instr, CGNode callerMethod, CGNode calleeMethod) {
    // TODO: optimization: the receiver of a constructor must have the same type
    // as the obj it's constructing. we can refute even earlier in this case
    // Util.Debug("before binding " + this);
    Util.Assert(!calleeMethod.equals(callerMethod), "recursion should be handled elsewhere");
    List<PointsToEdge> toAdd = new LinkedList<PointsToEdge>(), toRemove = new LinkedList<PointsToEdge>();
    if (instr.hasDef()) {
      // bind return value of method, if appropriate
      PointerVariable callerReturnValue = new ConcretePointerVariable(callerMethod, instr.getDef(),
          this.depRuleGenerator.getHeapModel());
      PointerVariable calleeReturnValue = Util.makeReturnValuePointer(calleeMethod, this.depRuleGenerator.getHeapModel());
      Util.Assert(calleeReturnValue.isLocalVar(), "make sure we're doing this right " + calleeReturnValue);

      for (PointsToEdge edge : constraints) {
        if (edge.getSource().equals(callerReturnValue)) {
          Util.Assert(edge.getField() == null, "expected " + edge + " to have local lhs");
          toAdd.add(new PointsToEdge(calleeReturnValue, edge.getSink()));
          toRemove.add(edge);
        }
      }
      for (PointsToEdge edge : toRemove)
        Util.Assert(constraints.remove(edge), "Couldn't remove edge " + edge + " from " + this);
      for (PointsToEdge edge : toAdd)
        Util.Assert(addConstraint(edge), "Couldn't add edge " + edge);
    }

    toRemove.clear();
    Util.Debug("binding formals to actuals: caller " + callerMethod + "; callee: " + calleeMethod);
    Set<PointerVariable> formalsAssigned = new HashSet<PointerVariable>();
    for (int i = 0; i < instr.getNumberOfParameters(); i++) {
      PointerVariable arg = new ConcretePointerVariable(callerMethod, instr.getUse(i), this.depRuleGenerator.getHeapModel());
      PointerVariable formal = new ConcretePointerVariable(calleeMethod, i + 1, this.depRuleGenerator.getHeapModel());
      for (PointsToEdge edge : constraints) {
        if (edge.getSource().equals(arg)) {
          // Util.Debug("binding " + formal + " to " + edge.getSink());
          PointsToEdge newEdge = new PointsToEdge(formal, edge.getSink());

          // DEBUG

          for (PointsToEdge prod : produced) {
            if (prod.getSource().equals(formal) && !prod.equals(newEdge)) {
              // multipe assignments to formal; let's see if ther consistent
              if (prod.getSink().isSymbolic() && !newEdge.getSink().isSymbolic()) {
                SymbolicPointerVariable sink = (SymbolicPointerVariable) prod.getSink();
                if (sink.getPossibleValues().contains(newEdge.getSink().getInstanceKey())) {
                  // new assignment is more precise; remove old one
                  toRemove.add(prod);
                } else
                  Util.Assert(
                      false,
                      "incompatible multiple assignments to " + formal + " edge " + newEdge + " produced "
                          + Util.constraintSetToString(produced));
              }
            }
            // Util.Assert(!prod.getSource().equals(formal) ||
            // prod.equals(newEdge),
            // "multiple assignments to " + formal + " edge " + newEdge +
            // " produced " + Util.constraintSetToString(produced));
          }

          for (PointsToEdge prod : constraints) {
            if (prod.getSource().equals(formal) && !prod.equals(newEdge)) {
              // multipe assignments to formal; let's see if ther consistent
              if (prod.getSink().isSymbolic() && !newEdge.getSink().isSymbolic()) {
                SymbolicPointerVariable sink = (SymbolicPointerVariable) prod.getSink();
                if (sink.getPossibleValues().contains(newEdge.getSink().getInstanceKey())) {
                  // new assignment is more precise; remove old one
                  toRemove.add(prod);
                } else
                  Util.Assert(
                      false,
                      "incompatible multiple assignments to " + formal + " edge " + newEdge + " produced "
                          + Util.constraintSetToString(constraints));
              }
            }
            // Util.Assert(!prod.getSource().equals(formal) ||
            // prod.equals(newEdge),
            // "multiple assignments to " + formal + " edge " + newEdge +
            // " produced " + Util.constraintSetToString(produced));
          }

          // END DEBUG
          for (PointsToEdge removeMe : toRemove)
            Util.Assert(produced.remove(removeMe), "couldn't remove edge " + removeMe);
          toRemove.clear();
          produced.add(newEdge);
          formalsAssigned.add(formal);
        }
      }
      toAdd.clear();
      for (PointsToEdge edge : produced) {
        if (edge.getSource().equals(arg)) {
          // Util.Debug("binding " + formal + " to " + edge.getSink());
          PointsToEdge newEdge = new PointsToEdge(formal, edge.getSink());
          // produced.add(newEdge);
          toAdd.add(newEdge);
          formalsAssigned.add(formal);
        }
      }

      produced.addAll(toAdd);
    }
    // constraints.removeAll(toRemove);
    return formalsAssigned;
  }

  @Override
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    return enterCall(instr, callee, currentPath, EMPTY_PV_VAR_SET);
  }

  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath, Set<PointerVariable> extraVars) {
    if (Options.GEN_DEPENDENCY_RULES_EAGERLY)
      depRuleGenerator.generateRulesForNode(callee);
    CGNode caller = currentPath.getCurrentNode(); // the call instruction occurs
                                                  // in the caller
    // need to do this even if there are no rules at the line because the return
    // value may be important (and is not represented in the dependency rules)
    Set<PointerVariable> formalsAlreadyAssigned = bindFormalsToActuals(instr, caller, callee);

    Util.Debug("PRODUCED " + Util.constraintSetToString(produced));

    Set<DependencyRule> rulesAtLine = depRuleGenerator.getRulesForInstr(instr, caller);
    if (rulesAtLine == null || rulesAtLine.isEmpty()) {
      Util.Debug("No rules at line...returning");
      return IQuery.FEASIBLE;
    }
    // Util.Assert(!rulesAtLine.isEmpty(),
    // "non-null list should always contain rules");
    // map from function parameter id's to list of dependency rules relevant to
    // that id
    Map<Integer, List<DependencyRule>> idRuleMap = new HashMap<Integer, List<DependencyRule>>(instr.getNumberOfParameters());
    // set of function parameters we have seen for which there is a relevant but
    // not consistent rule
    Set<Integer> inconsistentParams = new HashSet<Integer>();
    // set of function parameters for which there is a relevant and consistent
    // rule;
    Set<Integer> assignedParams = new HashSet<Integer>();

    for (DependencyRule rule : rulesAtLine) { // create map of rules to
                                              // parameters
      // Util.Assert(calleeMethod.getSignature().equals(
      // rule.getShown().getSource().getNode().getMethod().getSignature()),
      // "method signatures don't match! " +
      // instr.getCallSite().getDeclaredTarget().getSignature() + " and " +
      // rule.getShown().getSource().getNode().getMethod().getSignature());
      Util.Debug("trying rule for call " + rule);
      if (formalsAlreadyAssigned.contains(rule.getShown().getSource())) {
        Util.Debug("formal already assigned; continuing");
        continue; // this formal is already spoken for
      }
      if (isRuleRelevant(rule, currentPath, extraVars)) {
        int paramId = rule.getShown().getSource().hashCode();
        Set<DependencyRule> newRules = isRuleConsistent(rule, this, new TreeSet<DependencyRule>(), this.unsatCore,
            EMPTY_PT_EDGE_SET, null);
        if (newRules != null) {
          // if (isRuleConsistent(rule, this, caseSplits, new
          // TreeSet<DependencyRule>(), EMPTY_PT_EDGE_SET, null)) {
          List<DependencyRule> rulesForParam = idRuleMap.get(paramId);
          if (rulesForParam == null) {
            rulesForParam = new LinkedList<DependencyRule>();
            idRuleMap.put(paramId, rulesForParam);
          }
          rulesForParam.addAll(newRules);
          inconsistentParams.remove(paramId);
          assignedParams.add(paramId);
        } else if (!assignedParams.contains(paramId))
          inconsistentParams.add(paramId);
      }
    }

    if (!inconsistentParams.isEmpty()) {
      Util.Debug("Not all params can be assigned consistently, refuting");
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    unsatCore.clear();
    if (assignedParams.isEmpty()) {
      Util.Debug("Found no relevant rules for pts-to constraints...returning");
      return IQuery.FEASIBLE;
    }

    List<DependencyRule> applicableRules = new LinkedList<DependencyRule>();
    // see if there is more than one applicable rule for some parameter
    for (List<DependencyRule> rulesForParam : idRuleMap.values()) {
      if (rulesForParam.size() > 1) {
        if (idRuleMap.keySet().size() == 1) {
          // easy case; only one parameter. just add a choice for each
          for (DependencyRule rule : rulesForParam)
            applicableRules.add(rule);
          break;
        } // else, this is tricky. more than one parameter, and more than one
          // choice for one of them
        Util.Unimp("more than one rule for multiple parameters");
      } else if (rulesForParam.size() == 1)
        applicableRules.add(rulesForParam.get(0));
    }

    for (DependencyRule rule : applicableRules) { // apply each rule
      applyRule(rule, this);
    }
    return IQuery.FEASIBLE;
  }

  @Override
  public void enterCallFromJump(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    this.enterCall(instr, callee, currentPath);
  }

  static void applyRule(DependencyRule rule, PointsToQuery query) {
    // Util.Debug("applying rule " + rule + "\nto\n" + query);
    // Util.Pre(query.constraints.contains(rule.getShown()), "produced edge " +
    // rule.getShown() + " not in query! " + query);

    /*
     * if (shownLHS.isLocalVar()) { List<PointsToEdge> toRemove = new
     * LinkedList<PointsToEdge>(); // check for previous occurrences of this
     * variable and remove - we're doing a strong update for (PointsToEdge edge
     * : query.constraints) { if (edge.getSource().equals(shownLHS))
     * toRemove.add(edge); } for (PointsToEdge edge : toRemove)
     * query.constraints.remove(edge); }
     */

    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
    // special case for when the constraints contain a symbolic edge that
    // matches a concrete edge in the constraints
    for (PointsToEdge ruleEdge : rule.getToShow()) {
      if (ruleEdge.isSymbolic())
        continue;
      for (PointsToEdge edge : query.constraints) {
        if (edge.getSink().isSymbolic() && edge.getSource().equals(ruleEdge.getSource())) {
          if (edge.getSink().symbContains(ruleEdge.getSink())) {
            // remove the symbolic edge; it should be replaced with the concrete
            // one from this rule
            toRemove.add(edge);
          }
        }
      }
    }
    for (PointsToEdge removeMe : toRemove)
      query.constraints.remove(removeMe);

    boolean removed = query.constraints.remove(rule.getShown());
    // Util.Assert(removed, "couldn't remove edge " + rule.getShown() + " from "
    // + query);

    for (PointsToEdge edge : rule.getToShow()) {
      // don't want to re-add edges with local LHS's
      if (!edge.getSource().isLocalVar() || !query.produced.contains(edge))
        query.addConstraint(edge);
    }

    if (Options.LOG_WITNESSES) {
      query.witnessList.add(rule);
    }

    // only want to add constraints with local LHS to shown set because we can
    // produced refutations based on shown set...
    // ... it would be unsound to do this if we used constraints with heap LHS
    // (could be a different instance or strong update)
    if (rule.getShown().getSource().isLocalVar() && !WALACFGUtil.isInLoopBody(rule.getBlock(), rule.getNode().getIR())) {
      query.produced.add(rule.getShown());
    }

    // Util.Debug("after " + query);
  }

  /**
   * match symbolic variables in dependency rules with concrete/symbolic vars
   * already present in our constraints
   * 
   * @param rule
   * @param currentQuery
   * @param currentNode
   * @return
   */
  Set<DependencyRule> bindSymbolicRule(DependencyRule rule, PointsToQuery currentQuery, CGNode currentNode) {
    PointsToEdge shown = rule.getShown();
    Set<DependencyRule> rules = new TreeSet<DependencyRule>();
    List<Map<SymbolicPointerVariable, PointerVariable>> subMaps = new LinkedList<Map<SymbolicPointerVariable, PointerVariable>>();
    subMaps.add(new HashMap<SymbolicPointerVariable, PointerVariable>());
    // Map<SymbolicPointerVariable,PointerVariable> subMap = new
    // HashMap<SymbolicPointerVariable,PointerVariable>();
    Set<PointerVariable> alreadySubbed = new HashSet<PointerVariable>();

    List<PointsToEdge> ruleEdges = new LinkedList<PointsToEdge>();
    ruleEdges.add(shown);
    ruleEdges.addAll(rule.getToShow());

    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();

    // first, match edges with local LHS's and concrete RHS's. these are hard
    // constraints
    for (PointsToEdge edge : constraints) {
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && edge.getSource().isLocalVar() && !edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, true);
      }
    }
    for (PointsToEdge edge : produced) {
      Util.Assert(edge.getSource().isLocalVar(), "produced should only contain locals");
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && !edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, true);
      }
    }

    // now, match edges with local LHS's and symbolic sinks. these are not hard
    // constraints; there may be multiple choices
    for (PointsToEdge edge : constraints) {
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false);
      }
    }
    for (PointsToEdge edge : produced) {
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false);
      }
    }

    Util.Assert(subMaps.size() == 1, "more than one instantiation choice for shown! have " + subMaps.size()
        + " this shouldn't happen, since we've only considered local constraints");
    // DependencyRule newRule = rule;
    // if (subMaps.size() == 1) {
    Map<SymbolicPointerVariable, PointerVariable> singleMap = subMaps.iterator().next();
    alreadySubbed.addAll(singleMap.values());
    DependencyRule newRule = rule.substitute(singleMap);
    // }

    // now, do substitution for non-local edges
    for (PointsToEdge edge : constraints) {
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (!ruleEdge.getSource().isLocalVar() && !edge.getSource().isLocalVar())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false);
      }
    }

    for (Map<SymbolicPointerVariable, PointerVariable> map : subMaps) {
      rules.add(newRule.substitute(map));
    }

    Map<SymbolicPointerVariable, PointerVariable> aliasMap = new HashMap<SymbolicPointerVariable, PointerVariable>();

    List<DependencyRule> toAdd = new LinkedList<DependencyRule>();
    // also consider possible aliasing relationships
    for (DependencyRule symbRule : rules) {
      Set<SymbolicPointerVariable> symbVars = symbRule.getSymbolicVars();
      if (symbVars.size() > 1) { // more than 1 symbolic var; consider all
                                 // possible aliasing combos
        Util.Assert(symbVars.size() == 2, "more than 2 symbvars in " + symbRule);
        Iterator<SymbolicPointerVariable> iter = symbVars.iterator();
        SymbolicPointerVariable var0 = iter.next(), var1 = iter.next();
        // comparison issues mean we don't know whether var0/var1 is the
        // toSub/subFor var.
        // whichever var the old rule contains, that's the subFor variable
        if (rule.getSymbolicVars().contains(var0)) {
          if (Options.DEBUG)
            Util.Debug("considering aliasing of " + var0 + " and " + var1);
          aliasMap.put(var0, var1);
        } else {
          if (Options.DEBUG)
            Util.Debug("considering aliasing of " + var1 + " and " + var0);
          aliasMap.put(var1, var0);
        }

        toAdd.add(symbRule.substitute(aliasMap));
      }
      aliasMap.clear();
    }
    rules.addAll(toAdd);
    // Util.Debug("returning " + rules.size() + " rules.");
    return rules;
  }

  /*
   * Set<DependencyRule> bindSymbolicRule(DependencyRule rule, PointsToQuery
   * currentQuery, CGNode currentNode) { PointsToEdge shown = rule.getShown();
   * Set<DependencyRule> rules = new TreeSet<DependencyRule>();
   * List<Map<SymbolicPointerVariable,PointerVariable>> subMaps = new
   * LinkedList<Map<SymbolicPointerVariable,PointerVariable>>(); subMaps.add(new
   * HashMap<SymbolicPointerVariable,PointerVariable>());
   * //Map<SymbolicPointerVariable,PointerVariable> subMap = new
   * HashMap<SymbolicPointerVariable,PointerVariable>(); Set<PointerVariable>
   * alreadySubbed = new HashSet<PointerVariable>();
   * 
   * List<PointsToEdge> ruleEdges = new LinkedList<PointsToEdge>();
   * ruleEdges.add(shown); ruleEdges.addAll(rule.getToShow());
   * 
   * List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
   * 
   * // match edges with local LHS's first. since these can't have case splits,
   * they are hard constraints for (PointsToEdge edge : constraints) { for
   * (PointsToEdge ruleEdge : ruleEdges) { if (ruleEdge.getSource().isLocalVar()
   * && edge.getSource().isLocalVar()) ruleEdge.getSubsFromEdge(edge, subMaps,
   * alreadySubbed, true); } }
   * 
   * for (PointsToEdge edge : produced) {
   * Util.Assert(edge.getSource().isLocalVar(),
   * "produced should only contain locals"); for (PointsToEdge ruleEdge :
   * ruleEdges) { if (ruleEdge.getSource().isLocalVar())
   * ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, true); } }
   * Util.Assert(subMaps.size() == 1,
   * "more than one instantiation choice for shown! have " + subMaps.size() +
   * " this shouldn't happen, since we've only considered local constraints");
   * //DependencyRule newRule = rule; //if (subMaps.size() == 1) {
   * Map<SymbolicPointerVariable,PointerVariable> singleMap =
   * subMaps.iterator().next(); alreadySubbed.addAll(singleMap.values());
   * DependencyRule newRule = rule.substitute(singleMap); //}
   * 
   * // now, do substitution for non-local edges for (PointsToEdge edge :
   * constraints) { for (PointsToEdge ruleEdge : ruleEdges) { if
   * (!ruleEdge.getSource().isLocalVar() && !edge.getSource().isLocalVar())
   * ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false); } }
   * 
   * for (Map<SymbolicPointerVariable,PointerVariable> map : subMaps) {
   * rules.add(newRule.substitute(map)); }
   * 
   * Map<SymbolicPointerVariable,PointerVariable> aliasMap = new
   * HashMap<SymbolicPointerVariable, PointerVariable>();
   * 
   * List<DependencyRule> toAdd = new LinkedList<DependencyRule>(); // also
   * consider possible aliasing relationships for (DependencyRule symbRule :
   * rules) { Set<SymbolicPointerVariable> symbVars =
   * symbRule.getSymbolicVars(); if (symbVars.size() > 1) { // more than 1
   * symbolic var; consider all possible aliasing combos
   * Util.Assert(symbVars.size() == 2, "more than 2 symbvars in " + symbRule);
   * Iterator<SymbolicPointerVariable> iter = symbVars.iterator();
   * SymbolicPointerVariable var0 = iter.next(), var1 = iter.next(); //
   * comparison issues mean we don't know whether var0/var1 is the toSub/subFor
   * var. // whichever var the old rule contains, that's the subFor variable if
   * (rule.getSymbolicVars().contains(var0)) { if (Options.DEBUG)
   * Util.Debug("considering aliasing of " + var0 + " and " + var1);
   * aliasMap.put(var0, var1); } else { if (Options.DEBUG)
   * Util.Debug("considering aliasing of " + var1 + " and " + var0);
   * aliasMap.put(var1, var0); }
   * 
   * toAdd.add(symbRule.substitute(aliasMap)); } aliasMap.clear(); }
   * rules.addAll(toAdd); //Util.Debug("returning " + rules.size() + " rules.");
   * return rules; }
   */

  boolean isSymbolicRuleRelevant(DependencyRule rule, IPathInfo currentPath, Set<PointerVariable> extraVars) {
    PointsToEdge shown = rule.getShown();
    boolean shownSymbolic = shown.getSource().isSymbolic();
    for (PointsToEdge edge : constraints) {
      boolean lhsMatch;
      boolean fieldsEqual;
      if (shownSymbolic && edge.getSource().isSymbolic()) {
        lhsMatch = Util.intersectionNonEmpty(edge.getSource().getPossibleValues(), shown.getSource().getPossibleValues());
        fieldsEqual = Util.equal(edge.getFieldRef(), shown.getFieldRef());
      } else if (shownSymbolic) {
        lhsMatch = shown.getSource().getPossibleValues().contains(edge.getSource().getInstanceKey());
        fieldsEqual = Util.equal(edge.getFieldRef(), shown.getFieldRef());
      } else if (edge.getSource().isSymbolic()) {
        lhsMatch = edge.getSource().getPossibleValues().contains(shown.getSource().getInstanceKey());
        fieldsEqual = Util.equal(edge.getFieldRef(), shown.getFieldRef());
      } else {
        lhsMatch = edge.getSource().equals(shown.getSource()); // lhs's match
        fieldsEqual = Util.equal(edge.getField(), shown.getField()); // fields
                                                                     // match
      }

      if (lhsMatch && fieldsEqual) {
        if (Options.DEBUG)
          Util.Debug("relevant: " + edge);
        return true;
      }
    }
    return false;
  }

  DependencyRule isSymbolicRuleConsistent(DependencyRule rule, PointsToQuery currentQuery, Set<PointsToEdge> constraints,
      List<PointsToEdge> unsatCore, CGNode currentNode) {
    TreeSet<PointsToEdge> checkMe = new TreeSet<PointsToEdge>();
    PointsToEdge shown = rule.getShown();
    checkMe.addAll(rule.getToShow());
    checkMe.add(shown);

    // map from (symbolic pointer vars) -> (vars to sub, field)
    // Map<SymbolicPointerVariable,PointerVariable> subMap = new
    // HashMap<SymbolicPointerVariable,PointerVariable>();

    for (PointsToEdge constraint : constraints) {
      for (PointsToEdge edge : checkMe) {
        boolean lhsMatch;
        boolean fieldsEqualAndNotArrays;
        if (edge.getSource().isSymbolic() && constraint.getSource().isSymbolic()) { // both
                                                                                    // edges
                                                                                    // symbolic
          // lhsMatch =
          // Util.intersectionNonEmpty(edge.getSource().getPossibleValues(),
          // constraint.getSource().getPossibleValues());
          lhsMatch = edge.getSource() == constraint.getSource();
          fieldsEqualAndNotArrays = Util.equal(edge.getFieldRef(), constraint.getFieldRef())
              && (edge.getFieldRef() == null || !(edge.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS))
              && (constraint.getFieldRef() == null || !(constraint.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS));
          /*
           * if (lhsMatch && fieldsEqualAndNotArrays) { PointerVariable sub =
           * subMap.get(edge.getSource()); Util.Assert(sub == null ||
           * sub.equals(constraint.getSource()),
           * "more than one instantiation choice for " + edge.getSource() + ": "
           * + sub + " and " + constraint.getSource()); if (sub == null) {
           * Util.Debug("adding sub relationship " + edge.getSource() + " " +
           * constraint.getSource()); subMap.put((SymbolicPointerVariable)
           * edge.getSource(), constraint.getSource()); } }
           */
        } else if (edge.getSource().isSymbolic()) { // rule edge symbolic,
                                                    // constraint edge concrete
          lhsMatch = edge.getSource().getPossibleValues().contains(constraint.getSource().getInstanceKey());
          fieldsEqualAndNotArrays = Util.equal(edge.getFieldRef(), constraint.getFieldRef())
              && (edge.getFieldRef() == null || !(edge.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS))
              && (constraint.getField() == null || !(constraint.getField() instanceof ArrayContentsKey));
          /*
           * if (lhsMatch && fieldsEqualAndNotArrays) { PointerVariable sub =
           * subMap.get(edge.getSource()); Util.Assert(sub == null ||
           * sub.equals(constraint.getSource()),
           * "more than one instantiation choice " + sub + " " +
           * constraint.getSource()); if (sub == null) {
           * subMap.put((SymbolicPointerVariable) edge.getSource(),
           * constraint.getSource()); } }
           */
        } else if (constraint.getSource().isSymbolic()) { // constraint edge
                                                          // symbolic, rule edge
                                                          // concrete
          lhsMatch = constraint.getSource().getPossibleValues().contains(edge.getSource().getInstanceKey());
          fieldsEqualAndNotArrays = Util.equal(edge.getFieldRef(), constraint.getFieldRef())
              && (constraint.getFieldRef() == null || !(constraint.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS))
              && (edge.getField() == null || !(edge.getField() instanceof ArrayContentsKey));
        } else { // neither symbolic
          lhsMatch = edge.getSource().equals(constraint.getSource());
          fieldsEqualAndNotArrays = Util.equal(constraint.getField(), edge.getField())
              && (constraint.getField() == null || !(constraint.getField() instanceof ArrayContentsKey))
              && (edge.getField() == null || !(edge.getField() instanceof ArrayContentsKey));
        }

        if (lhsMatch && fieldsEqualAndNotArrays) {
          boolean rhsEq;
          if (edge.getSink().isSymbolic() && constraint.getSink().isSymbolic()) {
            // rhsEq =
            // Util.intersectionNonEmpty(edge.getSink().getPossibleValues(),
            // constraint.getSink().getPossibleValues());
            rhsEq = edge.getSink() == constraint.getSink();
            /*
             * PointerVariable sub = subMap.get(edge.getSink()); Util.Assert(sub
             * == null || sub.equals(constraint.getSink()),
             * "more than one instantiation choice " + sub + " " +
             * constraint.getSink()); if (sub == null) {
             * Util.Debug("adding sub relationship " + edge.getSink() + " " +
             * constraint.getSink()); subMap.put((SymbolicPointerVariable)
             * edge.getSink(), constraint.getSink()); }
             */
          } else if (edge.getSink().isSymbolic()) {
            rhsEq = edge.getSink().getPossibleValues().contains(constraint.getSink().getInstanceKey());
            /*
             * PointerVariable sub = subMap.get(edge.getSink()); Util.Assert(sub
             * == null || sub.equals(constraint.getSink()),
             * "more than one instantiation choice " + sub + " " +
             * constraint.getSink()); if (sub == null) {
             * subMap.put((SymbolicPointerVariable) edge.getSink(),
             * constraint.getSink()); }
             */
          } else if (constraint.getSink().isSymbolic()) {
            rhsEq = constraint.getSink().getPossibleValues().contains(edge.getSink().getInstanceKey());
          } else {
            rhsEq = constraint.getSink().equals(edge.getSink());
          }
          if (!rhsEq) {
            if (Options.DEBUG)
              Util.Debug("refuted: " + edge + " and " + constraint);
            unsatCore.add(constraint);
            return null;
          }
        }
      }
    }
    // sub out symbolic values for concrete ones
    // return rule.substitute(subMap);
    return rule;
  }

  boolean isRuleRelevant(DependencyRule rule, IPathInfo currentPath, Set<PointerVariable> extraVars) {
    if (rule.isSymbolic())
      return isSymbolicRuleRelevant(rule, currentPath, extraVars);
    TreeSet<PointsToEdge> checkMe = new TreeSet<PointsToEdge>();
    checkMe.add(rule.getShown());

    for (PointsToEdge edge : constraints) {
      for (PointsToEdge toCheck : checkMe) {
        boolean match = edge.getSource().equals(toCheck.getSource()) && // lhs's
                                                                        // match
            Util.equal(edge.getField(), toCheck.getField()); // fields match
        if (match) {
          if (Options.DEBUG)
            Util.Debug("relevant: " + edge);
          return true;
        }
      }
    }
    checkMe.addAll(rule.getToShow());

    // also possible that it matches / contradicts a constraint we already have
    // in produced
    for (PointsToEdge edge : produced) {
      Util.Assert(edge.getSource().isLocalVar(), "only constraints with local LHS should be in produced set!");
      for (PointsToEdge toCheck : checkMe) {
        if (toCheck.getSource().isLocalVar() && // for produced, can only
                                                // refuted based on locals...
                                                // heap locs can be mutated
            edge.getSource().equals(toCheck.getSource()) && // lhs's match
            Util.equal(edge.getField(), toCheck.getField()) && // fields match
            !edge.getSink().equals(toCheck.getSink())) { // rhs' do NOT match

          if (!WALACFGUtil.isInLoopBody(currentPath.getCurrentBlock(), currentPath.getCurrentNode().getIR())) {
            // multiple assignments are ok if var occurs in a loop
            if (Options.DEBUG)
              Util.Debug("relevant (produced): " + edge);
            return true;
          } // else, this assignment is in a loop, where multiple assigns can
            // occur. not relevant to us
        }
      }
    }

    /*
     * // check for relevance to extra vars for (PointsToEdge edge : checkMe) {
     * if (extraVars.contains(edge.getSource())) { if (Options.DEBUG)
     * Util.Debug("relevant (extra) " + edge); return true; } }
     */

    return false;
  }

  /*
   * boolean isRuleConsistent(DependencyRule rule, PointsToQuery currentQuery,
   * List<IQuery> caseSplits, Set<DependencyRule> irrelevantRules,
   * Set<PointsToEdge> refuted, CGNode currentNode) { // must be consistent both
   * with current constraints and constraints we have already produced //if
   * (!isRuleConsistent(rule, currentQuery, caseSplits, this.constraints,
   * irrelevantRules, refuted, currentNode)) return false; //return
   * isRuleConsistent(rule, currentQuery, caseSplits, this.produced,
   * irrelevantRules, refuted, currentNode); if (!isSymbolicRuleConsistent(rule,
   * currentQuery, this.constraints, currentNode)) return false; return
   * isSymbolicRuleConsistent(rule, currentQuery, this.produced, currentNode); }
   */

  Set<DependencyRule> isRuleConsistent(DependencyRule rule, PointsToQuery currentQuery, Set<DependencyRule> irrelevantRules,
      List<PointsToEdge> unsatCore, Set<PointsToEdge> refuted, CGNode currentNode) {
    // if (rule.isSymbolic()) {
    if (Options.ABSTRACT_DEPENDENCY_RULES) {
      if (rule.isSymbolic()) {
        Set<DependencyRule> newRules = bindSymbolicRule(rule, currentQuery, currentNode);
        Util.Assert(!newRules.isEmpty(), "should not be empty here!");
        List<DependencyRule> toRemove = new LinkedList<DependencyRule>();
        for (DependencyRule newRule : newRules) {
          if (isSymbolicRuleConsistent(newRule, currentQuery, this.constraints, unsatCore, currentNode) == null) {
            // DependencyRule newRule = isSymbolicRuleConsistent(rule,
            // currentQuery, this.constraints, currentNode);
            toRemove.add(newRule);
            continue;
          }
          // if (isSymbolicRuleConsistent(rule, currentQuery, this.produced,
          // currentNode) == null) return null;
          if (isSymbolicRuleConsistent(newRule, currentQuery, this.produced, unsatCore, currentNode) == null) {
            toRemove.add(newRule);
            continue;
          }
        }
        newRules.removeAll(toRemove);
        if (newRules.isEmpty())
          return null;
        return newRules;
      } else if (rule.getStmt() != null && rule.getStmt().isNewInstr()) { // this
                                                                          // is
                                                                          // a
                                                                          // new
                                                                          // instruction.
                                                                          // bind
                                                                          // it
        PointsToEdge shown = rule.getShown();
        Set<DependencyRule> singleton = new TreeSet<DependencyRule>();
        for (PointsToEdge edge : this.constraints) {
          if (edge.getSource().equals(shown.getSource())) {
            if (edge.getSink().isSymbolic()) {
              DependencyRule newRule = new DependencyRule(edge, rule.getStmt(), rule.getToShow(), rule.getNode(), rule.getBlock());
              // Util.Debug("replacing with " + newRule);
              singleton.add(newRule);
              return singleton;
            } else {
              if (edge.getSink().equals(shown.getSink())) {
                singleton.add(rule);
                return singleton;
              } else
                return null;
            }
          }
        }
        // Util.Unimp("shouldn't get here for rule " + rule + " query " +
        // currentQuery);
        singleton.add(rule);
        return singleton;
      } else
        return doConsistencyCheckNonSymbolic(rule, currentQuery, irrelevantRules, unsatCore, refuted, currentNode);
    } else {
      return doConsistencyCheckNonSymbolic(rule, currentQuery, irrelevantRules, unsatCore, refuted, currentNode);
    }
  }

  private Set<DependencyRule> doConsistencyCheckNonSymbolic(DependencyRule rule, PointsToQuery currentQuery,
      Set<DependencyRule> irrelevantRules, List<PointsToEdge> unsatCore, Set<PointsToEdge> refuted, CGNode currentNode) {
    if (!isRuleConsistent(rule, currentQuery, this.constraints, unsatCore, irrelevantRules, refuted, currentNode))
      return null;
    if (isRuleConsistent(rule, currentQuery, this.produced, unsatCore, irrelevantRules, refuted, currentNode)) {
      Set<DependencyRule> singleton = new TreeSet<DependencyRule>();
      singleton.add(rule);
      return singleton;
    } else
      return null;
  }

  static boolean isRuleConsistent(DependencyRule rule, PointsToQuery currentQuery, Set<PointsToEdge> constraints,
      List<PointsToEdge> unsatCore, Set<DependencyRule> irrelevantRules, Set<PointsToEdge> refuted, CGNode currentNode) {
    TreeSet<PointsToEdge> checkMe = new TreeSet<PointsToEdge>();
    PointsToEdge shown = rule.getShown();
    checkMe.addAll(rule.getToShow());
    checkMe.add(shown);

    /*
     * for (PointsToEdge edge : refuted) { if (checkMe.contains(edge)){
     * Util.Unimp("refuting based on this"); Util.Debug("edge " + edge +
     * " aready refuted!"); return false; } }
     */

    for (PointsToEdge constraint : constraints) {
      for (PointsToEdge edge : checkMe) {
        // to check: lhs's equal and (fieldnames equal and not array's) => rhs's
        // equal
        boolean lhsNameMatch = edge.getSource().equals(constraint.getSource());
        boolean fieldsEqualAndNotArrays = Util.equal(constraint.getField(), edge.getField())
            && (constraint.getField() == null || !(constraint.getField() instanceof ArrayContentsKey))
            && (edge.getField() == null || !(edge.getField() instanceof ArrayContentsKey));
        boolean rhsesEqual = constraint.getSink().equals(edge.getSink());

        if (lhsNameMatch && fieldsEqualAndNotArrays && !rhsesEqual) {
          PointerVariable constraintSrc = constraint.getSource();
          // is LHS a local or heap loc?
          if (constraintSrc.isLocalVar()) { // can't split a local into multiple
                                            // instances...
            if (WALACFGUtil.isInLoopBody(rule.getBlock(), rule.getNode().getIR())) { // ...unless
                                                                                     // it
                                                                                     // occurs
                                                                                     // in
                                                                                     // a
                                                                                     // loop
              // if (Util.isEdgeProduceableByLoop(edge, rule.getNode(),
              // currentQuery.depRuleGenerator.getHeapGraph(),
              // currentQuery.depRuleGenerator,
              // currentQuery.depRuleGenerator.getCallGraph())) {
              // (implicitly) allow both locals to be added; a strong update
              // will be enforced when the rule is applied
              // continue;
              // Util.Log("local refuted: " + edge + " and " + constraint);
              // return false;
            } else {
              // locals are not in a loop. we have a definite refutation, since
              // no local can point to two values at once
              Util.Debug("refuted: " + edge + " and " + constraint);
              unsatCore.add(constraint);
              return false;
            }
          }
          // else, LHS is a heap loc. we can't definitely refute, since they may
          // be different instances of the same abstract location
          // Set<Integer> instanceNums = collectInstanceNumsFor(constraintSrc,
          // constraints);
          // Util.Assert(instanceNums.size() == 1,
          // "more than one instance num? this is unexpected...");
          // TODO: no longer need this case...I think case splits for phi's
          // suffice to handle this
          // if there's only one instance num for the var in question, then it
          // suffices to consider two cases: one where the rule is applied,
          // and one where it is not. otherwise, we must do a case split for
          // each instance number...
          // if (caseSplits.isEmpty()) caseSplits.add(currentPath.deepCopy());
          // // a single "rule not applied" case suffices
          Util.Debug("refuted: " + edge + " and " + constraint);
          unsatCore.add(constraint);
          return false; // ok to label as inconsistent; only the rule not taken
                        // path (already accounted for) is consistent
        }
      }
    }
    /*
     * if (currentNode == null) return true; if
     * (rule.getShown().getSource().isLocalVar())
     * Util.Assert(rule.getShown().getSource().getNode().equals(currentNode),
     * "nodes don't match: cur " + currentNode + " and rule " +
     * rule.getShown().getSource().getNode() + "\nfor rule  " + rule); for
     * (PointsToEdge edge : rule.getToShow()) { if
     * (edge.getSource().isLocalVar())
     * Util.Assert(edge.getSource().getNode().equals(currentNode),
     * "nodes don't match: cur " + currentNode + " and rule " +
     * edge.getSource().getNode() + "\nfor rule " + rule); }
     */
    // Util.Post(caseSplits.isEmpty(),
    // "this is not handled correctly in all callers; they expect it to be empty. fix this");
    return true;
  }

  /**
   * @return - all distinct instance nums that var has in our constraint set
   */
  /*
   * static Set<Integer> collectInstanceNumsFor(PointerVariable var,
   * Set<PointsToEdge> constraints) { Util.Assert(var.isHeapVar(),
   * "Only heap vars can have instance num!"); Set<Integer> instanceNumSet = new
   * HashSet<Integer>();
   * 
   * for (PointsToEdge constraint : constraints) { PointerVariable src =
   * constraint.getSource(), snk = constraint.getSink(); if (var.equals(src)) {
   * instanceNumSet.add(src.getInstanceNum()); }
   * 
   * if (var.equals(snk)) { instanceNumSet.add(snk.getInstanceNum()); } } return
   * instanceNumSet; }
   */

  /**
   * find the var pointed to by the given var in our consraints
   * 
   * @param var
   *          - variable to look for on LHS of points-to relation
   * @return return the location pointed to by var, or null if var is not found
   *         on the LHS of any constraint in the set
   */
  PointerVariable getPointedTo(PointerVariable var) {
    PointerVariable pointed = getPointedTo(var, constraints);
    if (pointed != null)
      return pointed;
    return getPointedTo(var, produced);
  }

  /**
   * if we have var -> loc@1 in our set, this method will return loc@1.
   * 
   * @param var
   *          - variable to look for on LHS of points-to relation
   * @param set
   *          - set of edges to search in
   * @return return the location pointed to by var, or null if var is not found
   *         on the LHS of any constraint in the set
   */
  private static PointerVariable getPointedTo(PointerVariable var, Set<PointsToEdge> set) {
    PointerVariable found = null;
    for (PointsToEdge edge : set) {
      if (edge.getSource().equals(var)) {
        Util.Assert(found == null, "should only find var on LHS of one points-to relation!");
        found = edge.getSink();
      }
    }
    return found;
  }

  // branch conditions are always over locals, so there's nothing to do here
  @Override
  public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranchFeasible) {
    return true;
  }

  // do nothing
  @Override
  public void declareFakeWitness() {
  }

  @Override
  public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) {
    if (instr.hasDef()) {
      ConcretePointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      for (PointsToEdge edge : this.constraints) {
        if (edge.getSource().equals(retval)) {
          if (Options.DEBUG)
            Util.Debug("retval relevant: " + edge + "\nand\n" + retval);
          return true; // relevant due to the return value
        }
      }
    }

    // boolean relevant = false;

    /*
     * // collect all dependency rules produceable by this call
     * Set<DependencyRule> rulesProducedByCallee =
     * Util.getRulesProducableByCall(callee, cg, depRuleGenerator); for
     * (DependencyRule rule : rulesProducedByCallee) { PointerVariable shownLHS
     * = rule.getShown().getSource(); for (PointsToEdge edge : this.constraints)
     * { if (edge.getSource().equals(shownLHS)) { Util.Debug("relevant: " + edge
     * + "\nand\n" + rule.getShown()); return true; //relevant = true; //break;
     * } } }
     */

    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (PointsToEdge edge : constraints) {
      PointerKey key = edge.getField();
      if (key != null && keys.contains(key)) {
        // Util.Assert(relevant,
        // "mod/ref and dep rules disagree on relevance of " + edge);
        return true;
      }
    }

    return false;
  }

  @Override
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    Set<PointsToEdge> toRemove = new TreeSet<PointsToEdge>();

    if (instr.hasDef()) {
      ConcretePointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      for (PointsToEdge edge : this.constraints) {
        if (edge.getSource().equals(retval))
          toRemove.add(edge);
      }
    }

    /*
     * // collect all dependency rules produceable by this call
     * Set<DependencyRule> rulesProducedByCallee =
     * Util.getRulesProducableByCall(callee, depRuleGenerator.getCallGraph(),
     * depRuleGenerator); for (PointsToEdge edge : this.constraints) {
     * PointerVariable src = edge.getSource(); if (retval != null &&
     * src.equals(retval)) { toRemove.add(edge); continue; } for (DependencyRule
     * rule : rulesProducedByCallee) { PointerVariable shownLHS =
     * rule.getShown().getSource(); if (src.equals(shownLHS))
     * toRemove.add(edge); } }
     */

    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (PointsToEdge edge : constraints) {
      PointerKey key = edge.getField();
      if (key != null && keys.contains(key))
        toRemove.add(edge);
    }

    for (PointsToEdge edge : toRemove) {
      Util.Debug("dropping " + edge);
      this.constraints.remove(edge);
    }
  }

  @Override
  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    Set<DependencyRule> loopRules = new TreeSet<DependencyRule>();
    Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(currentNode); // get
                                                                               // all
                                                                               // rules
                                                                               // for
                                                                               // node
    for (DependencyRule rule : rules) { // keep only rules produced in loop
      Util.Assert(rule.getBlock() != null, "no basic block for rule " + rule);
      if (WALACFGUtil.isInLoopBody(rule.getBlock(), loopHead, currentNode.getIR())) {
        loopRules.add(rule);
      }
    }
    for (DependencyRule rule : loopRules) { // see if any of the rules produces
                                            // one of our edges
      if (this.constraints.contains(rule.getShown()))
        return true;

      else {
        for (PointsToEdge constraint : constraints) {
          if (constraint.symbEq(rule.getShown()))
            return true;
        }
      }
    }

    // the loop may also contain callees. see if those callees can write to vars
    // in our constraints
    Set<CGNode> targets = WALACFGUtil.getCallTargetsInLoop(loopHead, currentNode, depRuleGenerator.getCallGraph());
    for (CGNode callNode : targets) { // drop all vars that can be written by a
                                      // call in the loop body
      OrdinalSet<PointerKey> callKeys = depRuleGenerator.getModRef().get(callNode);
      for (PointsToEdge edge : constraints) {
        PointerKey key = edge.getField();
        if (key != null && callKeys.contains(key))
          return true;
      }
    }
    /*
     * for (PointsToEdge edge : this.constraints) { if
     * (edge.getSource().isLocalVar() && Util.isEdgeProduceableByLoop(edge,
     * loopHead, currentNode, depRuleGenerator.getHeapGraph(), depRuleGenerator,
     * depRuleGenerator.getCallGraph())) { Util.Debug("produceable: " + edge);
     * return true; } }
     */
    return false;
  }

  @Override
  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    if (this.constraints.isEmpty())
      return;
    Set<DependencyRule> loopRules = new TreeSet<DependencyRule>();
    Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(currentNode); // get
                                                                               // all
                                                                               // rules
                                                                               // for
                                                                               // node
    if (rules != null) {
      for (DependencyRule rule : rules) { // keep only rules produced in loop
        // Util.Debug("rule shown " + rule.getShown());
        Util.Assert(rule.getBlock() != null, "no basic block for rule " + rule);
        if (WALACFGUtil.isInLoopBody(rule.getBlock(), loopHead, currentNode.getIR())) {
          loopRules.add(rule);
        }
      }
    }

    List<PointsToEdge> toDrop = new LinkedList<PointsToEdge>();
    for (DependencyRule rule : loopRules) {
      for (PointsToEdge edge : this.constraints) {
        if (rule.getShown().equals(edge) || rule.getShown().symbEq(edge)) {
          toDrop.add(edge);
        }
      }
    }

    for (PointsToEdge edge : toDrop)
      this.constraints.remove(edge);
    toDrop.clear();

    // the loop may also contain callees. drop any constraint containing vars
    // that these callees can write to
    Set<CGNode> targets = WALACFGUtil.getCallTargetsInLoop(loopHead, currentNode, depRuleGenerator.getCallGraph());

    for (CGNode callNode : targets) { // drop all edges that can be written by a
                                      // call in the loop body
      OrdinalSet<PointerKey> callKeys = depRuleGenerator.getModRef().get(callNode);
      for (PointsToEdge edge : this.constraints) {
        if (edge.getField() != null && callKeys.contains(edge.getField()))
          toDrop.add(edge);
      }
      for (PointsToEdge edge : toDrop)
        this.constraints.remove(edge);
      toDrop.clear();
    }
  }

  /**
   * this contains other if it contains all of other's points-to edges
   */
  @Override
  public boolean contains(IQuery other) {
    if (!(other instanceof PointsToQuery))
      return false;
    PointsToQuery otherQuery = (PointsToQuery) other;

    if (otherQuery.constraints.isEmpty())
      return true;
    // can't contain the other query if it's bigger than us
    if (otherQuery.constraints.size() > this.constraints.size())
      return false;

    // Util.Debug("asking if " + this.constraints + " contains " +
    // otherQuery.constraints);

    for (PointsToEdge constraint1 : otherQuery.constraints) { // for each
                                                              // constraint in
                                                              // other
      boolean contained = false;
      for (PointsToEdge constraint2 : this.constraints) { // for each constraint
                                                          // in this
        // Util.Debug("eq " + constraint1 + " and " + constraint2);
        if (constraint2.symbContains(constraint1)) { // if this contains the
                                                     // constraint from other
          // if (constraint1.symbEq(constraint2)) {
          // Util.Debug("true");
          contained = true;
          break;
        }
      }
      if (!contained) {
        return false;
      }
    }

    // Util.Debug("contains query " + other + "?" + contains);
    return true;
  }

  /*
   * @Override public int compareTo(Object other) { if (!(other instanceof
   * PointsToQuery)) Util.Unimp("comparing to non- points-to query " +
   * other.getClass() + " " + other); PointsToQuery otherQuery = (PointsToQuery)
   * other; TreeSet<PointsToEdge> otherConstraints = otherQuery.constraints;
   * final int ptSize = constraints.size(), otherPtSize =
   * otherConstraints.size(); if (ptSize > otherPtSize) return 1; else if
   * (ptSize < otherPtSize) return -1; // sizes are the same
   * 
   * // sizes are the same; do edge-by-edge comparison final
   * Iterator<PointsToEdge> ptIter = constraints.descendingIterator(); final
   * Iterator<PointsToEdge> otherPtIter = otherConstraints.descendingIterator();
   * while (ptIter.hasNext() && otherPtIter.hasNext()) { final PointsToEdge
   * edge0 = ptIter.next(); final PointsToEdge edge1 = otherPtIter.next(); final
   * int comparison = edge0.compareTo(edge1); if (comparison != 0) return
   * comparison; } return 0; // all edges compared equal }
   */

  @Override
  public void removeAllLocalConstraints() {
    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
    for (PointsToEdge edge : constraints) {
      if (edge.getSource().isLocalVar())
        toRemove.add(edge);
    }
    for (PointsToEdge edge : toRemove)
      constraints.remove(edge);
  }

  @Override
  public Map<Constraint, Set<CGNode>> getModifiersForQuery() {
    // public Set<CGNode> getMethodsRelevantToQuery() {
    Map<Constraint, Set<CGNode>> constraintModMap = new HashMap<Constraint, Set<CGNode>>();
    for (PointsToEdge edge : constraints) {
      Set<DependencyRule> producingRules = new HashSet<DependencyRule>();
      Set<CGNode> producers = new HashSet<CGNode>();
      if (edge.isSymbolic()) {
        if (edge.getSink().isSymbolic() && edge.getSource().isSymbolic()) {
          SymbolicPointerVariable src = (SymbolicPointerVariable) edge.getSource();
          SymbolicPointerVariable snk = (SymbolicPointerVariable) edge.getSink();
          for (InstanceKey srcKey : src.getPossibleValues()) {
            for (InstanceKey snkKey : snk.getPossibleValues()) {
              ConcretePointerVariable srcVar = new ConcretePointerVariable(srcKey, Util.getNodeForInstanceKey(srcKey));
              ConcretePointerVariable snkVar = new ConcretePointerVariable(snkKey, Util.getNodeForInstanceKey(snkKey));
              PointsToEdge concreteEdge = new PointsToEdge(srcVar, snkVar, edge.getFieldRef());
              producingRules.addAll(Util.getProducersForEdge(concreteEdge, depRuleGenerator));
            }
          }
        } else if (edge.getSource().isSymbolic()) {
          SymbolicPointerVariable symb = (SymbolicPointerVariable) edge.getSource();
          for (InstanceKey key : symb.getPossibleValues()) {
            ConcretePointerVariable conc = new ConcretePointerVariable(key, Util.getNodeForInstanceKey(key));
            PointsToEdge concreteEdge = new PointsToEdge(conc, edge.getSink(), edge.getFieldRef());
            producingRules.addAll(Util.getProducersForEdge(concreteEdge, depRuleGenerator));
          }
        } else if (edge.getSink().isSymbolic()) {
          SymbolicPointerVariable symb = (SymbolicPointerVariable) edge.getSink();
          for (InstanceKey key : symb.getPossibleValues()) {
            ConcretePointerVariable conc = new ConcretePointerVariable(key, Util.getNodeForInstanceKey(key));
            PointsToEdge concreteEdge = new PointsToEdge(edge.getSource(), conc, edge.getFieldRef());
            producingRules.addAll(Util.getProducersForEdge(concreteEdge, depRuleGenerator));
          }
        } else
          Assertions.UNREACHABLE();
      } else
        producingRules.addAll(Util.getProducersForEdge(edge, depRuleGenerator));
      // Set<DependencyRule> producingRules = Util.getProducersForEdge(edge,
      // depRuleGenerator);
      // TODO: this means edge is definitely infeasible, and thus so are
      // constraints... should do something about this
      // Util.Assert(!producingRules.isEmpty(),
      // "couldn't find producer for edge " + edge);
      for (DependencyRule rule : producingRules) {
        producers.add(rule.getNode());
      }
      constraintModMap.put(edge, producers);
    }
    return constraintModMap;
  }

  @Override
  public void intializeStaticFieldsToDefaultValues() {
    for (PointsToEdge edge : this.constraints) {
      // if a constraint required a static field to point to something, that
      // constraint will never be satisfied. refute.
      if (edge.getSource().getInstanceKey() instanceof StaticFieldKey) {
        if (Options.DEBUG)
          Util.Debug("refuted by default values for static fields!");
        this.feasible = false;
        return;
      }
    }
  }

  @Override
  public boolean addContextualConstraints(CGNode node, IPathInfo currentPath) {
    // TODO: for now, we only need to make receiver constraints explicit. we may
    // have a need for others in the future as well...
    Context context = node.getContext();
    ContextItem receiver = context.get(ContextKey.RECEIVER);
    if (receiver instanceof InstanceKey) {
      InstanceKey receiverKey = (InstanceKey) receiver;
      PointerVariable site = Util.makePointerVariable(receiverKey);
      final int RECEIVER_VALUE_NUM = 1; // receiver is always v1
      PointerVariable receiverLocal = new ConcretePointerVariable(node, RECEIVER_VALUE_NUM, this.depRuleGenerator.getHeapModel());
      PointsToEdge receiverConstraint = new PointsToEdge(receiverLocal, site);
      if (Options.DEBUG)
        Util.Debug("adding receiver constraint " + receiverConstraint);
      // create trivial dependency rule
      DependencyRule rule = new DependencyRule(receiverConstraint, null, new TreeSet<PointsToEdge>(), node, node.getIR()
          .getControlFlowGraph().entry());
      Set<DependencyRule> newRules = isRuleConsistent(rule, this, new TreeSet<DependencyRule>(), unsatCore, EMPTY_PT_EDGE_SET,
          currentPath.getCurrentNode());
      if (newRules != null) { // && !produced.contains(receiverConstraint)) {
        if (!produced.contains(receiverConstraint))
          this.addConstraint(receiverConstraint);
      } else { // refuted!
        if (Options.DEBUG)
          Util.Debug("refuted by contextual constraints. newRules " + newRules);
        return false;
      }
    }
    /*
     * ContextItem caller = context.get(ContextKey.CALLER); if (caller
     * instanceof CGNode) {
     * 
     * }
     */

    return true;
  }

  private boolean addConstraint(PointsToEdge constraint) {
    // DEBUG
    if (constraint.getSource().isLocalVar()) {
      ConcretePointerVariable lhs = (ConcretePointerVariable) constraint.getSource();
      for (PointsToEdge edge : this.constraints) {
        Util.Assert(!lhs.equals(edge.getSource()) || edge.equals(constraint), "constraints already contain " + edge + "\nadding "
            + constraint);
      }
    }
    return constraints.add(constraint);
  }

  /**
   * perform non-destructive set differencing between start constraints and this
   * (i.e. do startConstraints \ this)
   */
  // @Override
  public PointsToQuery nonDestructiveDifference(PointsToQuery startConstraints) {
    PointsToQuery copy = startConstraints.deepCopy();
    // copy.r
    // copy.constraints.removeAll(c)

    copy.intersect(startConstraints);
    Util.Unimp("non-destructive difference");
    return null;
  }

  public List<DependencyRule> getWitnessList() {
    return witnessList;
  }

  @Override
  public boolean containsConstraint(Constraint constraint) {
    if (!(constraint instanceof PointsToEdge))
      return false;
    return this.constraints.contains(constraint);
  }

  /*
   * @Override public boolean equals(Object other) { if (!(other instanceof
   * PointsToQuery)) return false; PointsToQuery otherQuery = (PointsToQuery)
   * other; return constraints.equals(otherQuery.constraints); }
   * 
   * 
   * @Override public int hashCode() { Util.Unimp("Don't hash this query");
   * return -1; }
   */

  @Override
  public String toString() {
    return Util.constraintSetToString(constraints);
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((constraints == null) ? 0 : constraints.hashCode());
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    PointsToQuery other = (PointsToQuery) obj;
    if (constraints == null) {
      if (other.constraints != null)
        return false;
    } else if (!constraints.equals(other.constraints))
      return false;
    return true;
  }

}

package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.Context;
import com.ibm.wala.ipa.callgraph.ContextItem;
import com.ibm.wala.ipa.callgraph.ContextKey;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAGetCaughtExceptionInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
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

  final AbstractDependencyRuleGenerator depRuleGenerator;
  // constraints that have not been produced yet
  final Set<PointsToEdge> constraints; 
  // constraints with that have already been produced and have not been invalidated 
  final Set<PointsToEdge> produced;
  // the constraints produced, in the order they were produced
  final List<DependencyRule> witnessList;
  final List<PointsToEdge> unsatCore = new ArrayList<PointsToEdge>();

  private boolean feasible = true; // this is just a sanity check to make sure
                                   // that refuted queries are not re-used

  // public PointsToQuery(Set<PointsToEdge> startConstraints, PointsToEdge
  // producedEdge, AbstractDependencyRuleGenerator depRuleGenerator) {
  public PointsToQuery(DependencyRule startRule, AbstractDependencyRuleGenerator depRuleGenerator) {
    // create a tree set out of the input set; typically, the input set is
    // immutable (comes from toShow set of a dep rule), so we cannot use it as
    // our constraint set
    // this.constraints = new TreeSet<PointsToEdge>();
    this.constraints = HashSetFactory.make();//new HashSet<PointsToEdge>();
    constraints.addAll(startRule.getToShow());
    this.depRuleGenerator = depRuleGenerator;
    this.produced = HashSetFactory.make(); //new HashSet<PointsToEdge>();
    PointsToEdge producedEdge = startRule.getShown();
    //if (producedEdge.getSource().isLocalVar())
    this.produced.add(producedEdge);
    this.witnessList = new LinkedList<DependencyRule>();
    this.witnessList.add(startRule);
  }

  public PointsToQuery(PointsToEdge startEdge, AbstractDependencyRuleGenerator depRuleGenerator) {
    // this.constraints = new TreeSet<PointsToEdge>();
    this.constraints = HashSetFactory.make(); //new HashSet<PointsToEdge>();
    addConstraint(startEdge);
    this.depRuleGenerator = depRuleGenerator;
    this.produced = HashSetFactory.make(); //new HashSet<PointsToEdge>();
    this.produced.add(startEdge);
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
    
    //List<PointsToEdge> toRemove = new ArrayList<PointsToEdge>();
    
    for (PointsToEdge edge : constraints) {
      // do any constraints have a local var from node on the LHS?
      if (edge.getSource().isLocalVar() && edge.getSource().getNode().equals(node)) {
        if (Options.DEBUG) {
          Util.Debug("found stale constraint " + edge + "\nfor method " + node + "\nin " + this);
        }
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
    // TODO: explicitly check for assignment to null here
    Set<DependencyRule> rules = getRulesForInstr(instr, currentPath);
    if (rules == null) {
      return IQuery.FEASIBLE;
    }
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
    // won't get a match if one of the phi terms is a null; check if we can refute based on this
    if (matchingRules.isEmpty()) {
      PointerVariable phiLHS = new ConcretePointerVariable(currentPath.getCurrentNode(), instr.getDef(),
                               this.depRuleGenerator.getHeapModel());
      for (PointsToEdge edge : this.constraints) {
        // TODO: need to check rhs here? it shouldn't ever be null...
        if (edge.getSource().equals(phiLHS)) {
          Util.Debug("refuted by assignment to null");
          return IQuery.INFEASIBLE;
        }
      }
      return IQuery.FEASIBLE;
    }
    List<IQuery> splits = visitInternal(instr, currentPath, matchingRules);
    
    if (splits == IQuery.INFEASIBLE) {
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    if (Options.DEBUG) Util.Debug("after phi visit " + this);
    // Util.Assert(splits.isEmpty(), "shouldn't have caseSplits for phi's!");
    return splits;
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) {
    // what are the dependency rules generated by this instruction?
    Set<DependencyRule> rulesAtLine = getRulesForInstr(instr, currentPath);
    return visitInternal(instr, currentPath, rulesAtLine);
  }
  
  /**
   * @return
   */
  private List<IQuery> visitInternal(SSAInstruction instr, IPathInfo currentPath, Set<DependencyRule> rulesAtLine) {
    if (instr instanceof SSAGetCaughtExceptionInstruction) {
      if (Options.DEBUG)
        Util.Debug("refuted by exceptional path"); // we assume all thrown
                                                   // exception bubble to the
                                                   // top level
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }

    if (rulesAtLine == null || rulesAtLine.isEmpty()) {
      return checkForNullRefutation(instr, currentPath.getCurrentNode());
    }
    List<DependencyRule> applicableRules = new LinkedList<DependencyRule>();
    int inconsistentRules = 0;

    int ruleCounter = 0; // debug only
    for (DependencyRule rule : rulesAtLine) {
      if (Options.DEBUG)
        Util.Debug("rule " + ++ruleCounter + " of " + rulesAtLine.size() + ": " + rule);
      // see if this rule is relevant w.r.t our points-to constraints
      if (isRuleRelevant(rule, currentPath)) {
        Set<DependencyRule> newRules = isRuleConsistent(rule, unsatCore, currentPath.getCurrentNode());
        if (newRules != null) {
          if (Options.DEBUG) Util.Debug("consistent: " + newRules.size());
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
      //if (!Options.ABSTRACT_DEPENDENCY_RULES) caseSplits.add(this.deepCopy()); 
      //if (!rule.getShown().getSource().isLocalVar()) {
      if (!rule.getShown().getSource().isLocalVar() && !(rule.getShown().getSource().getInstanceKey() instanceof StaticFieldKey)) {
        boolean simultaneousPointsTo = false;
        for (PointsToEdge toShow : rule.getToShow()) {
          // if one of the preconditions for the rule is x -> A and we already have x -> B in our constraints,
          // then we cannot add a rule not applied path because this would imply that x points to two different locations simultaneouly.
          // even if A = B, this would imply that x points to two different instances of A, still giving us a refutation based on
          // simultaneous points-to
          if (toShow.getSource().isLocalVar() && (this.constraints.contains(toShow) || containsLocalVar(toShow.getSource()))) {
          //if (toShow.getSource().isLocalVar() && this.constraints.contains(toShow)) {
            simultaneousPointsTo = true;
            break;
          }
        }        
        if (!simultaneousPointsTo) {
          Util.Debug("adding rule not applied path.");
          caseSplits.add(this.deepCopy()); // add "rule not applied" path. this is neede for soundness
        }
      }
      if (applyRule(rule, this, this.depRuleGenerator.getHeapGraph())) return caseSplits;
      return IQuery.INFEASIBLE; // else, refuted
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
      
      DependencyRule rul = applicableRules.iterator().next();
      //if (!Options.ABSTRACT_DEPENDENCY_RULES) cases.add(copy.deepCopy()); // add "rule not applied" path
      if (!rul.getShown().getSource().isLocalVar() && !(rul.getShown().getSource().getInstanceKey() instanceof StaticFieldKey)) {
        caseSplits.add(this.deepCopy());
      }

      // many applicable rules; case split!
      for (DependencyRule rule : applicableRules) {
        if (first) {
          if (applyRule(rule, this, this.depRuleGenerator.getHeapGraph())) {
            first = false;
          //  continue; // first query will be the path we continue on (not added to
                    // case split array)
          }
          continue;
        }
        // create copy for this case and add it to the case split array
        PointsToQuery curQuery = copy.deepCopy(); 
        if (applyRule(rule, curQuery, this.depRuleGenerator.getHeapGraph())) {
          cases.addLast(curQuery);
        }
      }
      if (first) {
        // never found feasible path
        Util.Assert(cases.isEmpty());
        return IQuery.INFEASIBLE;
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
      if (Options.GEN_DEPENDENCY_RULES_EAGERLY) {
        depRuleGenerator.generateRulesForNode(currentPath.getCurrentNode());
      }
      // enter call from perspective of caller node
      // TODO: need special case of visiting?
      bindActualsToFormals(instr, currentPath.getCurrentNode(), callee);
      if (!isFeasible())
        return IQuery.INFEASIBLE; // check for refutation--can refute based on
                                  // null bindings in the above
    } else
      caseSplits = IQuery.FEASIBLE;

    // we need to do this in case there were rules that we didn't apply when
    // entering the call because they weren't relevant, but they are relevant now
    // TODO: is this heavy-handed? maybe we can just intelligently drop
    // constraints rather than re-entering the call...
    caseSplits = enterCall(instr, callee, currentPath);
    if (caseSplits == IQuery.INFEASIBLE) {
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    if (Options.DEBUG_ASSERTS)
      Util.Assert(caseSplits.isEmpty(), "shouldn't case split here because the arguments to the call are known!");

    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
    for (PointsToEdge edge : produced) {
      if (edge.getSource().getNode() != null && edge.getSource().getNode().equals(callee))
        toRemove.add(edge);
    }
    for (PointsToEdge edge : toRemove) {
      boolean removed = produced.remove(edge);
      if (Options.DEBUG_ASSERTS)
        Util.Assert(removed, "couldn't remove edge " + edge);
    }

    if (this.containsStaleConstraints(callee)) {
      if (Options.PIECEWISE_EXECUTION) {
        // TODO: hack! can make piecewise execution a bit more careful about
        // adding/removing local constraints
        removeAllLocalConstraints();
        return IQuery.FEASIBLE;
      }
      if (Options.DEBUG) Util.Debug("refuted by stale constraints!");
      return IQuery.INFEASIBLE;
    }
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
    Set<PointerVariable> formalsAssigned = HashSetFactory.make();
    MutableIntSet argsSeen = new BitVectorIntSet();
    Set<PointerVariable> possiblyAliased = HashSetFactory.make();
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    
    Map<PointerVariable,PointerVariable> subMap = HashMapFactory.make();
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
          // get the points-to set of arg, intersect with the sink of edge
          Set<InstanceKey> possibeVals = HashSetFactory.make();
          for (Iterator<Object> succs = hg.getSuccNodes(arg.getInstanceKey()); succs.hasNext();) {
            Object succ = succs.next();
            if (succ instanceof InstanceKey) possibeVals.add((InstanceKey) succ);
          }
          PointerVariable argVar = SymbolicPointerVariable.makeSymbolicVar(possibeVals);
          PointerVariable merged = SymbolicPointerVariable.mergeVars(argVar, edge.getSink());
          if (argVar.equals(merged)) continue;
          if (merged == null) {
            if (Options.DEBUG) {
              Util.Debug("refuted by parameter binding! intersection of " + argVar + " and " + edge.getSink() + " empty old edge " + edge);
            }
            this.feasible = false;
            return formalsAssigned;
          }
               
          Util.Assert(!subMap.containsKey(argVar) || subMap.get(argVar) == merged, "subMap already has " + argVar + Util.printMap(subMap));
          Util.Assert(!subMap.containsKey(edge.getSink()));

          subMap.put(argVar, merged);
          subMap.put(edge.getSink(), merged);
          
          PointsToEdge newEdge = new PointsToEdge(arg, merged);
          toAdd.add(newEdge);
          toRemove.add(edge);
          formalsAssigned.add(formal);
        }
      }
    }

    this.constraints.removeAll(toRemove);
    this.constraints.addAll(toAdd);
    substitute(this, subMap);
    toRemove.clear();
    toAdd.clear();
    subMap.clear();
    
    /*
    // TODO: might have to simplify w.r.t merged var
    for (PointsToEdge edge : toRemove) {
      boolean removed = constraints.remove(edge);
      if (!removed) Util.Assert(removed, "couldn't remove edge " + edge + " from " + Util.printCollection(constraints));
    }
    toRemove.clear();
    */
    
    Set<PointsToEdge> toAdd2 = HashSetFactory.make();
    for (PointsToEdge addMe : toAdd) {
      PointerVariable lhs = addMe.getSource();
      boolean add = true;
      // check for multiple bindings for single LHS
      for (PointsToEdge edge : this.constraints) {
        if (lhs.equals(edge.getSource())) {
          // merge the two vars
          PointerVariable newRHS = SymbolicPointerVariable.mergeVars(edge.getSink(), addMe.getSink());
          if (newRHS == null) {
            if (Options.DEBUG) Util.Debug("refuted by multiple binding! " + edge + " and " + addMe);
            this.feasible = false;
            return formalsAssigned;
          }
          add = false;
          toAdd2.add(new PointsToEdge(lhs, newRHS));
          toRemove.add(edge);
          Util.Assert(!subMap.containsKey(edge.getSink()));
          Util.Assert(!subMap.containsKey(addMe.getSink()));
          subMap.put(edge.getSink(), newRHS);
          subMap.put(addMe.getSink(), newRHS);
          break;
        }
      }
      if (add) addConstraint(addMe);
    }
    this.constraints.removeAll(toRemove);
    toRemove.clear();
    this.constraints.addAll(toAdd2);
    substitute(this, subMap);

    if (!possiblyAliased.isEmpty()) { // handle case where aliasing relationship
                                      // may be created by param passing
      if (Options.DEBUG)
        Util.Debug("potential aliasing!");
      for (PointerVariable var : possiblyAliased) {
        // set of edges with var as LHS
        Set<PointsToEdge> aliasedEdges = new TreeSet<PointsToEdge>(); 
        for (PointsToEdge edge1 : this.constraints) {
          if (edge1.getSource().isLocalVar() && edge1.getSource().equals(var))
            aliasedEdges.add(edge1);
        }
        toRemove.clear();
        toAdd.clear();
        for (PointsToEdge edge1 : aliasedEdges) { // for each edge with the same LHS
          for (PointsToEdge edge2 : aliasedEdges) {
            PointerVariable edge1Sink = edge1.getSink(), edge2Sink = edge2.getSink();
            if (edge1Sink.equals(edge2Sink)) {
              // sinks are the same; just pick one edge to remove
              toRemove.add(edge1);
              continue;
            }

            if (!edge1Sink.isSymbolic() && !edge2Sink.isSymbolic()) { // both concrete
              // they can't be equal; we already checked for equality
              if (Options.DEBUG)
                Util.Debug("refuted by parameter binding! " + edge1 + " " + edge2);
              this.feasible = false;
              return formalsAssigned;
            } 
            
            else if (!Options.NARROW_FROM_CONSTRAINTS) {
              toRemove.add(edge1); // can't narrow; just remove both of them
              toRemove.add(edge2);
              continue;
            }
            
            else if (edge1Sink.isSymbolic() && edge2Sink.isSymbolic()) { // both symbolic
              // pick the smaller set of abstract locations, remove the other set
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
                toAdd.add(new PointsToEdge(edge1.getSource(), SymbolicPointerVariable.makeSymbolicVar(intersectedValues)));
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
        for (PointsToEdge edge : toAdd) {
          addConstraint(edge);
        }
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
      for (PointsToEdge edge : toRemove) {
        Util.Assert(constraints.remove(edge), "Couldn't remove edge " + edge + " from " + this);
      }
      for (PointsToEdge edge : toAdd) {
        Util.Assert(addConstraint(edge), "Couldn't add edge " + edge);
      }
    }

    toRemove.clear();
    Util.Debug("binding formals to actuals: caller " + callerMethod + "; callee: " + calleeMethod);
    Set<PointerVariable> formalsAssigned = HashSetFactory.make();

    for (int i = 0; i < instr.getNumberOfParameters(); i++) {
      PointerVariable arg = new ConcretePointerVariable(callerMethod, instr.getUse(i), this.depRuleGenerator.getHeapModel());
      PointerVariable formal = new ConcretePointerVariable(calleeMethod, i + 1, this.depRuleGenerator.getHeapModel());
      
      for (PointsToEdge edge : constraints) {
        if (edge.getSource().equals(arg)) {
          //Util.Debug("binding " + formal + " to " + edge.getSink());
          PointsToEdge newEdge = new PointsToEdge(formal, edge.getSink());
       
          // begin ugliness; should rework this
          for (PointsToEdge prod : produced) {
            if (prod.getSource().equals(formal) && !prod.equals(newEdge)) {
              Util.Debug("multiple assignments " + prod + " and " + newEdge);
              // multiple assignments to formal; let's see if they're consistent
              if (prod.getSink().isSymbolic() && !newEdge.getSink().isSymbolic()) {
                
                if (Options.NARROW_FROM_CONSTRAINTS) {
                
                  SymbolicPointerVariable sink = (SymbolicPointerVariable) prod.getSink();
                  if (sink.getPossibleValues().contains(newEdge.getSink().getInstanceKey())) {
                    // new assignment is more precise; remove old one
                    toRemove.add(prod);
                  } else {
                    if (Options.DEBUG) {
                      Util.Debug("refuted by incompatible assignments to " + formal + " edge " 
                              + newEdge + " produced " + Util.constraintSetToString(produced));
                    }
                    // refuted

                    this.feasible = false;
                    return null;
                  }
                } else { // not narrowing
                  toRemove.add(prod);
                }
              }
            }
          }
          
          for (PointsToEdge removeMe : toRemove) {
            Util.Assert(produced.remove(removeMe), "couldn't remove edge " + removeMe + " from " + produced);
          }
          toRemove.clear();
          if (!Options.NARROW_FROM_CONSTRAINTS) produced.add(newEdge);
          formalsAssigned.add(formal);
          /*
          for (PointsToEdge prod : constraints) {

            if (prod.getSource().equals(formal) && !prod.equals(newEdge)) {
              // multiple assignments to formal; let's see if they're consistent
              if (prod.getSink().isSymbolic() && !newEdge.getSink().isSymbolic()) {
                
                if (Options.NARROW_FROM_CONSTRAINTS) {
                
                  SymbolicPointerVariable sink = (SymbolicPointerVariable) prod.getSink();
                  if (sink.getPossibleValues().contains(newEdge.getSink().getInstanceKey())) {
                    // new assignment is more precise; remove old one
                    toRemove.add(prod);
                  } else {
                    if (Options.DEBUG) {
                      Util.Debug("refuted by incompatible assignments to " + formal + " edge " 
                              + newEdge + " produced " + Util.constraintSetToString(produced));
                    }
                    // refuted
                    this.feasible = false;
                    return null;
                  }
                } else { // not narrowing
                  toRemove.add(prod);
                }
              }
            }
          }
          // end ugliness
           
          for (PointsToEdge removeMe : toRemove) {
            Util.Assert(constraints.remove(removeMe), "couldn't remove edge " + removeMe + " from " + produced);
          }
          toRemove.clear();
          if (!Options.NARROW_FROM_CONSTRAINTS) constraints.add(newEdge);
          formalsAssigned.add(formal);
          */
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

    return formalsAssigned;
  }
  
  private List<IQuery> checkForNullRefutation(SSAInstruction instr, CGNode node) {
    HeapModel hm = depRuleGenerator.getHeapModel();
    PointerKey key = null;
    if (instr instanceof SSAGetInstruction) {
      key = hm.getPointerKeyForLocal(node, instr.getDef());
    } else if (instr instanceof SSAReturnInstruction) {
      key = hm.getPointerKeyForReturnValue(node);
    }
    if (key != null) {
      PointerVariable var = Util.makePointerVariable(key);
      //Iterator<Object> succs = depRuleGenerator.getHeapGraph().getSuccNodes(key);
      //Util.Assert(!succs.hasNext());
      for (PointsToEdge edge : this.constraints) {
        if (edge.getSource().equals(var)) {
          this.feasible = false;
          Util.Debug("refuted by assigment to null");
          return IQuery.INFEASIBLE;
        }
      }
    }
    
    if (Options.DEBUG) Util.Debug("No rules at line...returning");
    return IQuery.FEASIBLE;
  }

  @Override
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    if (Options.GEN_DEPENDENCY_RULES_EAGERLY) depRuleGenerator.generateRulesForNode(callee);
    // the call instruction occurs in the caller
    CGNode caller = currentPath.getCurrentNode(); 
    // need to do this even if there are no rules at the line because the return
    // value may be important (and is not represented in the dependency rules)
    if (bindFormalsToActuals(instr, caller, callee) == null) {
      return IQuery.INFEASIBLE;
    }

    Util.Debug("PRODUCED " + Util.constraintSetToString(produced));

    //Set<DependencyRule> rulesAtLine = depRuleGenerator.getRulesForInstr(instr, caller);
    // get only the rules specific to entering this callee
    Set<DependencyRule> rulesAtLine = depRuleGenerator.generateAbstractRulesForInvoke(instr, caller, callee);
    if (rulesAtLine == null || rulesAtLine.isEmpty()) {
      return checkForNullRefutation(instr, currentPath.getCurrentNode());
    }
    // map from function parameter id's to list of dependency rules relevant to that id
    Map<Integer, List<DependencyRule>> idRuleMap = HashMapFactory.make();
    // set of function parameters we have seen for which there is a relevant but
    // not consistent rule
    Set<Integer> inconsistentParams = HashSetFactory.make();
    // set of function parameters for which there is a relevant and consistent rule
    Set<Integer> assignedParams = HashSetFactory.make(); 

    for (DependencyRule rule : rulesAtLine) { // create map of rules to parameters
      Util.Debug("trying rule for call " + rule);
      //if (formalsAlreadyAssigned.contains(rule.getShown().getSource())) {
        //Util.Debug("formal already assigned; continuing");
        //continue; // this formal is already spoken for
      //}

      if (isRuleRelevant(rule, currentPath)) {
        int paramId = rule.getShown().getSource().hashCode();
        Set<DependencyRule> newRules = isRuleConsistent(rule, this.unsatCore, null);
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
          for (DependencyRule rule : rulesForParam) {
            applicableRules.add(rule);
          }
          break;
        } // else, this is tricky. more than one parameter, and more than one
          // choice for one of them
          Util.Unimp("more than one rule for multiple parameters");
      } else if (rulesForParam.size() == 1)
        applicableRules.add(rulesForParam.get(0));
    }

    for (DependencyRule rule : applicableRules) { // apply each rule
      if (!applyRule(rule, this, this.depRuleGenerator.getHeapGraph())) return IQuery.INFEASIBLE;
    }
    return IQuery.FEASIBLE;
  }

  /**
   * given that we are entering callee from an arbitrary context, perform all possible combinations of var bindings
   * @param callee
   */
  @Override
  public void enterCallFromJump(CGNode callee) {
    int[] params = callee.getIR().getParameterValueNumbers();
    HeapModel hm = this.depRuleGenerator.getHeapModel();
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    MutableIntSet bound = new BitVectorIntSet();
    for (int i = 0; i < params.length; i++) {
      PointerKey key = hm.getPointerKeyForLocal(callee, params[i]);
      PointerVariable param = new ConcretePointerVariable(callee, params[i], this.depRuleGenerator.getHeapModel());
      Iterator<Object> succs = hg.getSuccNodes(key);
      while (succs.hasNext()) {
        Object succ = succs.next();
        PointerVariable paramPointedTo = Util.makePointerVariable(succ);
        for (PointsToEdge edge : this.constraints) {
          if (edge.getSource().symbEq(paramPointedTo)) {
            Util.Assert(!edge.getSource().isSymbolic(), "unimp: need to bind symbolic var here");
            this.produced.add(new PointsToEdge(param, paramPointedTo));
            boolean added = bound.add(params[i]);
            Util.Assert(added, "more than one binding for v" + params[i] + Util.printCollection(this.produced)); 
          }
        }
      }
    }
  }

  static boolean applyRule(DependencyRule rule, PointsToQuery query, HeapGraph hg) {
    // TODO: this is a giant mess that's impossible to reason about. clean it up
    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
    // special case for when the constraints contain a symbolic edge that
    // matches a concrete edge in the constraints
    for (PointsToEdge ruleEdge : rule.getToShow()) {
      if (ruleEdge.isSymbolic()) continue;
      for (PointsToEdge edge : query.constraints) {
        if (edge.getSink().isSymbolic() && 
            edge.getSource().equals(ruleEdge.getSource())) {
          if (edge.getSink().symbContains(ruleEdge.getSink())) {
            // remove the symbolic edge; it should be replaced with the concrete
            // one from this rule
            toRemove.add(edge);
          }
        }
      }
    }
    for (PointsToEdge removeMe : toRemove) {
      //Util.Debug("removing " + toRemove);
      query.constraints.remove(removeMe);
    }

    toRemove.clear();
    for (PointsToEdge edge : query.produced) {
      if (edge.getSource().isLocalVar()) continue;
      if (edge.getSource().equals(rule.getShown().getSource()) && 
          !rule.getShown().getSink().equals(edge.getSink())) {
        toRemove.add(edge);
      }
    }
    for (PointsToEdge removeMe : toRemove) query.produced.remove(removeMe);
    toRemove.clear();
        
    Map<SymbolicPointerVariable,PointerVariable> subMap = HashMapFactory.make();

    //Util.Debug("removing " + rule.getShown());
    query.constraints.remove(rule.getShown());
    // special case for if shown removes a symbolic edge from the constraints
    for (PointsToEdge edge : query.constraints) {
      //if (edge.isSymbolic() && edge.symbContains(rule.getShown())) {
      if (edge.isSymbolic() && edge.symbEq(rule.getShown())) {
        toRemove.add(edge);
        // look for other instances of the symbolic var to subsitute
        if (edge.getSource().isSymbolic()) {
          subMap.put((SymbolicPointerVariable) edge.getSource(), rule.getShown().getSource());
          Util.Debug("replacing " + edge.getSource() + " with " + rule.getShown().getSource());
        } else if (edge.getSink().isSymbolic()) {
          subMap.put((SymbolicPointerVariable) edge.getSink(), rule.getShown().getSink());
          Util.Debug("replacing " + edge.getSink() + " with " + rule.getShown().getSink());
        }
      }
    }
    for (PointsToEdge removeMe : toRemove) {
      Util.Debug("removing " + removeMe);
      query.constraints.remove(removeMe);
    }

    List<PointsToEdge> toAdd = new ArrayList<PointsToEdge>();
    for (SymbolicPointerVariable key : subMap.keySet()) {
      toRemove.clear();
      for (PointsToEdge edge : query.constraints) {
        boolean remove = false;
        PointerVariable newSrc = edge.getSource(), newSnk = edge.getSink();
        if (edge.getSource() == key) {
          newSrc = subMap.get(key);
          remove = true;
        }
        if (edge.getSink() == key) {
          newSnk = subMap.get(key);
          remove = true;
        }
        if (remove) {
          PointsToEdge newEdge = new PointsToEdge(newSrc, newSnk, edge.getFieldRef());
          Util.Debug("now adding " + newEdge);
          toAdd.add(newEdge);
          toRemove.add(edge);
        }
      }
      for (PointsToEdge removeMe : toRemove) {
        Util.Debug("removing " + removeMe);
        query.constraints.remove(removeMe);
      }
      //query.constraints.removeAll(toRemove);
      query.constraints.addAll(toAdd);
      toAdd.clear();
    }
        

    if (rule.getShown().getSource().isParameter() ||
        !WALACFGUtil.isInLoopBody(rule.getBlock(), rule.getNode().getIR())) query.produced.add(rule.getShown());
    //else Util.Debug("not adding " + rule.getShown() + " because in loop body");
    toRemove.clear();
    
    for (PointsToEdge edge : rule.getToShow()) {
      if (edge.isSymbolic()) {
        boolean add = true;
        // check if some produced edge already subsumes the new edge 
        for (PointsToEdge prod : query.produced) {
          if (!prod.getSource().isLocalVar()) continue;
          if (edge.equals(prod)) {
            add = false;
            break;
          }
        }
        
        for (PointsToEdge queryEdge : query.constraints) {
          if (edge.symbContains(queryEdge)) {
            // query edge is already more specific
            add = false;
            break;
          }

          // else, merge the two if LHS's are the same
          // TODO: not sure if this is sound with heap lhs's, sticking to locals for now
          if (edge.getSource().isLocalVar() && edge.getSource().equals(queryEdge.getSource())) {
            PointerVariable newSnk = SymbolicPointerVariable.mergeVars(edge.getSink(), queryEdge.getSink());
            if (newSnk == null) {
              if (Options.DEBUG) Util.Debug("refuting by empty intersection of " + edge.getSink() + " and " + queryEdge.getSink());
              return false;
            }
            Util.Debug("merged " + edge.getSink() + " and " + queryEdge.getSink() + " with common lhs " + edge.getSource());
            Util.Assert(newSnk != null, "problem merging " + edge + " and " + queryEdge);
            edge = new PointsToEdge(queryEdge.getSource(), newSnk, queryEdge.getField());
            toRemove.add(queryEdge);
          }
        }
         
        if (add) {
          //Util.Debug("adding " + edge);
          query.addConstraint(edge);
        }
        for (PointsToEdge removeMe : toRemove) {
          //Util.Debug("removing " + removeMe);
          query.constraints.remove(removeMe);
        }
        toRemove.clear();
      } else {
        //if (query.produced.contains(edge)) Util.Debug("re-adding " + edge);
        if (!query.produced.contains(edge) || !edge.getSource().isLocalVar()) {
          //Util.Debug("adding here " + edge);
          query.addConstraint(edge);
        } 
      }
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
    
    if (Options.DEBUG) {
      //Util.Debug("after simplification, query is " + qry);
      for (PointsToEdge constraint : query.constraints) {
        if (constraint.getSource().isLocalVar()) {
          ConcretePointerVariable lhs = (ConcretePointerVariable) constraint.getSource();
          for (PointsToEdge edge : query.constraints) {
            if (edge == constraint) continue;
            Util.Assert(!lhs.equals(edge.getSource()), "constraints already contain " + edge + "\nadding " + constraint);
            //Util.Assert(!lhs.equals(edge.getSource()) || edge.equals(constraint), "constraints already contain " + edge + "\nadding "
              //    + constraint);
          }
        }
      } 
    }
 
    //Util.Debug("after applying " + query);
    return simplifyQuery(query, hg);
    //return true;
  }
  
  /**
   * further constraint symbolic variables according to the pts-to and pts-at sets of vars they share an edge with
   */
  // TODO: what if the symbolic variables occur in the path query?
  public static boolean simplifyQuery(PointsToQuery qry, HeapGraph hg) {
    Map<PointerVariable,PointerVariable> subMap = HashMapFactory.make(qry.constraints.size());
    for (PointsToEdge edge : qry.constraints) {
      if (!edge.isSymbolic()) continue; // no symbolic vars; impossible to constraint this more      
      IField field = edge.getFieldRef();
      if (field != null) {
        PointerVariable src = edge.getSource();
        PointerVariable snk = edge.getSink();
        Set<InstanceKey> srcVals = src.getPossibleValues();
        Set<InstanceKey> snkVals = snk.getPossibleValues();

        //Util.Debug("snkVals " + Util.printCollection(snkVals));
        Set<InstanceKey> srcPtsTo = src.getPointsToSet(hg, field);
        //Util.Debug("src pts-to " + Util.printCollection(srcPtsTo));
        srcPtsTo.retainAll(snkVals);
        //Util.Debug("after inter " + Util.printCollection(srcPtsTo));
        if (srcPtsTo.isEmpty()) {
          if (Options.DEBUG) Util.Debug("refuted by intersection of pts-to set and symbolic var on " + edge);
          return false;
        }
        
        // ptsTo(src) \cap vals(sink) == vals(sink)? 
        if (!srcPtsTo.equals(snkVals)) {
          // if not, vals(sink) is not precise; create new symbolic var containing the intersection
          PointerVariable newVar = SymbolicPointerVariable.makeSymbolicVar(srcPtsTo);
          PointerVariable mapping = subMap.get(snk);
          if (mapping == null) subMap.put(snk, newVar); // no sub for this yet
          else if (newVar.getPossibleValues().equals(mapping.getPossibleValues())) {
            // already subbed, but the possible values don't agree. take the intersection
            Set<InstanceKey> newVals = newVar.getPossibleValues();
            newVals.retainAll(mapping.getPossibleValues());
            if (newVals.isEmpty()) {
              if (Options.DEBUG) Util.Debug("refuted by intersection of pts-to set and symbolic var on " + edge);
              return false;
            }
            newVar = SymbolicPointerVariable.makeSymbolicVar(newVals);
            subMap.put(snk, newVar);
          }
        }
        
        // no hope in refuting based on the pts-at set of a static field
        if (field.isStatic()) continue;
        
        //Util.Debug("srcVals " + Util.printCollection(srcVals));
        Set<InstanceKey> snkPtsAt = snk.getPointsAtSet(hg, field);
        //Util.Debug("snk pts-at " + Util.printCollection(snkPtsAt));
        snkPtsAt.retainAll(srcVals);
        //Util.Debug("after inter " + Util.printCollection(snkPtsAt));
        
        if (snkPtsAt.isEmpty()) {
          if (Options.DEBUG) Util.Debug("refuted by intersection of pts-at set and symbolic var on " + edge);
          return false;
        }
        
        // ptsAt(snk) \cap vals(src) == vals(src)? 
        if (!snkPtsAt.equals(srcVals)) {
          // if not, vals(src) is not precise; create new symbolic var containing the intersection
          PointerVariable newVar = SymbolicPointerVariable.makeSymbolicVar(snkPtsAt);
          PointerVariable mapping = subMap.get(src);
          if (mapping == null) subMap.put(src, newVar); // no sub for this yet
          else if (!newVar.getPossibleValues().equals(mapping.getPossibleValues())) {
            // already subbed, but the possible values don't agree. take the intersection
            Set<InstanceKey> newVals = newVar.getPossibleValues();
            newVals.retainAll(mapping.getPossibleValues());
            if (newVals.isEmpty()) {
              if (Options.DEBUG) Util.Debug("refuted by intersection of pts-to set and symbolic var on " + edge);
              return false;
            }
            newVar = SymbolicPointerVariable.makeSymbolicVar(newVals);
            subMap.put(src, newVar);
          }
        }           
      }
    }
    
    substitute(qry, subMap);
 
    if (Options.DEBUG) {
      //Util.Debug("after simplification, query is " + qry);
      for (PointsToEdge constraint : qry.constraints) {
        if (constraint.getSource().isLocalVar()) {
          ConcretePointerVariable lhs = (ConcretePointerVariable) constraint.getSource();
          for (PointsToEdge edge : qry.constraints) {
            if (edge == constraint) continue;
            Util.Assert(!lhs.equals(edge.getSource()), "constraints already contain " + edge + "\nadding " + constraint);
            //Util.Assert(!lhs.equals(edge.getSource()) || edge.equals(constraint), "constraints already contain " + edge + "\nadding "
              //    + constraint);
          }
        }
      } 
    }
    return true;
  }
  
  // update query by performing substituion according to subMap
  private static void substitute(PointsToQuery qry, Map<PointerVariable,PointerVariable> subMap) {
    List<PointsToEdge> toRemove = new ArrayList<PointsToEdge>(qry.constraints.size());
    List<PointsToEdge> toAdd = new ArrayList<PointsToEdge>(qry.constraints.size());
    // iterate through edges and perform necessary substitutions
    for (PointsToEdge edge : qry.constraints) {
      PointsToEdge subbed = edge.substitute(subMap);
      if (subbed != edge) {
        toRemove.add(edge);
        toAdd.add(subbed);
      }
    }
    for (PointsToEdge removeMe : toRemove) qry.constraints.remove(removeMe);
    for (PointsToEdge addMe : toAdd) qry.addConstraint(addMe);//qry.constraints.add(addMe
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
    // TODO: this is probably the ugliest/worst code in all of Thresher. rethink entirely
    PointsToEdge shown = rule.getShown();
    Set<DependencyRule> rules = new TreeSet<DependencyRule>();
    List<Map<SymbolicPointerVariable, PointerVariable>> subMaps = new LinkedList<Map<SymbolicPointerVariable, PointerVariable>>();
    Map<SymbolicPointerVariable, PointerVariable> subMap = HashMapFactory.make();
    subMaps.add(subMap);
    Set<PointerVariable> alreadySubbed = HashSetFactory.make();

    List<PointsToEdge> ruleEdges = new LinkedList<PointsToEdge>();
    ruleEdges.add(shown);
    ruleEdges.addAll(rule.getToShow());

    // first, match edges with local LHS's and concrete RHS's. these are hard constraints
    for (PointsToEdge edge : constraints) {
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && edge.getSource().isLocalVar() && !edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, true);
      }
    }
    for (PointsToEdge edge : produced) {
      if (!edge.getSource().isLocalVar()) continue;
      //Util.Assert(edge.getSource().isLocalVar(), "produced should only contain locals");
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && !edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, true);
      }
    }

    // now, match edges with local LHS's and symbolic sinks. these are not hard constraints; there may be multiple choices
    for (PointsToEdge edge : constraints) {
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && edge.getSink().isSymbolic())
          //ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false);
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, true);
      }
    }
    for (PointsToEdge edge : produced) {
      if (!edge.getSource().isLocalVar()) continue;
      for (PointsToEdge ruleEdge : ruleEdges) {
        if (ruleEdge.getSource().isLocalVar() && edge.getSink().isSymbolic())
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false);
      }
    }

    if (subMaps.size() != 1) {
      for (Map map : subMaps) Util.Debug(Util.printMap(map));
      Util.Assert(subMaps.size() == 1, "more than one instantiation choice for shown! have " + subMaps.size()
          + " this shouldn't happen, since we've only considered local constraints");      
    }

    
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
          Util.Print("doing non-local edge ruleEdge " + edge + " and edge " + edge);
          ruleEdge.getSubsFromEdge(edge, subMaps, alreadySubbed, false);
      }
    }

    for (Map<SymbolicPointerVariable, PointerVariable> map : subMaps) {
      rules.add(newRule.substitute(map));
    }

    Map<SymbolicPointerVariable, PointerVariable> aliasMap = HashMapFactory.make();

    List<DependencyRule> toAdd = new LinkedList<DependencyRule>();
    // also consider possible aliasing relationships
    for (DependencyRule symbRule : rules) {
      Set<SymbolicPointerVariable> symbVars = symbRule.getSymbolicVars();
      if (symbVars.size() > 1) { // more than 1 symbolic var; consider all
                                 // possible aliasing combos
        Util.Assert(symbVars.size() == 2, "more than 2 symbvars in " + symbRule);
        Iterator<SymbolicPointerVariable> iter = symbVars.iterator();
        SymbolicPointerVariable var0 = iter.next(), var1 = iter.next();
        // comparison issues mean we don't know whether var0/var1 is the toSub/subFor var.
        // whichever var the old rule contains, that's the subFor variable
        if (rule.getSymbolicVars().contains(var0)) {
          if (var1.symbEq(var0))  {
            if (Options.DEBUG) {
              //Util.Debug(rule + "contains " + var0);
              Util.Debug("considering aliasing of " + var0 + " and " + var1);
            }
            aliasMap.put(var0, var1);
          }
        } else {
          if (var0.symbEq(var1)) {
            if (Options.DEBUG) {
              Util.Debug("considering aliasing of " + var1 + " and " + var0);
            }
            //aliasMap.put(var1, var0);
            aliasMap.put(var0, var1);
          }
        }

        toAdd.add(symbRule.substitute(aliasMap));
      }
      aliasMap.clear();
    }
    rules.addAll(toAdd);  
    return rules;
  }

  boolean isSymbolicRuleRelevant(DependencyRule rule, IPathInfo currentPath) {
    PointsToEdge shown = rule.getShown();
    Collection<PointsToEdge> toCheck = new ArrayList<PointsToEdge>(3);
    toCheck.add(rule.getShown());
    toCheck.addAll(rule.getToShow());
    
    // TMP: desired?
    //for (PointsToEdge shown : toCheck) {
    
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
        fieldsEqual = Util.equal(edge.getField(), shown.getField()); // fields match
      }

      if (lhsMatch && fieldsEqual) {
        if (Options.DEBUG)
          Util.Debug("relevant: " + edge);
        return true;
      }
    }
  
    if (!SCWALA_MODE) {
    for (PointsToEdge edge : produced) {
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
        fieldsEqual = Util.equal(edge.getField(), shown.getField()); // fields match
      }

      // won't be able to get refutation via simultaneous points-to if field is an array field
      boolean notArrays = (edge.getFieldRef() == null || !(edge.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS))
                       && (shown.getFieldRef() == null || !(shown.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS));
      
      //if (lhsMatch && fieldsEqual) {
      if (lhsMatch && fieldsEqual && notArrays) {
        if (Options.DEBUG)
          Util.Debug("relevant (produced): " + edge);
        return true;
      }
    }
    }
    
    return false;
  }

  DependencyRule isSymbolicRuleConsistent(DependencyRule rule, Set<PointsToEdge> constraints,
                                          List<PointsToEdge> unsatCore, CGNode currentNode) {
    TreeSet<PointsToEdge> checkMe = new TreeSet<PointsToEdge>();
    PointsToEdge shown = rule.getShown();
    checkMe.addAll(rule.getToShow());
    checkMe.add(shown);
    
    // HACK
    boolean producedSet = constraints == this.produced;

    // map from (symbolic pointer vars) -> (vars to sub, field)
    // Map<SymbolicPointerVariable,PointerVariable> subMap = new
    // HashMap<SymbolicPointerVariable,PointerVariable>();

    for (PointsToEdge constraint : constraints) {
      // can't refuted based on non-local constraints in produced set
      if (producedSet && !constraint.getSource().isLocalVar()) continue;
      for (PointsToEdge edge : checkMe) {
        boolean lhsMatch;
        boolean fieldsEqualAndNotArrays;
        if (edge.getSource().isSymbolic() && constraint.getSource().isSymbolic()) { // both edges symbolic
          lhsMatch = edge.getSource().getPossibleValues().equals(constraint.getSource().getPossibleValues());
          
          // can't compare symbolic vars for equality if we can't narrow (only inequality). must soundly say NEQ
          if (!Options.NARROW_FROM_CONSTRAINTS) lhsMatch = false;
                                                           
          
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
        } else if (edge.getSource().isSymbolic()) { // rule edge symbolic, constraint edge concrete
          lhsMatch = edge.getSource().getPossibleValues().contains(constraint.getSource().getInstanceKey());
          fieldsEqualAndNotArrays = Util.equal(edge.getFieldRef(), constraint.getFieldRef())
              && (edge.getFieldRef() == null || !(edge.getFieldRef() == AbstractDependencyRuleGenerator.ARRAY_CONTENTS))
              && (constraint.getField() == null || !(constraint.getField() instanceof ArrayContentsKey));
         } else if (constraint.getSource().isSymbolic()) { // constraint edge symbolic, rule edge concrete
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
            //if (Options.NARROW_FROM_CONSTRAINTS) {
              rhsEq = Util.intersectionNonEmpty(edge.getSink().getPossibleValues(), 
                                               constraint.getSink().getPossibleValues());
            //} else rhsEq = true; // can't compare for equality without narrowing
          } else if (edge.getSink().isSymbolic()) {
            rhsEq = edge.getSink().getPossibleValues().contains(constraint.getSink().getInstanceKey());
           } else if (constraint.getSink().isSymbolic()) {
            rhsEq = constraint.getSink().getPossibleValues().contains(edge.getSink().getInstanceKey());
          } else { // concrete case
            rhsEq = constraint.getSink().equals(edge.getSink());
          }
          if (!rhsEq) {
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

  public boolean isRuleRelevant(DependencyRule rule, IPathInfo currentPath) {
    //if (rule.isSymbolic()) return isSymbolicRuleRelevant(rule, currentPath);
    if (true) return isSymbolicRuleRelevant(rule, currentPath);
    List<PointsToEdge> checkMe = new ArrayList<PointsToEdge>(3);
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

    if (!SCWALA_MODE) {
      
    // also possible that it matches / contradicts a constraint we already have
    // in produced
    for (PointsToEdge edge : produced) {
    //  Util.Assert(edge.getSource().isLocalVar(), "only constraints with local LHS should be in produced set!");
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
    
    }

    /*
     * // check for relevance to extra vars for (PointsToEdge edge : checkMe) {
     * if (extraVars.contains(edge.getSource())) { if (Options.DEBUG)
     * Util.Debug("relevant (extra) " + edge); return true; } }
     */
    return false;
  }

  // queries configured for scwala, which does not have SSA
  static boolean SCWALA_MODE = true;
  
  Set<DependencyRule> isRuleConsistent(DependencyRule rule, List<PointsToEdge> unsatCore, CGNode currentNode) {
    // if (rule.isSymbolic()) {
    if (Options.ABSTRACT_DEPENDENCY_RULES) {
     
        // if this is a new instruction, bind it
      if (rule.getStmt() != null && rule.getStmt().isNewInstr()) {
        PointsToEdge shown = rule.getShown();
        Set<DependencyRule> singleton = new TreeSet<DependencyRule>();

        for (PointsToEdge edge : this.constraints) {
          if (edge.getSource().equals(shown.getSource())) {
            if (edge.getSink().isSymbolic()) {
              DependencyRule newRule = new DependencyRule(edge, rule.getStmt(), rule.getToShow(), rule.getNode(), rule.getBlock());
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
          
          if (edge.getSource().equals(shown.getSink())) {
            // if there are constraints on the fields of this instance, they can never be produced now, so we can refute
            // TODO: this is the wrong way to do this...we should find the class initializer and symbolically execute it
            if (Options.DEBUG) Util.Debug("refuted by stale field on " + edge);
            return null;
          }

        }
        singleton.add(rule);
        return singleton;
      } else {
        //if (rule.isSymbolic()) {
          Set<DependencyRule> newRules = bindSymbolicRule(rule, this, currentNode);
          Util.Assert(!newRules.isEmpty(), "should not be empty here!");
          List<DependencyRule> toRemove = new LinkedList<DependencyRule>();
          for (DependencyRule newRule : newRules) {
            if (isSymbolicRuleConsistent(newRule, this.constraints, unsatCore, currentNode) == null) {
              // DependencyRule newRule = isSymbolicRuleConsistent(rule,
              // currentQuery, this.constraints, currentNode);
              toRemove.add(newRule);
              continue;
            }
            // if (isSymbolicRuleConsistent(rule, currentQuery, this.produced,
            // currentNode) == null) return null;
            if (isSymbolicRuleConsistent(newRule, this.produced, unsatCore, currentNode) == null) {
              toRemove.add(newRule);
              continue;
            }
          }
          newRules.removeAll(toRemove);
          if (newRules.isEmpty())
            return null;
          return newRules; 
      //}
      }
        //else
        //return doConsistencyCheckNonSymbolic(rule, unsatCore, currentNode);
    } else {
      return doConsistencyCheckNonSymbolic(rule, unsatCore, currentNode);
    }
  }

  private Set<DependencyRule> doConsistencyCheckNonSymbolic(DependencyRule rule, List<PointsToEdge> unsatCore, CGNode currentNode) {
    if (!isRuleConsistent(rule, this, this.constraints, unsatCore, currentNode, false))
      return null;
    if (isRuleConsistent(rule, this, this.produced, unsatCore, currentNode, true)) {
      Set<DependencyRule> singleton = new TreeSet<DependencyRule>();
      singleton.add(rule);
      return singleton;
    } else
      return null;
  }

  static boolean isRuleConsistent(DependencyRule rule, PointsToQuery currentQuery, Set<PointsToEdge> constraints,
      List<PointsToEdge> unsatCore, CGNode currentNode, boolean producedSet) {
    TreeSet<PointsToEdge> checkMe = new TreeSet<PointsToEdge>();
    PointsToEdge shown = rule.getShown();
    checkMe.addAll(rule.getToShow());
    checkMe.add(shown);
    
    for (PointsToEdge constraint : constraints) {
      // can't refute based on non-locals in proudced
      if (producedSet && !constraint.getSource().isLocalVar()) continue;
      for (PointsToEdge edge : checkMe) {
        // to check: lhs's equal and (fieldnames equal and not array's) => rhs's
        // equal
        boolean lhsNameMatch = edge.getSource().equals(constraint.getSource());
        boolean fieldsEqualAndNotArrays = Util.equal(constraint.getField(), edge.getField())
            && (constraint.getField() == null || !(constraint.getField() instanceof ArrayContentsKey))
            && (edge.getField() == null || !(edge.getField() instanceof ArrayContentsKey));
        boolean rhsesEqual;
        if (constraint.getSink().isSymbolic()) {
          rhsesEqual = constraint.getSink().symbEq(edge.getSink());
        } else {
          rhsesEqual = constraint.getSink().equals(edge.getSink());
        }

        if (lhsNameMatch && fieldsEqualAndNotArrays && !rhsesEqual) {
          PointerVariable constraintSrc = constraint.getSource();
          // is LHS a local or heap loc?
          if (constraintSrc.isLocalVar()) { // can't split a local into multiple instances...
            if (WALACFGUtil.isInLoopBody(rule.getBlock(), rule.getNode().getIR())) { // ...unless
                                                                                     // it
                                                                                     // occurs
                                                                                     // in
          
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
          // a single "rule not applied" case suffices
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
   * @return - the points-to set of var if it is a singleton, otherwise err
   */
  public PointerVariable getPointedTo(PointerVariable var) {
    return getPointedTo(var, true);
  }
  
  public PointerVariable getPointedTo(PointerVariable var, FieldReference field) {
    Util.Pre(var.isLocalVar());
    Util.Pre(field != null);
    PointerVariable found = null;
    PointerVariable ref = getPointedTo(var);
    if (ref != null) {
      for (PointsToEdge edge : this.constraints) {
        if (edge.getSource().equals(ref) && edge.getFieldRef() != null && edge.getFieldRef().getReference().equals(field)) {
          Util.Assert(found == null, "should only find var on LHS of one points-to relation! got " + found + " and " + edge.getSink());
          found = edge.getSink();
        }
      }
    }  
   
    return found;
  }
  
  public Set<PointerVariable> getPointsToSet(PointerVariable var) {
    Set<PointerVariable> pt = HashSetFactory.make();
    for (PointsToEdge edge : this.constraints) {
      if (edge.getSource().equals(var)) {
        pt.add(edge.getSink());
      }
    }
    return pt;
  }
  
  public Set<PointerVariable> getPointsAtSet(PointerVariable var) {
    Set<PointerVariable> pa = HashSetFactory.make();
    for (PointsToEdge edge : this.constraints) {
      if (edge.getSink().equals(var)) {
        pa.add(edge.getSource());
      }
    }
    return pa;
  }
  
  /**
   * find the var pointed to by the given var in our consraints
   * 
   * @param var
   *          - variable to look for on LHS of points-to relation
   * @return return the location pointed to by var, or null if var is not found
   *         on the LHS of any constraint in the set
   */
  PointerVariable getPointedTo(PointerVariable var, boolean checkProduced) {
    PointerVariable pointed = getPointedTo(var, constraints);
    if (pointed != null) return pointed;
    if (checkProduced) {
      return getPointedTo(var, produced);
    }
    return null;
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
        Util.Assert(found == null, "should only find var on LHS of one points-to relation! got " + found + " and " + edge.getSink());
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
  
  @Override
  public boolean addConstraintFromConditional(SSAConditionalBranchInstruction instruction, 
      CGNode node, boolean trueBranchFeasible) {
    return true;
  }
  
  // do nothing
  @Override
  public void declareFakeWitness() {}
  
  public Set<PointsToEdge> getConstraintsRelevantToCall(CGNode callee, boolean earlyRet) {
    return getConstraintsRelevantToCall(null, null, callee, earlyRet);
  }
  
  public Set<PointsToEdge> getConstraintsRelevantToCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee, boolean earlyRet) {
    Set<PointsToEdge> toRemove = HashSetFactory.make();
    if (instr != null && instr.hasDef()) {
      ConcretePointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      for (PointsToEdge edge : this.constraints) {
        if (edge.getSource().equals(retval)) {
          // relevant due to the return value
          toRemove.add(edge);
          if (earlyRet) {
            Util.Debug("retval relevant");
            return toRemove; 
          }
        }
      }
    }
    // a null callee means we're dropping constraints for a call that resolves to 0 call sites (so only need to drop retval)
    if (callee == null) return toRemove;
    
    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (PointsToEdge edge : constraints) {     
      PointerKey key = edge.getField();  
      if (key != null && keys.contains(key)) {
        toRemove.add(edge);
        if (earlyRet) {
          Util.Debug("key " + key + " relevant");
          return toRemove; 
        }
      }
      
      // if the source is symbolic, there may be many fields that are modified -- check 'em all
      if (edge.getSource().isSymbolic()) {
        Util.Assert(edge.getFieldRef() != null);
        SymbolicPointerVariable src = (SymbolicPointerVariable) edge.getSource();    
        for (PointerKey fieldKey : src.getPossibleFields(edge.getFieldRef(), this.depRuleGenerator.getHeapModel())) {
          if (keys.contains(fieldKey)) {  
            toRemove.add(edge);
            if (earlyRet) {
              Util.Debug("key " + fieldKey + " relevant");
              return toRemove; 
            }
          }
        }
      }
    }
    return toRemove;
  }
  
  @Override
  public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) {
    if (this.constraints.isEmpty()) return false;
    return !getConstraintsRelevantToCall(instr, caller, callee, true).isEmpty();
  }
  
  @Override
  public void dropReturnValueConstraintsForCall(SSAInvokeInstruction instr, CGNode caller) {
    if (instr.hasDef()) {
      ConcretePointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      PointsToEdge toRemove = null;
      for (PointsToEdge edge : this.constraints) {
        if (edge.getSource().equals(retval)) {
          toRemove = edge;
          break;
        }
      }
      if (toRemove != null) this.constraints.remove(toRemove);
    }
  }

  @Override
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee, boolean dropPtConstraints) {
    if (this.constraints.isEmpty()) return;
    Set<PointsToEdge> toRemove = getConstraintsRelevantToCall(instr, caller, callee, false); 
    for (PointsToEdge edge : toRemove) {
      Util.Print("dropping constraint " + edge);
      //if (Options.DEBUG) Util.Debug("DROPPING " + edge);
      
      this.constraints.remove(edge);
      this.produced.remove(edge);
    }
  }

  // TODO: change this to use the mod/ref instead of generating rules?
  public Set<PointsToEdge> getLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode, boolean earlyRet) {
    Set<PointsToEdge> relevant = HashSetFactory.make();
    Set<DependencyRule> loopRules = new TreeSet<DependencyRule>();
    Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(currentNode); 
    for (DependencyRule rule : rules) { // keep only rules produced in loop
      Util.Assert(rule.getBlock() != null, "no basic block for rule " + rule);
      if (WALACFGUtil.isInLoopBody(rule.getBlock(), loopHead, currentNode.getIR())) {
        loopRules.add(rule);
      }
    }
    // see if any of the rules produces one of our edges
    for (DependencyRule rule : loopRules) { 
      for (PointsToEdge edge : this.constraints) {
        if (rule.getShown().equals(edge) || rule.getShown().symbEq(edge)) {
          relevant.add(edge);
          if (earlyRet) return relevant;
        }
      }
    }

    // the loop may also contain callees. see if those callees can write to vars in our constraints
    Set<CGNode> targets = WALACFGUtil.getCallTargetsInLoop(loopHead, currentNode, depRuleGenerator.getCallGraph());
    for (CGNode callNode : targets) { 
      // drop all vars that can be written by a call in the loop body
      Set<PointsToEdge> callRelevant = getConstraintsRelevantToCall(callNode, earlyRet);
      if (earlyRet && !callRelevant.isEmpty()) return callRelevant;
      relevant.addAll(callRelevant);
    }
    return relevant;
  }
  
  /**
   * @return - all the constraints with local LHS's
   */
  private Collection<ConcretePointerVariable> getLocalVars() {
    Collection<ConcretePointerVariable> locals = new ArrayList<ConcretePointerVariable>();
    for (PointsToEdge edge : this.constraints) {
      if (edge.getSource().isLocalVar()) {
        locals.add((ConcretePointerVariable) edge.getSource());
      }
    }
    return locals;
  }
  
  public boolean containsLocalVar(PointerVariable loc) {
    Util.Pre(loc.isLocalVar());
    for (PointsToEdge edge : this.constraints) {
      if (edge.getSource().equals(loc)) return true;
    }
    return false;
  }

  @Override
  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    if (this.constraints.isEmpty()) return false;
    return !getLoopProduceableConstraints(loopHead, currentNode, true).isEmpty();
  }

  @Override
  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    if (this.constraints.isEmpty()) return;
    Set<PointsToEdge> toRemove = getLoopProduceableConstraints(loopHead, currentNode, false);
    for (PointsToEdge edge : toRemove) {
      if (Options.DEBUG) Util.Debug("dropping " + edge);
      this.constraints.remove(edge);
      this.produced.remove(edge);
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

        // if the concretization of the other edge \supset eq concretization of our edge
        if (constraint1.symbContains(constraint2)) { 
        //if (constraint2.symbContains(constraint1)) { 
          // if (constraint1.symbEq(constraint2)) {

          contained = true;
          break;
        }
      }
      if (!contained) {
        return false;
      }
    }

    //Util.Debug("contains query " + other + "?" + contained);
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
    for (PointsToEdge edge : toRemove) constraints.remove(edge);
    // about to do a piecewise jump; we no longer have any reliable produced information
    if (Options.PIECEWISE_EXECUTION) this.produced.clear(); 
  }
  
  @Override
  public void removeAllNonClinitConstraints() {
    List<PointsToEdge> toRemove = new LinkedList<PointsToEdge>();
    for (PointsToEdge edge : constraints) {
      if (!edge.isClinitConstraint()) {
        toRemove.add(edge);
      }
    }
    for (PointsToEdge edge : toRemove) constraints.remove(edge);
    // about to do a piecewise jump; we no longer have any reliable produced information
    this.produced.clear(); 
  }
  
  @Override
  public Map<Constraint, Set<CGNode>> getRelevantNodes() {
    Map<Constraint, Set<CGNode>> constraintRelevantMap = HashMapFactory.make();
    HeapGraph hg = depRuleGenerator.getHeapGraph();
    for (PointsToEdge edge : constraints) {
      
      Set<CGNode> nodes = Util.getRelevantNodesForVar(edge.getSource(), hg);
      // TODO: may not want to do this. this gets gens, but not kills
      // take the intersection--a node must point to both in order to do a write
      nodes.retainAll(Util.getRelevantNodesForVar(edge.getSink(), hg));

      IField field = edge.getFieldRef();
      if (field != null) {
        boolean array = field == AbstractDependencyRuleGenerator.ARRAY_CONTENTS;
        FieldReference fldRef = field.getReference();
        
        List<CGNode> toRemove = new ArrayList<CGNode>(nodes.size());
        for (CGNode node : nodes) {
          boolean found = false;
          for (SSAInstruction instr : node.getIR().getInstructions()) {
            if (!array && instr instanceof SSAPutInstruction) {
              SSAPutInstruction put = (SSAPutInstruction) instr;
              if (put.getDeclaredField().equals(fldRef)) {
                found = true;
                break;
              }
            } else if (array && instr instanceof SSAArrayStoreInstruction) {
              found = true; 
              break;
            }
          }
          // didn't find the field
          if (!found && fldRef != null) {
            toRemove.add(node);
          }
        }
        nodes.removeAll(toRemove);
      } //else Util.Debug("field null for " + edge);
      constraintRelevantMap.put(edge, nodes);
    }
    return constraintRelevantMap;
  }

  @Override
  public Map<Constraint, Set<CGNode>> getModifiersForQuery() {
    CallGraph cg = depRuleGenerator.getCallGraph();
    CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(cg);
    // public Set<CGNode> getMethodsRelevantToQuery() {
    Map<Constraint, Set<CGNode>> constraintModMap = HashMapFactory.make();
    for (PointsToEdge edge : constraints) {
      Set<DependencyRule> producingRules = HashSetFactory.make();
      Set<CGNode> producers = HashSetFactory.make();
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
        } else {
          Assertions.UNREACHABLE();
        }
      } else {
        producingRules.addAll(Util.getProducersForEdge(edge, depRuleGenerator));
      }
      for (DependencyRule rule : producingRules) {
        CGNode producingNode = rule.getNode();
        // if producer is only called by fakeWorldClinit, count it as fakeWorldClinit
        if (Util.isOnlyCalledBy(fakeWorldClinit, producingNode, cg)) producers.add(fakeWorldClinit);
        else producers.add(producingNode);
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
  
  private static boolean isDispatchFeasibleHelper(Set<PointsToEdge> edges, PointerVariable receiver, IClass calleeType, 
                                                  InstanceKey receiverKey, IClassHierarchy cha) {
    // if constraints contain receiver and say that this could not be the callee, no need to drop
    outer:
    for (PointsToEdge edge : edges) {
      if (edge.getSource().equals(receiver)) {
        PointerVariable snk = edge.getSink();
        if (receiverKey != null && !snk.getPossibleValues().contains(receiverKey)) {
          return false;
        }
        for (InstanceKey key : snk.getPossibleValues()) {
          // if the instance key type is a subtype of the declaring class type, this dispatch could happen
          if (cha.isAssignableFrom(calleeType, key.getConcreteType())) {
            break outer;
          }
        }
        // no instance key in the possible values could cause callee to be called 
        Util.Debug("refuted by infeasible dispatch!");
        return false;
      }
      break;
    }
    return true;
  }
  
  @Override
  public boolean isDispatchFeasible(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    // TODO: add context-sensitivity here as well
    if (callee.getMethod().isStatic()) return true;
    
    //Util.Debug("checking feasibility of dispatch call " + callee);
    IClass calleeType = callee.getMethod().getDeclaringClass();
    PointerVariable receiver = Util.makePointerVariable(this.depRuleGenerator.getHeapModel().getPointerKeyForLocal(caller, instr.getReceiver()));
    IClassHierarchy cha = this.depRuleGenerator.getClassHierarchy();
    
    Context context = callee.getContext();
    ContextItem receiverItem = context.get(ContextKey.RECEIVER);
    InstanceKey receiverKey = receiverItem instanceof InstanceKey ? (InstanceKey) receiverItem : null;
    return isDispatchFeasibleHelper(this.constraints, receiver, calleeType, receiverKey, cha) &&
           isDispatchFeasibleHelper(this.produced, receiver, calleeType, receiverKey, cha);
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
      if (Options.DEBUG) Util.Debug("adding receiver constraint " + receiverConstraint);
      // create trivial dependency rule
      DependencyRule rule = new DependencyRule(receiverConstraint, null, new TreeSet<PointsToEdge>(), node, node.getIR()
          .getControlFlowGraph().entry());
      Set<DependencyRule> newRules = isRuleConsistent(rule, unsatCore,
                                                      currentPath.getCurrentNode());
      if (newRules != null) { 
        if (!produced.contains(receiverConstraint))
          this.addConstraint(receiverConstraint);
      } else { // refuted!
        if (Options.DEBUG)
          Util.Debug("refuted by contextual constraints. newRules " + newRules);
        return false;
      }
    }
    
    return true;
  }

  private boolean addConstraint(PointsToEdge constraint) {
    //Util.Debug("adding constraint " + constraint);
    //Thread.dumpStack();
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
  
  @Override
  public List<AtomicPathConstraint> getIndexConstraintsFor(FieldReference fld) {
    return null;
  }
  
  @Override
  public List<IQuery> addPathConstraintFromSwitch(SSASwitchInstruction instr, SSACFG.BasicBlock lastBlock, CGNode currentNode) {
    return IQuery.FEASIBLE;
  }
  
  @Override
  public boolean addPathConstraintFromSwitch(SSAConditionalBranchInstruction switchCase, CGNode currentNode, boolean negated) {
    return true;
  }

  @Override
  public List<DependencyRule> getWitnessList() {
    return witnessList;
  }
  
  @Override
  public AbstractDependencyRuleGenerator getDepRuleGenerator() { 
    return depRuleGenerator;
  }

  @Override
  public boolean containsConstraint(Constraint constraint) {
    if (!(constraint instanceof PointsToEdge))
      return false;
    return this.constraints.contains(constraint);
  }
  
  @Override
  public Set<FieldReference> getFields() {
    Set<FieldReference> fields = HashSetFactory.make();
    for (PointsToEdge edge : this.constraints) {
      fields.addAll(edge.getFields());
    }
    return fields;
  }
  
  @Override
  public void dispose() { }
  
  @Override
  public Iterator<? extends Constraint> constraints() {
    return constraints.iterator();
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

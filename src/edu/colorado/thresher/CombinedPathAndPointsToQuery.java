package edu.colorado.thresher;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.Context;
import com.ibm.wala.ipa.callgraph.ContextItem;
import com.ibm.wala.ipa.callgraph.ContextKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.intset.BitVectorIntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.OrdinalSet;

/**
 * Path and points-to query that share information to make each more precise.
 * 
 * @author sam
 */

public class CombinedPathAndPointsToQuery extends PathQuery {
  
  // special class just to allow us to override methods of PointsToQuery
  private static final class PointsToQueryWrapper extends PointsToQuery {
    private final CombinedPathAndPointsToQuery parent;
    
    public PointsToQueryWrapper(DependencyRule producer, AbstractDependencyRuleGenerator depRuleGenerator, CombinedPathAndPointsToQuery parent) {
      super(producer, depRuleGenerator);
      this.parent = parent;
    }
    
    public PointsToQueryWrapper(PointsToEdge startEdge, AbstractDependencyRuleGenerator depRuleGenerator, CombinedPathAndPointsToQuery parent) {
      super(startEdge, depRuleGenerator);
      this.parent = parent;
    }
    
    PointsToQueryWrapper(Set<PointsToEdge> constraints, Set<PointsToEdge> produced, List<DependencyRule> witnessList,
        AbstractDependencyRuleGenerator depRuleGenerator, CombinedPathAndPointsToQuery parent) {
      super(constraints, produced, witnessList, depRuleGenerator);
      this.parent = parent;
    }
    
    PointsToQueryWrapper(PointsToQuery qry, CombinedPathAndPointsToQuery parent) {
      super(Util.deepCopyPointsToEdgeSet(qry.constraints), Util.deepCopySet(qry.produced), Util.deepCopyList(qry.witnessList), 
            qry.depRuleGenerator);
      this.parent = parent;
    }
    
    @Override
    public boolean isRuleRelevant(DependencyRule rule, IPathInfo currentPath) {
      return super.isRuleRelevant(rule, currentPath) || parent.isRuleRelevantForPathQuery(rule, currentPath); 
    }
    
    @Override 
    Set<DependencyRule> isRuleConsistent(DependencyRule rule, List<PointsToEdge> unsatCore, CGNode currentNode) {
      // isRuleConsistent only refutes based on null constraints, and so we can't always get an absolute refutation
      // here due to the possibility that we read null from a field or produced null via a check cast. thus, we can't 
      // declare an absolute refutation here; instead, say that the feasible case is the one where no rule is applied,
      // which we signify by returning an empty set
      if (!parent.isRuleConsistentWithPathQuery(rule)) {
        PointerVariable lhs = rule.getShown().getSource();
        // should only get inconsistency with path query on local
        //Util.Assert(lhs.isLocalVar());
        // check for presence of rule LHS in pts-to query
        for (PointsToEdge edge : this.constraints) {
          if (lhs.equals(edge.getSource())) {
            // the path query says that lhs -> null, but in the pts-to query, we need lhs -> [non-null value]. refute
            if (Options.DEBUG) Util.Debug("refuted by path/pts-to discrepancy");
            return null;
          }
        }
        if (Options.DEBUG) Util.Debug("rule not consistent with path query, but not in pt-constraints. applying no rules.");
        return Collections.EMPTY_SET;
      }
      return super.isRuleConsistent(rule, unsatCore, currentNode);
    }
    
    public PointsToQueryWrapper deepCopy(CombinedPathAndPointsToQuery parent) {
      return new PointsToQueryWrapper(Util.deepCopyPointsToEdgeSet(constraints), Util.deepCopySet(produced), Util.deepCopyList(witnessList),
          depRuleGenerator, parent);
    }
  }

  final PointsToQueryWrapper pointsToQuery;
  boolean fakeWitness = false;

  public CombinedPathAndPointsToQuery(PointsToEdge startEdge, AbstractDependencyRuleGenerator depRuleGenerator) {
    super(depRuleGenerator);
    this.pointsToQuery = new PointsToQueryWrapper(startEdge, depRuleGenerator, this);
  }
  
  public CombinedPathAndPointsToQuery(DependencyRule producer, AbstractDependencyRuleGenerator depRuleGenerator) {
    super(depRuleGenerator);
    this.pointsToQuery = new PointsToQueryWrapper(producer, depRuleGenerator, this);
  }

  CombinedPathAndPointsToQuery(PointsToQueryWrapper pointsToQuery, PathQuery pathQuery) {
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator, pathQuery.ctx);
    this.pointsToQuery = pointsToQuery.deepCopy(this);
  }
  
  CombinedPathAndPointsToQuery(PointsToQuery ptQuery, PathQuery pathQuery) {
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator, pathQuery.ctx);
    this.pointsToQuery = new PointsToQueryWrapper(ptQuery, this);
  }
  
  CombinedPathAndPointsToQuery(PathQuery pathQuery) {
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator, pathQuery.ctx);
    Set<PointsToEdge> ptConstraints = HashSetFactory.make();
    Set<PointsToEdge> ptProduced = HashSetFactory.make();
    this.pointsToQuery = new PointsToQueryWrapper(ptConstraints, ptProduced, new ArrayList<DependencyRule>(),
        pathQuery.depRuleGenerator, this);
  }
  
  CombinedPathAndPointsToQuery(CombinedPathAndPointsToQuery query) {
    super(query.constraints, query.pathVars, query.witnessList, query.depRuleGenerator, query.ctx);
    this.pointsToQuery = query.pointsToQuery;
  }

  /**
   * @return true if the query has been successfully witnessed, false otherwise
   */
  public boolean foundWitness() {
    return fakeWitness || (super.foundWitness() && pointsToQuery.foundWitness());
  }

  @Override
  public CombinedPathAndPointsToQuery deepCopy() {
    return new CombinedPathAndPointsToQuery(pointsToQuery, super.deepCopy());
  }

  @Override
  public boolean isFeasible() {
    return super.isFeasible() && pointsToQuery.isFeasible();
  }

  @Override
  public void intersect(IQuery other) {
    Util.Assert(other instanceof CombinedPathAndPointsToQuery, "Not sure how to deal with query type " + other.getClass());
    CombinedPathAndPointsToQuery query = (CombinedPathAndPointsToQuery) other;
    super.intersect((PathQuery) query);
  }

  @Override
  public List<IQuery> visitPhi(SSAPhiInstruction instr, int phiIndex, IPathInfo currentPath) {
    Util.Pre(currentPath.query == this);
    List<IQuery> pathResults = super.visitPhi(instr, phiIndex, currentPath);
    if (pathResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    List<IQuery> ptResults = pointsToQuery.visitPhi(instr, phiIndex, currentPath);
    if (ptResults == IQuery.INFEASIBLE)
      return IQuery.INFEASIBLE;
    Util.Debug("CONS " + this.toString());
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }
  
  @Override
  public boolean visit(SSAInstanceofInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.depRuleGenerator.getHeapModel());
    if (pathVars.contains(lhsVar)) {
      boolean negated = false, found = false;
      // find the constraint and see if it's negated or not
      for (AtomicPathConstraint constraint : this.constraints) {
        if (constraint.getVars().contains(lhsVar) && constraint.getLhs() instanceof SimplePathTerm &&
            constraint.getRhs() instanceof SimplePathTerm && (constraint.getLhs().isIntegerConstant() ||
            constraint.getRhs().isIntegerConstant())) {
            if (constraint.getOp() == ConditionalBranchInstruction.Operator.EQ) {
              // constraint is "!(checkedVar instanceof type)"
              negated = true;
            } else if (constraint.getOp() == ConditionalBranchInstruction.Operator.NE) {
              // constraint is "checkedVar instanceof type"
              negated = false;
            } else Util.Unimp("bad case");
            found = true;
            break;
        }
      }
      Util.Assert(found, "couldn't find relevant constraint!");
      
      ClassHierarchy cha = this.depRuleGenerator.getClassHierarchy();
      // instruction is lhsVar = instanceof checkedVar
      // get local whose type we checked
      PointerVariable checkedVar = new ConcretePointerVariable(node, instr.getUse(0), this.depRuleGenerator.getHeapModel());
      // see what the local var points to according to the points-to query
      PointerVariable rhsVar = this.pointsToQuery.getPointedTo(checkedVar);
      
      Set<InstanceKey> oldKeys;
      if (rhsVar == null) {
        Util.Debug("var " + checkedVar + " not in pts-to constraints... looking it up");
        // checkedVar not in the points-to query; find it in the pointer analysis and get its possible values
        oldKeys = HashSetFactory.make();
        Iterator<Object> succs = this.getDepRuleGenerator().getHeapGraph().getSuccNodes(checkedVar.getInstanceKey());
        while (succs.hasNext()) {
          Object key = succs.next();
          Util.Assert(key instanceof InstanceKey);
          oldKeys.add((InstanceKey) key);
        }
        Util.Assert(!oldKeys.isEmpty());
        // add checkedVar -> possibleValues edge to points-to constraints.
        // no need to check feasability here. since we know checkedVar wasn't an lhs before, this can't cause a refutation
        this.pointsToQuery.constraints.add(new PointsToEdge(checkedVar, SymbolicPointerVariable.makeSymbolicVar(oldKeys)));
      } else {
        // look inside rhsVar and grab the instance keys that are of the required type
        oldKeys = rhsVar.getPossibleValues();
      }
      
      // get the class for the type we checked against 
      TypeReference type = instr.getCheckedType();
      IClass checkedType = cha.lookupClass(type);
      Set<InstanceKey> newKeys = HashSetFactory.make();
      for (InstanceKey key : oldKeys) {
        Util.Debug("key " + key);
        if (cha.isAssignableFrom(checkedType, key.getConcreteType())) {
          if (!negated) {
            newKeys.add(key);
          }
        } else {
          if (negated) {
            Util.Debug("adding key " + key);
            newKeys.add(key);
          }
        }
      }
      
      if (newKeys.isEmpty()) {
        // if none of the keys are of the required type, the instanceof evaluates to false  
        if (negated) this.substituteExpForVar(new SimplePathTerm(1), lhsVar);
        else this.substituteExpForVar(new SimplePathTerm(0), lhsVar);
      } else {
        // if one or more of the keys is of the required type, the instanceof evaluates to true
        if (negated) this.substituteExpForVar(new SimplePathTerm(0), lhsVar);
        else this.substituteExpForVar(new SimplePathTerm(1), lhsVar);
      }
      // check if substitution made path infeasible
      if (!this.feasible) return false;
      // this constraint didn't give us any additional information about rhsVar; no need to narrow
      if (newKeys.size() == 0 ||
          newKeys.size() == oldKeys.size()) return true;
      
      // else, we have to create a new pts-to constraint based on newKeys
      Set<PointsToEdge> ptConstraints = this.pointsToQuery.constraints;
      PointsToEdge toRemove = null;
      for (PointsToEdge edge : ptConstraints) {
        if (edge.getSource().equals(checkedVar)) {
          toRemove = edge;
          break;
        }
      }
      if (toRemove != null) ptConstraints.remove(toRemove);
      ptConstraints.add(new PointsToEdge(checkedVar, SymbolicPointerVariable.makeSymbolicVar(newKeys)));
    }
    return true;
  }
  

  @Override
  boolean visit(SSANewInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable local = new ConcretePointerVariable(node, instr.getDef(), this.depRuleGenerator.getHeapModel());
    if (pathVars.contains(local)) {
      // special case for arrays
      if (instr.getNewSite().getDeclaredType().isArrayType()) { 
        // may need to update path constraints with the length of this array
        SimplePathTerm arrLength;
        if (tbl.isConstant(instr.getUse(0))) {
          arrLength = new SimplePathTerm(tbl.getIntValue(instr.getUse(0)));
        } else {
          arrLength = new SimplePathTerm(new ConcretePointerVariable(node, instr.getUse(0), this.depRuleGenerator.getHeapModel()));
        }
        substituteExpForFieldRead(arrLength, local, SimplePathTerm.LENGTH);
      }

      InstanceKey key = depRuleGenerator.getHeapModel().getInstanceKeyForAllocation(node, instr.getNewSite());
      if (key != null) {
        PointerVariable newVar = Util.makePointerVariable(key);
        substituteExpForVar(new SimplePathTerm(newVar), local);
      }
      return isFeasible();
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) {
    Util.Pre(currentPath.query == this);
    List<IQuery> ptResults = pointsToQuery.visit(instr, currentPath);
    if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    if (Options.DEBUG) Util.Debug("CONS " + this.toString());

    List<IQuery> pathResults = super.visit(instr, currentPath);
    if (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  @Override
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    Util.Pre(currentPath.query == this);
    List<IQuery> ptResults = pointsToQuery.enterCall(instr, callee, currentPath);
    if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    Util.Assert(ptResults.isEmpty(), "Unimp: handling case splits at calls!");
    List<IQuery> pathResults = super.enterCall(instr, callee, currentPath);
    if (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  /**
   * if we are entering a call from a jump, we cannot do parameter binding
   * directly, as we do normally instead, we must be a a bit more clever and use
   * the dependency rules to help us make relevant bindings
   */
  @Override
  public void enterCallFromJump(CGNode callee) { 
    int[] params = callee.getIR().getParameterValueNumbers();
    HeapModel hm = this.depRuleGenerator.getHeapModel();
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    MutableIntSet bound = new BitVectorIntSet();
    for (int i = 0; i < params.length; i++) { // for each parameter
      PointerKey key = hm.getPointerKeyForLocal(callee, params[i]);
      PointerVariable param = new ConcretePointerVariable(callee, params[i], this.depRuleGenerator.getHeapModel());
      Iterator<Object> succs = hg.getSuccNodes(key);
      while (succs.hasNext()) { // for each object this parameter might point to
        Object succ = succs.next();
        PointerVariable paramPointedTo = Util.makePointerVariable(succ);
        PointsToEdge producedEdge = new PointsToEdge(param, paramPointedTo);
        
        List<PointsToEdge> ptConstraintsToRemove = new ArrayList(1);
        List<PointsToEdge> ptConstraintsToAdd = new ArrayList(1);
        
        for (PointsToEdge edge : pointsToQuery.constraints) {
          if (edge.getSource().symbEq(paramPointedTo)) {
            
            if (edge.getSource().isSymbolic()) {
              // instantiate source with concrete value of paramPointedTo   
              ptConstraintsToRemove.add(edge);
              ptConstraintsToAdd.add(new PointsToEdge(paramPointedTo, edge.getSink(), edge.getField()));
            }

            if (pointsToQuery.produced.add(producedEdge)) {
              boolean added = bound.add(params[i]);
              Util.Assert(added, "more than one binding for v" + params[i] + Util.printCollection(pointsToQuery.produced));
            }
          } 
        }
        
        for (PointsToEdge edge : ptConstraintsToRemove) pointsToQuery.constraints.remove(edge);
        for (PointsToEdge edge : ptConstraintsToAdd) pointsToQuery.constraints.add(edge);
        
        
        if (this.pathVars.contains(paramPointedTo)) {
          Util.Debug("path vars have " + paramPointedTo);
          if (pointsToQuery.produced.add(producedEdge)) {
            //substituteExpForVar(new SimplePathTerm(param), paramPointedTo);
            boolean added = bound.add(params[i]);
            Util.Assert(added, "more than one binding for v" + params[i] + Util.printCollection(pointsToQuery.produced)); 
          } // else, substitution will occur later
        }
      }
    }
    
    // if params were bound, they will be in the produced set. apply these param bindings to the path constraints
    for (PointsToEdge constraint : pointsToQuery.produced) {
      if (this.pathVars.contains(constraint.getSink())) {
        Util.Debug("doing sub for " + constraint.getSink());
        substituteExpForVar(new SimplePathTerm(constraint.getSource()), constraint.getSink());
      }
    }
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
    Util.Print("returning from call; query is " + this);
    Util.Pre(currentPath.query == this);
    List<IQuery> ptResults = pointsToQuery.returnFromCall(instr, callee, currentPath);
    if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
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
          combinedQuery.add(new CombinedPathAndPointsToQuery((PointsToQueryWrapper) ptQuery.deepCopy(), (PathQuery) pathQuery.deepCopy()));
        }
      }
    } else if (!pathEmpty) {
      for (IQuery pathQuery : pathQueries) {
        combinedQuery.add(new CombinedPathAndPointsToQuery(pointsToQuery, (PathQuery) pathQuery.deepCopy()));
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
    Util.Pre(currentPath.query == this);
    return pointsToQuery.addContextualConstraints(node, currentPath) && super.addContextualConstraints(node, currentPath);
  }

  @Override
  public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) {
    return pointsToQuery.isCallRelevant(instr, caller, callee, cg)
        || this.doesCallWriteToHeapLocsInPathConstraints(instr, caller, callee, cg);
  }

  @Override
  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    if (!Options.LOOP_INVARIANT_INFERENCE) pointsToQuery.removeLoopProduceableConstraints(loopHead, currentNode);
    // we only need to remove path constraints produceable in the loop... we don't want to remove
    // pts-to constraints; we are computing a fixed point over those
    dropPathConstraintsWrittenInLoop(loopHead, currentNode);
  }

  @Override
  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    Util.Unimp("don't call this");
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
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee, boolean dropPtConstraints) {
    if (dropPtConstraints) this.pointsToQuery.dropConstraintsProduceableInCall(instr, caller, callee, dropPtConstraints);
    this.dropPathConstraintsProduceableByCall(instr, caller, callee);
    if (this.foundWitness()) Util.Debug("dropping constraints led to FAKE witness!");
  }

  void dropConstraintsProuceableByRuleSet(Set<DependencyRule> rules) {
    Set<PointerVariable> toDrop = HashSetFactory.make(); //new HashSet<PointerVariable>();
    Set<PointerVariable> relevantVars = HashSetFactory.make();// new HashSet<PointerVariable>();
    for (PointerVariable var : this.pathVars) {
      if (!var.isLocalVar())
        relevantVars.add(var);
      else { // this is a local
        // try to use pts-to constraints to determine which heap loc this local corresponds to
        PointerVariable pointedTo = this.pointsToQuery.getPointedTo(var);
        if (pointedTo == null) {
          // can't find this var in our points-to constraints; no telling what it might point to. must drop it.
          toDrop.add(var);
        }
        relevantVars.add(pointedTo);
      }
    }
    for (PointerVariable var : toDrop) dropConstraintsContaining(var);
    relevantVars.removeAll(toDrop);

    Set<AtomicPathConstraint> toRemove = HashSetFactory.make();
    for (AtomicPathConstraint constraint : this.constraints) {
      Set<PointerVariable> vars = constraint.getVars();
      Set<FieldReference> fields = constraint.getFields();
      // see if a dependency rules can write to one of the heap loc's in the path constraints
      for (DependencyRule rule : rules) {
        PointerVariable src = rule.getShown().getSource(); 
        if (vars.contains(src))
          toRemove.add(constraint);
        if (rule.getShown().getFieldRef() != null && fields.contains(rule.getShown().getFieldRef().getReference()))
          toRemove.add(constraint);
      }
    }
    for (AtomicPathConstraint constraint : toRemove) {
      if (Options.DEBUG) Util.Debug("dropping constraint produceable by rule set" + constraint);
      removeConstraint(constraint);
    }
    super.rebuildZ3Constraints();
  }
  

  private void dropPathConstraintsWrittenInLoop(SSACFG.BasicBlock loopHead, CGNode node) {
    if (this.constraints.isEmpty()) return;
    
    CallGraph cg = depRuleGenerator.getCallGraph();
    for (SSAInstruction instr : WALACFGUtil.getInstructionsInLoop(loopHead, node.getIR())) {
      if (instr instanceof SSAInvokeInstruction) {
        SSAInvokeInstruction invoke = (SSAInvokeInstruction) instr;
        for (CGNode callee : cg.getPossibleTargets(node, invoke.getCallSite())) {
          // seems to slow things down?
          //dropConstraintsProduceableInCall(invoke, node, callee, false);
          dropConstraintsProduceableInCall(invoke, node, callee, true);
        }
      } else if (instr instanceof SSAPutInstruction) {
        SSAPutInstruction put = (SSAPutInstruction) instr;
        if (put.isStatic()) {
          IField staticField = depRuleGenerator.getCallGraph().getClassHierarchy().resolveField(put.getDeclaredField());
          if (staticField == null) { // TODO: this shouldn't happen, but it sometimes does
            continue;
          }
          PointerVariable staticFieldVar = Util.makePointerVariable(depRuleGenerator.getHeapModel().getPointerKeyForStaticField(
              staticField));
          if (pathVars.contains(staticFieldVar)) {
            dropConstraintsContaining(staticFieldVar);
          }
        } else {
          PointerVariable varName = new ConcretePointerVariable(node, instr.getUse(0), this.depRuleGenerator.getHeapModel()); 
          if (pathVars.contains(varName)) {
            dropConstraintsContaining(varName);
          }
        }
      } else if (instr.hasDef()) {
        PointerVariable var = new ConcretePointerVariable(node, instr.getDef(), this.depRuleGenerator.getHeapModel());
        if (this.pathVars.contains(var)) {
          dropConstraintsContaining(var);
        }
      }
    }
  }

  void dropPathConstraintsProduceableByCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    ConcretePointerVariable retval = null;
    if (instr.hasDef()) {
      retval = new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.getHeapModel());
      dropConstraintsContaining(retval);
    }
    // a null callee means we're dropping constraints for a call that resolves to 0 call sites (so only need
    // to drop retval)
    if (callee == null) return;
   
    List<AtomicPathConstraint> toDrop = new LinkedList<AtomicPathConstraint>();
    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerKey key : constraint.getPointerKeys(depRuleGenerator)) {
        if (keys.contains(key)) {
          toDrop.add(constraint);
          break;
        }
      }
    }
    for (AtomicPathConstraint dropMe : toDrop) {
      removeConstraint(dropMe); 
    }
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
        // constraints contain a non-constant param that's passed to this function; possibly relevant
        if (this.pathVars.contains(arg)) return true; 
      }
    }
    
    // does this call modify our path constraints according to its precomputed mod set?
    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerKey key : constraint.getPointerKeys(depRuleGenerator)) {
      if (keys.contains(key)) return true; // mod set says yes
        if (key instanceof StaticFieldKey) {
          IClass declaringClass = ((StaticFieldKey) key).getField().getDeclaringClass();
          // if this is a <clinit>, might initialize field to default values
          return declaringClass.equals(callee.getMethod().getDeclaringClass())
              && (callee.getMethod().isClinit());
        } 
      }
    }

    return false;
  }

  @Override
  public void removeAllLocalConstraints() {
    // IMPORTANT! must do this first, otherwise we lose the local pts-to info!
    this.removeAllLocalPathConstraints(); 
    pointsToQuery.removeAllLocalConstraints();
  }

  /**
   * take advantage of pts-to information to sub out locals for their heap
   * value, if known
   */
  public void removeAllLocalPathConstraints() {
    // first, sub out all locals for their corresponding heap locations, if we know them
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

  private Map<Constraint, Set<CGNode>> getModifiersForQueryHelper() {
    CallGraph cg = depRuleGenerator.getCallGraph();
    CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(cg);
    Map<PointerKey, Set<CGNode>> reversedModRef = this.depRuleGenerator.getReversedModRef();
    Map<Constraint, Set<CGNode>> constraintModMap = HashMapFactory.make();//new HashMap<Constraint, Set<CGNode>>();
    for (AtomicPathConstraint constraint : this.constraints) {
      Set<CGNode> nodes = HashSetFactory.make();
      addInitsForConstraintFields(constraint, nodes);
      addClassInitsForStaticFields(constraint, nodes);
      // if it may write to the constraint
      for (PointerKey key : constraint.getPointerKeys(depRuleGenerator)) {
        Set<CGNode> modRefNodes = reversedModRef.get(key);
        // this can happen when var is the this param for a class with no fields
        if (modRefNodes == null) continue;
        for (CGNode node : modRefNodes) {
          // add to mapping *only* if node modifies pointer key directly (not via callees)
          // this is because the use of the reversed mod/ref is to jump directly to
          // the node that might modify our key of interest
          if (Util.writesKeyLocally(node, key, this.depRuleGenerator.getHeapModel(), 
              this.depRuleGenerator.getHeapGraph(), this.depRuleGenerator.getClassHierarchy())) {
            // if producer is only called by fakeWorldClinit, count it as fakeWorldClinit
            if (Util.isOnlyCalledBy(fakeWorldClinit, node, cg)) nodes.add(fakeWorldClinit);
            else nodes.add(node);
          }
        }
      }
      constraintModMap.put(constraint, nodes);
    }
    return constraintModMap;
  }
  
  private void addInitsForConstraintFields(AtomicPathConstraint constraint, Set<CGNode> nodes) {
    for (PointerKey key : constraint.getPointerKeys(depRuleGenerator)) {
      Set<PointerVariable> constraintVars = constraint.getVars();
      if (key instanceof InstanceFieldKey) {
        IField fieldKey = ((InstanceFieldKey) key).getField(); 
        for (IMethod method : fieldKey.getDeclaringClass().getDeclaredMethods()) {
          if (method.isInit()) {
            Set<CGNode> initNodes = this.depRuleGenerator.getCallGraph().getNodes(method.getReference());
            for (CGNode initNode : initNodes) {
              // use context information to prevent adding nodes from different contexts
              Context context = initNode.getContext();
              ContextItem receiver = context.get(ContextKey.RECEIVER);
              if (receiver instanceof InstanceKey) {
                InstanceKey receiverKey = (InstanceKey) receiver;
                PointerVariable var = Util.makePointerVariable(receiverKey);
                if (constraintVars.contains(var)) nodes.add(initNode);
              }
            }
          }
        }
      }
    }
  }
  
  public boolean isRuleRelevantForPathQuery(DependencyRule rule, IPathInfo currentPath) {
    List<PointsToEdge> edges = new ArrayList<PointsToEdge>(3);
    edges.add(rule.getShown());
    //edges.addAll(rule.getToShow());
    for (PointsToEdge edge : edges) {
      if (this.pathVars.contains(edge.getSource())) {
        return true;
      }
    
      if (edge.getSink().isSymbolic()) {
        SymbolicPointerVariable symb = (SymbolicPointerVariable) edge.getSink();
        for (PointerVariable var : pathVars) {
          if (symb.symbContains(var)) {
            return true;
          }
        }
      } else if (this.pathVars.contains(edge.getSink())) {
        return true;
      } 
      //Util.Assert(!this.toString().contains(edge.getSink().toString()), "problem getting relevance of " + edge + " to " + this);
    }
    return false;
  }
  
  public boolean isRuleConsistentWithPathQuery(DependencyRule rule) {
    PointerVariable src = rule.getShown().getSource();
    if (pathVars.contains(src)) {
      // check for a constraint of the form src == null
      for (AtomicPathConstraint constraint : this.constraints) {
        if (constraint.isNullConstraintFor(rule.getShown())) return false;
      }
    }
    return true;
  }

  /**
   * add the class init for each field to the set of relevant nodes. need to do
   * this because class inits can write to fields by writing their default
   * values. this implicit write is not reflected in the normal mod/ref analysis
   * 
   * @param constraint
   * @param nodes
   */
  
  private void addClassInitsForStaticFields(AtomicPathConstraint constraint, Set<CGNode> nodes) {
    Util.Debug("adding clinits for constraint " + constraint); 
    for (PointerKey key : constraint.getPointerKeys(depRuleGenerator)) {
      // if we have any static fields, need to consider running the class initializer for the class
      // that declares the static field, since it may write to the field.
      if (key instanceof StaticFieldKey) {
        CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(depRuleGenerator.getCallGraph());
        nodes.add(fakeWorldClinit);
        break;
        /*
        IField fieldKey = ((StaticFieldKey) key).getField();
        IMethod clinit= fieldKey.getDeclaringClass().getClassInitializer();
        if (clinit == null) continue;
        Util.Debug("classInit is " + clinit); 
        // TODO: if class init is null, need to consider initializing static fields to default values
        MethodReference classInit = fieldKey.getDeclaringClass().getClassInitializer().getReference();
        Set<CGNode> classInitNodes = this.depRuleGenerator.getCallGraph().getNodes(classInit);
        Util.Assert(classInitNodes.size() == 1); // should only be one class init
        nodes.add(classInitNodes.iterator().next());
        */
      }
    } 
  }
  

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
    if (!(other instanceof CombinedPathAndPointsToQuery)) {
      return false;
    }
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

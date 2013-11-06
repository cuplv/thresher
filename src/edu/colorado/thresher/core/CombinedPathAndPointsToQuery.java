package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
import com.ibm.wala.ipa.callgraph.propagation.ConcreteTypeKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSALoadMetadataInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
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
  public static final class PointsToQueryWrapper extends PointsToQuery {
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

  public final PointsToQueryWrapper pointsToQuery;
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
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator, pathQuery.ctx, pathQuery.solver);
    this.pointsToQuery = pointsToQuery.deepCopy(this);
  }
  
  CombinedPathAndPointsToQuery(PointsToQuery ptQuery, PathQuery pathQuery) {
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator, pathQuery.ctx, pathQuery.solver);
    this.pointsToQuery = new PointsToQueryWrapper(ptQuery, this);
  }
  
  CombinedPathAndPointsToQuery(PathQuery pathQuery) {
    super(pathQuery.constraints, pathQuery.pathVars, pathQuery.witnessList, pathQuery.depRuleGenerator, pathQuery.ctx, pathQuery.solver);
    Set<PointsToEdge> ptConstraints = HashSetFactory.make();
    Set<PointsToEdge> ptProduced = HashSetFactory.make();
    this.pointsToQuery = new PointsToQueryWrapper(ptConstraints, ptProduced, new ArrayList<DependencyRule>(),
        pathQuery.depRuleGenerator, this);
  }
  
  CombinedPathAndPointsToQuery(CombinedPathAndPointsToQuery query) {
    super(query.constraints, query.pathVars, query.witnessList, query.depRuleGenerator, query.ctx, query.solver);
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
    if (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    List<IQuery> ptResults = pointsToQuery.visitPhi(instr, phiIndex, currentPath);    
    
    if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;    		
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }
  
  @Override
  boolean visitStaticPut(SSAPutInstruction instr, CGNode node, SymbolTable tbl) {
    if (!super.visitStaticPut(instr, node, tbl)) return false;
    PointerVariable localVar = new ConcretePointerVariable(node, instr.getUse(0), depRuleGenerator.getHeapModel());
    PointerVariable heapVal = this.pointsToQuery.getPointedTo(localVar, false);
    if (pathVars.contains(heapVal)) {
      // do substitution
      substituteExpForVar(new SimplePathTerm(localVar), heapVal);
      return isFeasible();
    }
    return true;
  }
  
  @Override
  boolean visit(SSAGetInstruction instr, CGNode node) {
    Util.Assert(instr.getNumberOfDefs() == 1, "Expecting only 1 def!");
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {
      SimplePathTerm toSub = null;
      if (instr.isStatic()) { // static field get
        IField staticField = depRuleGenerator.getCallGraph().getClassHierarchy().resolveField(instr.getDeclaredField());

        // TODO: support this somehow
        if (staticField == null) {
          Util.Assert(instr.getDeclaredField().getFieldType().isPrimitiveType());
          if (Options.DEBUG) Util.Debug("getstatic for field of primitive type? " + instr.getDeclaredField() + " dropping related constraints");
          dropConstraintsContaining(varName);
          return true;
        }
        
        PointerKey key = depRuleGenerator.getHeapModel().getPointerKeyForStaticField(staticField);
        PointerVariable var = Util.makePointerVariable(key);
        
        PointerVariable pointedTo = this.pointsToQuery.getPointedTo(var, false);
        if (pointedTo != null) {
          toSub = new SimplePathTerm(pointedTo);  
        } else {
          toSub = new SimplePathTerm(var);  
        }
      } else { // non-static get
        PointerVariable objRead = makeVarFromUse(node, instr.getUse(0));
        //PointerVariable pointedTo = this.pointsToQuery.getPointedTo(objRead);
        //if (pointedTo != null) {
          //toSub = new SimplePathTerm(pointedTo, instr.getDeclaredField());  
        //} else {
          toSub = new SimplePathTerm(objRead, instr.getDeclaredField());  
        //}
      }
      substituteExpForVar(toSub, varName);
      if (isFeasible()) {
        List<AtomicPathConstraint> toRemove = new ArrayList<AtomicPathConstraint>();
        // look through the constraints and see if we just added a constraint that can be converted to a points-to constraint
        for (AtomicPathConstraint constraint : this.constraints) {
          if (constraint.isPointsToConstraint()) {
            toRemove.add(constraint);
          }
        }
        for (AtomicPathConstraint removeMe : toRemove) {
          PointsToEdge edge = removeMe.makePointsToEdge(this.depRuleGenerator.getHeapGraph());
          DependencyRule rule = 
              Util.makeUnconditionalDependencyRule(edge, instr, PointerStatement.EdgeType.GetField, -1, -1, node);
          // remove this constraint from the path constraints and add it to the points-to constraints.
          if (pointsToQuery.isRuleConsistent(rule, pointsToQuery.unsatCore, node) != null) {
            if (Options.DEBUG) Util.Debug("adding edge " + edge + " from path constraints");
            this.pointsToQuery.constraints.add(edge);
            this.constraints.remove(removeMe);
          } else {
            if (Options.DEBUG) Util.Debug("refuting by merging pts-to and path constraints!");
            return false;
          }
        }
        return true;
      }
      return false;
    }
    return true; // didn't add any constraints, can't be infeasible
  }
  
  @Override
  public boolean visit(SSALoadMetadataInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(lhsVar)) {
      if (Util.isClassMetadataGetter(instr)) {
        // this instruction is lhsVar = something.class
        TypeReference ref = (TypeReference) instr.getToken();
        IClass clazz = this.depRuleGenerator.getClassHierarchy().lookupClass(ref);
        PointerVariable typeVar = Util.makePointerVariable(new ConcreteTypeKey(clazz));
        substituteExpForVar(new SimplePathTerm(typeVar), lhsVar);
        return isFeasible();
      } else {
        Util.Assert(false, "unsupported metatadata instruction " + instr + " " + node.getIR());
        dropConstraintsContaining(lhsVar);
      }
    }
    return true;
  }
  
  @Override
  public boolean visit(SSAInstanceofInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
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
      PointerVariable checkedVar = new ConcretePointerVariable(node, instr.getUse(0), this.heapModel);
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
        
        if (oldKeys.isEmpty()) {
          // points-to set is empty, so var must be null
          // add null constraint
          this.constraints.add(new AtomicPathConstraint(new SimplePathTerm(checkedVar), 
                               SimplePathTerm.NULL, ConditionalBranchInstruction.Operator.EQ));
        } else {
          // add checkedVar -> possibleValues edge to points-to constraints.
          // no need to check feasibility here. since we know checkedVar wasn't an lhs before, this can't cause a refutation
          this.pointsToQuery.constraints.add(new PointsToEdge(checkedVar, SymbolicPointerVariable.makeSymbolicVar(oldKeys)));
        }
      } else {
        // look inside rhsVar and grab the instance keys that are of the required type
        oldKeys = rhsVar.getPossibleValues();
      }
      
      // get the class for the type we checked against 
      TypeReference type = instr.getCheckedType();
      IClass checkedType = cha.lookupClass(type);
      Set<InstanceKey> newKeys = HashSetFactory.make();
      for (InstanceKey key : oldKeys) {
        if (cha.isAssignableFrom(checkedType, key.getConcreteType())) {
          if (!negated) {
            newKeys.add(key);
          }
        } else {
          if (negated) {
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
    PointerVariable local = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    InstanceKey allocatedKey = null;
    try {
      allocatedKey = this.heapModel.getInstanceKeyForAllocation(node, instr.getNewSite());
    } catch (NullPointerException e) {} // hack to get around WALA bug -- see AbstractDependencyRuleGenerator for descripton
    if (allocatedKey == null) { // this can happen due to exclusions
      if (Options.DEBUG) Util.Debug("can't find key for allocation instr " + instr);
      dropConstraintsContaining(local);
      return true;
    }
    PointerVariable allocated = Util.makePointerVariable(allocatedKey);
    PointerVariable subFor = null;
    if (pathVars.contains(local)) subFor = local;
    else if (pathVars.contains(allocated)) subFor = allocated;
    if (subFor != null) {
      // special case for arrays
      if (instr.getNewSite().getDeclaredType().isArrayType()) { 
        // may need to update path constraints with the length of this array
        SimplePathTerm arrLength;
        if (tbl.isConstant(instr.getUse(0))) {
          arrLength = new SimplePathTerm(tbl.getIntValue(instr.getUse(0)));
        } else {
          arrLength = new SimplePathTerm(new ConcretePointerVariable(node, instr.getUse(0), this.heapModel));
        }
        substituteExpForFieldRead(arrLength, subFor, SimplePathTerm.LENGTH);
      }

      InstanceKey key = depRuleGenerator.getHeapModel().getInstanceKeyForAllocation(node, instr.getNewSite());
      if (key != null) {
        PointerVariable newVar = Util.makePointerVariable(key);
        substituteExpForVar(new SimplePathTerm(newVar), local);
      }
      
      if (Options.INDEX_SENSITIVITY) {        
        final SimplePathTerm DEFAULT_ARR_VAL = new SimplePathTerm(0);
        // initialize all array fields to default values
        if (instr.getNewSite().getDeclaredType().isArrayType()) {
          if (Options.DEBUG) Util.Debug("initializing array indices to default vals.");
          List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
          List<SimplePathTerm> toSub = new LinkedList<SimplePathTerm>();
          InstanceKey arrRef = this.depRuleGenerator.getHeapModel().getInstanceKeyForAllocation(node, instr.getNewSite());
          for (AtomicPathConstraint constraint : this.constraints) {
            for (SimplePathTerm term : constraint.getTerms()) {
              if (term.getObject() != null && term.getObject().getInstanceKey() != null && term.getObject().getInstanceKey().equals(arrRef)) {
                Util.Assert(term.getFirstField() != null);
                // remove constraints on index value
                PointerVariable indexName = new ConcretePointerVariable(term.getFirstField().getName().toString());
                toRemove.addAll(this.getConstraintsWithVar(indexName, false));
                // assign to default value
                //substituteExpForFieldRead(DEFAULT_ARR_VAL, term.getObject(), term.getFirstField());
                toSub.add(term);
              }
            }
          }
          for (AtomicPathConstraint removeMe : toRemove) this.constraints.remove(removeMe);
          for (SimplePathTerm term : toSub) substituteExpForFieldRead(DEFAULT_ARR_VAL, term.getObject(), term.getFirstField());
        }
      }            
      return isFeasible();
    }
    return true; // didn't add any constraints, can't be infeasible
  }
  
  boolean visitArrayStoreInternal(SSAArrayStoreInstruction instr, CGNode node, SymbolTable tbl, PointerVariable arrayVar) {
    int storedVal = instr.getValue();
    SimplePathTerm stored;
    if (tbl.isConstant(storedVal)) stored = new SimplePathTerm(tbl.getIntValue(storedVal));
    else stored = new SimplePathTerm(new ConcretePointerVariable(node, storedVal, this.heapModel));
    
    List<AtomicPathConstraint> arrConstraints = getConstraintsWithVar(arrayVar, true);    
    
    // TODO: generalize this to multiple constraints on arr; not expected for now
    Util.Assert(arrConstraints.size() == 1, "more than one array index constraint on " + arrayVar + " " + arrConstraints.size());
    AtomicPathConstraint arrConstraint = arrConstraints.iterator().next();
    Pair<FieldReference, List<AtomicPathConstraint>> indexPair = getIndexConstraintsFor(arrConstraint);
    FieldReference indexField = indexPair.fst;
    List<AtomicPathConstraint> indexConstraints = indexPair.snd;
    
    if (indexConstraints.isEmpty()) {
      Util.Debug("dropping constraints on " + arrayVar + " because we don't have an expression associated with the array index");
      dropConstraintsContaining(arrayVar);
      return true;
    }
    Util.Assert(indexConstraints.size() == 1, "more or less than 1 index constraint for index expr " + indexConstraints.size());
    AtomicPathConstraint indexConstraint = indexConstraints.iterator().next();
    // compare index constraint to index
    PathTerm indexExpr = indexConstraint.getRhs();
    int instrIndex = instr.getIndex();
    // TODO: check inequality constraints also!
    // TODO: check if rhs is wrong
    if (indexExpr.isIntegerConstant() && tbl.isIntegerConstant(instrIndex)) {
      // both index expression and index of array store instruction are constants. we can determine
      // unambiguously whether this instruction writes to the index of interest
      if (((SimplePathTerm) indexExpr).getIntegerConstant() == tbl.getIntValue(instrIndex)) {
        // yes, it writes to our index. sub out arrayRef[index] for stored and remove the index expression
        // constraint
        //Util.Print("instr " + instr + " does write to index " + indexExpr + ". subbing.");
        removeConstraint(indexConstraint);
        //Util.Unimp("need to extract this to avoid concurrent modification exception");
        substituteExpForFieldRead(stored, arrayVar, indexField);
        //toSub.add(Pair.make(stored, Pair.make(arrayRef, indexField)));
      } // else, it definitely does not write to our index. fall through
    } else {
      // TODO:
      // at least one of the indices is not a constant. we need to fork two cases: one where this
      // instruction does produce our constraint (with an additional equality constraint on the indices)
      // and one where this instruction does not produce our constraint (with an additional inequality 
      // constraint on the indices). we can also ask z3 to prove that it definitely *is* or *isn't* our index?
      Util.Unimp("case split due to ambiguous array write");
    }
    return isFeasible();
  }
  
  @Override
  // TODO: this is too slow--redo with local vars
  boolean visit(SSAArrayStoreInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable arrayVar = new ConcretePointerVariable(node, instr.getArrayRef(), this.heapModel);
    if (Options.INDEX_SENSITIVITY) {
      if (pathVars.contains(arrayVar)) {
        return visitArrayStoreInternal(instr, node, tbl, arrayVar);
      }
      
      List<Pair<SimplePathTerm,PointerVariable>> toSub1 = new LinkedList<Pair<SimplePathTerm,PointerVariable>>();
      List<Pair<SimplePathTerm,Pair<PointerVariable, FieldReference>>> toSub2 = 
          new LinkedList<Pair<SimplePathTerm,Pair<PointerVariable, FieldReference>>>();      
      
      outer:
      for (AtomicPathConstraint constraint : this.constraints) {
        for (SimplePathTerm term : constraint.getTerms()) {
          PointerVariable arrayRef = null;
          if (term.getObject() != null) {            
            if (term.getObject().isLocalVar() && term.getFirstField() != null) {
              PointerVariable localPtr = term.getObject();
              FieldReference fld = term.getFirstField();
              if (isArrayIndexField(fld)) {
                arrayRef = this.pointsToQuery.getPointedTo(localPtr);      
                //if (arrayRef != null) toSub1.add(Pair.make(new SimplePathTerm(arrayRef), localPtr));
                if (arrayRef != null && Util.intersectionNonEmpty(arrayVar.getPointsToSet(this.depRuleGenerator.getHeapGraph()), 
                    arrayRef.getPossibleValues())) {
                  toSub1.add(Pair.make(new SimplePathTerm(arrayVar), localPtr));
                  break outer;
                }
              } else {  
                // sub out local.arrayField for the array ref pointed to by local.arrayField
                arrayRef = this.pointsToQuery.getPointedTo(localPtr, this.depRuleGenerator.getClassHierarchy().resolveField(fld)); 
                //if (arrayRef != null) toSub2.add(Pair.make(new SimplePathTerm(arrayRef), Pair.make(localPtr, fld)));                
                if (arrayRef != null && Util.intersectionNonEmpty(arrayVar.getPointsToSet(this.depRuleGenerator.getHeapGraph()), 
                                                                arrayRef.getPossibleValues())) {
                  toSub2.add(Pair.make(new SimplePathTerm(arrayVar), Pair.make(localPtr, fld)));
                  break outer;
                }
              }                           
            }
          }
        }
      }
      
      for (Pair<SimplePathTerm,PointerVariable> pair : toSub1) {
        //Util.Print("subbing in " + pair.fst + " for " + pair.snd);
        substituteExpForVar(pair.fst, pair.snd);
      }
      for (Pair<SimplePathTerm,Pair<PointerVariable,FieldReference>> pair : toSub2) {
        //Util.Print("subbing in " + pair.fst + " for " + pair.snd.fst + "." + pair.snd.snd);
        substituteExpForFieldRead(pair.fst, pair.snd.fst, pair.snd.snd);
      }

      if (pathVars.contains(arrayVar)) {
        return visitArrayStoreInternal(instr, node, tbl, arrayVar);
      }
      return true;      
    } else {
      if (Options.DEBUG) {
        Util.Debug("we don't handle path queries with arrays precisely; dropping constraints. this arrayStore insruction " + instr
            + " might matter for " + this);
      }
      dropConstraintsContaining(arrayVar);
    }
    return true;
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) {
    Util.Pre(currentPath.query == this);
    List<IQuery> ptResults = pointsToQuery.visit(instr, currentPath);
    if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    if (Options.DEBUG) Util.Debug("CONS " + currentPath);
    
    List<IQuery> pathResults = super.visit(instr, currentPath);
    if (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    Util.Assert(pathResults.isEmpty(), "should never be case splits on path constraints!");

    return combinePathAndPointsToQueries(ptResults, pathResults);
  }
  
  // for now, only BOOLEAN_VALUE_OF; may need more general code later
  public boolean handleStubbedMethod(SSAInvokeInstruction instr, IPathInfo currentPath) {
    Util.Print("handling stub;");
    CGNode caller = currentPath.getCurrentNode();
    substituteExpForVar(new SimplePathTerm(new ConcretePointerVariable(caller, instr.getUse(0), this.depRuleGenerator.hm)),
                        new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.hm));
   return isFeasible();
    
    /*
    if (tbl.isIntegerConstant(instr.getUse(0))) {
      substituteExpForVar(new SimplePathTerm(tbl.getIntValue(instr.getUse(0))), 
                          new ConcretePointerVariable(caller, instr.getDef(), this.depRuleGenerator.hm));
      return isFeasible();
    }*/
    //return true;
   
     //Util.Assert(instr.hasDef() && instr.getNumberOfUses() == 1);
     //PointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.heapModel);
     //PointerVariable receiver = new ConcretePointerVariable(caller, instr.getReceiver(), this.heapModel);
   
  }
  
  private static final MethodReference INT_VALUE = MethodReference.findOrCreate(TypeReference.JavaLangInteger, "intValue", "()I");
  private static final MethodReference BOOLEAN_VALUE = MethodReference.findOrCreate(TypeReference.JavaLangBoolean, "booleanValue", "()Z");
  private static final MethodReference BOOLEAN_VALUE_OF = MethodReference.findOrCreate(TypeReference.JavaLangBoolean, "valueOf", "(Z)Ljava/lang/Boolean");

  // TODO: hack to handle weirdness of boxing and unboxing booleans
  private boolean isStubbedMethod(MethodReference method) { // avoid classLoader matching issues by checking class name and descriptor
    return BOOLEAN_VALUE_OF.getDeclaringClass().getName().equals(method.getDeclaringClass().getName()) &&
    BOOLEAN_VALUE_OF.getSelector().equals(method.getSelector());
  }
  
  @Override
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    Util.Pre(currentPath.query == this);        
    //if (!isStubbedMethod(instr.getDeclaredTarget())) {
      List<IQuery> ptResults = pointsToQuery.enterCall(instr, callee, currentPath);
      if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
      Util.Assert(ptResults.isEmpty(), "Unimp: handling case splits at calls!");
      List<IQuery> pathResults = super.enterCall(instr, callee, currentPath);
      if (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
      return combinePathAndPointsToQueries(ptResults, pathResults);
    //} else {
      //if(!handleStubbedMethod(instr, currentPath)) return IQuery.INFEASIBLE;
      //pointsToQuery.dropConstraintsProduceableInCall(instr, currentPath.getCurrentNode(), callee, true);
     //return IQuery.FEASIBLE;
    //}
  }

  /**
   * if we are entering a call from a jump, we cannot do parameter binding
   * directly, as we do normally instead, we must be a a bit more clever and use
   * the dependency rules to help us make relevant bindings
   */
  @Override
  public void enterCallFromJump(CGNode callee) {
    // TODO: need to do this for path query as well? for non-parameter locals?
    this.pointsToQuery.produced.clear(); // all bets on contents of produced are off
    int[] params = callee.getIR().getParameterValueNumbers();
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    for (int i = 0; i < params.length; i++) { // for each parameter
      PointerVariable param = new ConcretePointerVariable(callee, params[i], this.heapModel);
      Set<InstanceKey> pt = param.getPointsToSet(hg);
      if (!pt.isEmpty()) {
        PointsToEdge toAdd = null;
        PointerVariable paramPT = SymbolicPointerVariable.makeSymbolicVar(pt);
        for (PointsToEdge edge : pointsToQuery.constraints) {
          if (paramPT.symbEq(edge.getSource())) {
            toAdd = new PointsToEdge(param, edge.getSource());
            break;
          }        
        }
        if (toAdd != null) this.pointsToQuery.constraints.add(toAdd);
      }
    }
    /*
    this.pointsToQuery.produced.clear(); // all bets on contents of produced are off
    int[] params = callee.getIR().getParameterValueNumbers();
    HeapModel hm = this.heapModel;
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    MutableIntSet bound = new BitVectorIntSet();
    for (int i = 0; i < params.length; i++) { // for each parameter
      PointerKey key = hm.getPointerKeyForLocal(callee, params[i]);
      PointerVariable param = new ConcretePointerVariable(callee, params[i], this.heapModel);
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
        if (constraint.getSource().isLocalVar()) {
          substituteExpForVar(new SimplePathTerm(constraint.getSource()), constraint.getSink());
        }
      }
    }
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
    Util.Pre(currentPath.query == this);
    List<IQuery> ptResults = pointsToQuery.returnFromCall(instr, callee, currentPath);
    if (ptResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    List<IQuery> pathResults = super.returnFromCall(instr, callee, currentPath);
    if (pathResults == IQuery.INFEASIBLE) return IQuery.INFEASIBLE;
    return combinePathAndPointsToQueries(ptResults, pathResults);
  }

  /**
   * @return - cartesian product of two lists of case splits; one points-to and
   *         one path
   */
  List<IQuery> combinePathAndPointsToQueries(List<IQuery> pointsToQueries, List<IQuery> pathQueries) {
    //boolean ptEmpty = pointsToQueries == IQuery.FEASIBLE, pathEmpty = pathQueries == IQuery.FEASIBLE;
    boolean ptEmpty = pointsToQueries.isEmpty(), pathEmpty = pathQueries.isEmpty();

    List<IQuery> combinedQuery = new LinkedList<IQuery>();
    if (!ptEmpty && !pathEmpty) {
      Util.Unimp("case split in path and points-to");
      // TODO: would need to mix in current query here as well, which would get
      // messy...
      for (IQuery ptQuery : pointsToQueries) {
        for (IQuery pathQuery : pathQueries) {
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
      combinedQuery.add(new CombinedPathAndPointsToQuery(pointsToQuery, super.deepCopy()));
    } else { // ptEmpty && pathEmpty
      return IQuery.FEASIBLE;
    }
    return combinedQuery;
  }

  @Override
  public boolean addContextualConstraints(CGNode node, IPathInfo currentPath) {
    Util.Pre(currentPath.query == this);
    return pointsToQuery.addContextualConstraints(node, currentPath) && addContextualConstraintsForPathQuery(node);
  }
  
  private boolean addContextualConstraintsForPathQuery(CGNode node) {
    Collection<PointerVariable> maySub = new ArrayList<PointerVariable>();
    // find params that might point to one of our heap vars according to the points-to analysis
    for (AtomicPathConstraint constraint : this.constraints) {
      for (PointerVariable var : constraint.getVars()) {
        if (!var.isLocalVar()) {
          maySub.add(var);
        }
      }
    }
    
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    IMethod method = node.getMethod();
    for (int i = 0; i < method.getNumberOfParameters(); i++) {
      if (method.getParameterType(i).isPrimitiveType()) continue;
      PointerVariable param = new ConcretePointerVariable(node, i + 1, this.heapModel);
      Set<InstanceKey> possibleValues = param.getPointsToSet(hg);
      if (possibleValues.isEmpty()) continue;
      for (PointerVariable var : maySub) {
        if (var.getPossibleValues() != null &&
            Util.intersectionNonEmpty(var.getPossibleValues(), possibleValues)) {
          // add points-to edge param -> var and substitute param for var in the path constraints
          this.substituteExpForVar(new SimplePathTerm(param), var);
          /*
          for (PointsToEdge edge : this.pointsToQuery.constraints) {
            Util.Assert(!edge.getSource().equals(param), "pts-to constraints already have " + edge);
          }
          */
        }
      }
    }
    return true;
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
  public boolean isDispatchFeasible(SSAInvokeInstruction instr, CGNode caller, CGNode callee){
    return this.pointsToQuery.isDispatchFeasible(instr, caller, callee) &&
        super.isDispatchFeasible(instr, caller, callee);
  }
  
  @Override
  public void dropReturnValueConstraintsForCall(SSAInvokeInstruction instr, CGNode caller) {
    if (instr.hasDef()) {
      this.pointsToQuery.dropReturnValueConstraintsForCall(instr, caller);
      super.dropReturnValueConstraintsForCall(instr, caller);
    }
  }
  
  @Override
  public void dropConstraintsContaining(Set<PointerVariable> vars) {
    super.dropConstraintsContaining(vars);
    this.pointsToQuery.dropConstraintsContaining(vars);
  }

  @Override
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee, boolean dropPtConstraints) {  
    if (dropPtConstraints) this.pointsToQuery.dropConstraintsProduceableInCall(instr, caller, callee, dropPtConstraints);
    this.dropPathConstraintsProduceableByCall(instr, caller, callee);
    if (this.foundWitness()) Util.Debug("dropping constraints led to FAKE witness!");
  }

  void dropConstraintsProduceableByRuleSet(Set<DependencyRule> rules) {
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
          if (isDispatchFeasible(invoke, node, callee)) {
            // seems to slow things down?
            //dropConstraintsProduceableInCall(invoke, node, callee, false);
            //dropConstraintsProduceableInCall(invoke, node, callee, true);
            dropPathConstraintsProduceableByCall(invoke, node, callee);
          } else if (!this.isFeasible()) return; // path refuted--can return
        }
      } else if (instr instanceof SSAPutInstruction) {
        SSAPutInstruction put = (SSAPutInstruction) instr;
        IField fld = depRuleGenerator.getCallGraph().getClassHierarchy().resolveField(put.getDeclaredField());
        if (fld == null) { // TODO: this shouldn't happen, but it sometimes does
          continue;
        }
        if (put.isStatic()) {
          PointerVariable staticFieldVar = Util.makePointerVariable(depRuleGenerator.getHeapModel().getPointerKeyForStaticField(fld));
          if (pathVars.contains(staticFieldVar)) {
            Util.Debug("dropping constraints with " + staticFieldVar + " due to loop instr " + instr);
            dropConstraintsContaining(staticFieldVar);
          }
        } else {
          PointerVariable varName = new ConcretePointerVariable(node, instr.getUse(0), this.heapModel); 
          if (pathVars.contains(varName)) {
            Util.Debug("dropping constraints with " + varName + " due to loop instr " + instr);
            dropConstraintsContaining(varName, fld);
          }
        }
      } else if (instr.hasDef()) {
        PointerVariable var = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
        if (this.pathVars.contains(var)) {
          Util.Debug("dropping constraints with " + var + " due to loop insr " + instr);
          dropConstraintsContaining(var);
        }
      }
    }
  }

  @Override
  public boolean initializeInstanceFieldsToDefaultValues(CGNode constructor) {
    return super.initializeInstanceFieldsToDefaultValues(constructor) && 
        this.pointsToQuery.initializeInstanceFieldsToDefaultValues(constructor);
  }
  /*
  @Override
  void dropConstraintsContaining(PointerVariable retval) {
    super.dropConstraintsContaining(retval);
    for (PointsToE)
  }*/
  
  void dropPathConstraintsProduceableByCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    ConcretePointerVariable retval = null;
    if (instr.hasDef()) {
      retval = new ConcretePointerVariable(caller, instr.getDef(), this.heapModel);
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
      ConcretePointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.heapModel);
      if (this.pathVars.contains(retval)) {
        Util.Debug("path vars contain retval");
        return true; // constraints contain retval; definitely relevant
      }
    }
    
    IClass calleeClass = callee.getMethod().getDeclaringClass();
    // does this call modify our path constraints according to its precomputed mod set?
    OrdinalSet<PointerKey> keys = this.depRuleGenerator.getModRef().get(callee);
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerKey key : constraint.getPointerKeys(depRuleGenerator)) {
        if (keys.contains(key)) {
          Util.Debug("relevant according to mod set.");
          return true; // mod set says yes
        }
        if (key instanceof StaticFieldKey) {
          IClass declaringClass = ((StaticFieldKey) key).getField().getDeclaringClass();
          // if this is a <clinit>, might initialize field to default values
          if (declaringClass.equals(calleeClass) && (callee.getMethod().isClinit())) {
            Util.Debug("relevant because is clinit and could initialize static field " + key);
            return true;
          }
        } else if (key instanceof InstanceFieldKey) {
          IClass declaringClass = ((InstanceFieldKey) key).getField().getDeclaringClass();
          if (declaringClass.equals(calleeClass) && callee.getMethod().isInit()) {
            Util.Debug("relevant because is init and could initialize field " + key);
            return true;
          }
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
  
  @Override
  public void removeAllNonClinitConstraints() {
    super.removeAllNonClinitConstraints();
    this.pointsToQuery.removeAllNonClinitConstraints();
  }
 
  /**
   * take advantage of pts-to information to sub out locals for their heap
   * value, if known
   * TODO: should also replace with points-to sets if not in constraints. also, do we need to consider aliasing?
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
    
    Set<PointerVariable> ignoreVars = HashSetFactory.make();
    // replace remaining local vars with their pts-to sets, if applicable
    for (AtomicPathConstraint constraint : this.constraints) {
      if (constraint.isEqNullConstraint()) ignoreVars.addAll(constraint.getVars());    
    }
    List<PointerVariable> toReplace = new ArrayList<PointerVariable>();
    for (PointerVariable var : this.pathVars) {
      if (var.isLocalVar() && !ignoreVars.contains(var)) {
        toReplace.add(var);
      }
    }
    
    for (PointerVariable replaceMe : toReplace) {
      PointerVariable newVar = SymbolicPointerVariable.makeSymbolicVar(replaceMe.getInstanceKey(), 
          this.depRuleGenerator.getHeapGraph());
      if (newVar != null) {
        this.substituteExpForVar(new SimplePathTerm(newVar), replaceMe);
      }
    }

    // now, can remove all local constraints
    List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerVariable var : constraint.getVars()) {
        if (var.isLocalVar()) {
          toRemove.add(constraint);
          break;
        }
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
  
  @Override
  public List<IQuery> addPathConstraintFromSwitch(SSASwitchInstruction instr, SSACFG.BasicBlock lastBlock, CGNode currentNode) {
    // don't need to do anything with points-to constraints here
    return super.addPathConstraintFromSwitch(instr, lastBlock, currentNode);
  }

  @Override
  public boolean addPathConstraintFromSwitch(SSAConditionalBranchInstruction switchCase, CGNode currentNode, boolean negated) {
    return super.addPathConstraintFromSwitch(switchCase, currentNode, negated);
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
          if (Util.writesKeyLocally(node, key, this.heapModel, 
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
  public Map<Constraint, Set<CGNode>> getRelevantNodes() {
    Map<Constraint, Set<CGNode>> mods = pointsToQuery.getRelevantNodes();
    mods.putAll(this.getRelevantNodesForPathQuery());
    return mods;
  }
  
  public Map<Constraint, Set<CGNode>> getRelevantNodesForPathQuery() {
    Map<Constraint, Set<CGNode>> constraintRelevantMap = HashMapFactory.make();
    IClassHierarchy cha = this.depRuleGenerator.getClassHierarchy();
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    for (AtomicPathConstraint constraint : this.constraints) {
      Set<CGNode> nodes = HashSetFactory.make();
      for (SimplePathTerm term : constraint.getTerms()) {
        if (!term.isIntegerConstant()) {
          // TODO: how to handle multiple fields?
          // TODO: commenting out for now (which is wrong).
          // will change representation so only one field should occur in path constraints
          //Util.Assert(term.getFields() == null || term.getFields().size() == 1);
          PointerVariable var = term.getObject();
          if (var.isLocalVar()) {
            PointerVariable ptsTo = this.pointsToQuery.getPointedTo(var);
            if (ptsTo != null) {
              var = ptsTo;
            } else { 
              // consult the points-to analysis
              PointerVariable newVar = SymbolicPointerVariable.makeSymbolicVar(var.getInstanceKey(), hg);
              if (newVar != null) var = newVar;
            }
          }
          
          FieldReference field = term.getFirstField();
          if (field != null) {
            IField fld = cha.resolveField(field);
            if (fld == null) Util.Debug("couldn't resolve field " + fld);
            nodes.addAll(Util.getRelevantForFieldWrite(var, fld, hg));
          } else {
            // it's a local. only the current node is relevant
            nodes.add(var.getNode());
          }
        } 
      }
      constraintRelevantMap.put(constraint, nodes);
    }    
    return constraintRelevantMap;
    //return getModifiersForQuery();
  }
  
  @Override
  public Map<Constraint, Set<CGNode>> getModifiersForQuery() {
    Map<Constraint, Set<CGNode>> mods = pointsToQuery.getModifiersForQuery();
    mods.putAll(getModifiersForQueryHelper());
    return mods;
  }
  
  @Override
  public Set<FieldReference> getFields() {
    Set<FieldReference> fields = this.pointsToQuery.getFields();
    fields.addAll(super.getFields());
    return fields;
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
  
  @Override
  public Iterator<? extends Constraint> constraints() {
    List<Constraint> constraints = new ArrayList<Constraint>(this.pointsToQuery.constraints.size() + super.constraints.size());
    for (Constraint constraint : this.pointsToQuery.constraints) {
      constraints.add(constraint);
    }
    for (Constraint constraint : this.constraints) {
      constraints.add(constraint);
    }
    return constraints.iterator();
  }
  
  @Override
  public PointerVariable getPointedTo(PointerVariable var) {
    return this.pointsToQuery.getPointedTo(var);
  }  
  
  public int getNumberOfPathConstraints() {
    return constraints.size();
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

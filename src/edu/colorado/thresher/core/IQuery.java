package edu.colorado.thresher.core;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.types.FieldReference;

public interface IQuery { // extends Comparable {

  // empty list means feasible to the visit() method
  public static final List<IQuery> FEASIBLE = Collections.unmodifiableList(new LinkedList<IQuery>());
  // null means infeasible to the visit() method
  public static final List<IQuery> INFEASIBLE = null;

  /**
   * @return true if the query has been sucessfully witnessed, false otherwise
   */
  public boolean foundWitness();

  /**
   * add a path constraint to the query based on conditional contained in point
   * 
   * @param point
   *          - branch point whose conditional will be used in the constraint
   * @param trueBranchFeasible
   *          - true if the true side of the conditional is feasible, false
   *          otherwise
   * @return true if the query is feasible after adding the constraint, false
   *         otherwise
   */
  public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranchFeasible);
  
  public boolean addConstraintFromConditional(SSAConditionalBranchInstruction instruction, 
      CGNode node, boolean trueBranchFeasible);
  
  public List<IQuery> addPathConstraintFromSwitch(SSASwitchInstruction instr, SSACFG.BasicBlock lastBlock, CGNode currentNode);

  public boolean addPathConstraintFromSwitch(SSAConditionalBranchInstruction switchCase, CGNode currentNode, boolean negated);
  
  public IQuery deepCopy();

  /**
   * @return - true if the query has been refuted, false otherwise
   */
  public boolean isFeasible();

  /**
   * drop parts of the query that are not shared by the current query and other
   */
  public void intersect(IQuery other);

  /**
   * does this query subsume other?
   */
  public boolean contains(IQuery other);

  /**
   * does this query contain constraint?
   */
  public boolean containsConstraint(Constraint constraint);
  
  public List<AtomicPathConstraint> getIndexConstraintsFor(FieldReference fld);


  /**
   * modify query to simulate execution of non-call instr
   * 
   * @return null if query is infeasible after executing instr, empty list if
   *         query is feasible and there are no case splits, list of paths to
   *         explore (in addition to the current path) if current path is
   *         feasible and there are case splits
   */
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath);

  /**
   * phi's are a special case between we need a variable to tell us which index
   * to pick
   */
  public List<IQuery> visitPhi(SSAPhiInstruction instr, int phiIndex, IPathInfo currentPath);

  /**
   * enter a callee. note that the CGNode of currentPath should be the callee,
   * NOT the caller
   * 
   * @param caller
   *          - the CGNode that the call was made from
   * @return null if query is infeasible after executing instr, empty list if
   *         query is feasible and there are no case splits, list of paths to
   *         explore (in addition to the current path) if current path is
   *         feasible and there are case splits
   */
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode caller, IPathInfo currentPath);

  /**
   * return from a callee. note that the CGNode of currentPath should be the
   * caller, NOT the callee
   * 
   * @param callee
   *          - method we are returning from
   */
  public List<IQuery> returnFromCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath);

  /**
   * stale constraints are constraints that refer to locals of a method we are
   * about to exit from we should mark the path infeasible if the method
   * contains stale constraints, since these constraints can never be produced
   * 
   * @param currentNode
   *          - the node we are about to exit (i.e. return to its caller)
   * @return - true if query contains stale constraints, false otherwise
   */
  public boolean containsStaleConstraints(CGNode currentNode);

  /**
   * give up execution and declare witness, if permitted by this query
   */
  public void declareFakeWitness();

  /**
   * can the call produce or affect any constraints in this query?
   */
  public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg);

  public void dropConstraintsContaining(Set<PointerVariable> vars);
  
  /**
   * rather than entering a call, overapproximate its effect by dropping all of
   * the constraints it can produce
   */
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee, boolean dropPtConstraints);

  public void dropReturnValueConstraintsForCall(SSAInvokeInstruction instr, CGNode caller);
  
  /**
   * reflect context-sensitivity of node in query, if applicable
   * 
   * @param node
   *          - CGNode we are about to enter for the first time
   * @return - true if query is feasible after adding constraints, false
   *         otherwise
   */
  public boolean addContextualConstraints(CGNode node, IPathInfo currentPath);

  /**
   * can @param instr dispatch to @param callee from @param caller given our constraints? 
   * @return true if feasible, false otherwise
   */
  public boolean isDispatchFeasible(SSAInvokeInstruction instr, CGNode caller, CGNode callee);
  
  /**
   * drop constraints containing non-heap values
   */
  public void removeAllLocalConstraints();

  public AbstractDependencyRuleGenerator getDepRuleGenerator();
  
  public Iterator<? extends Constraint> constraints();
  
  public Set<FieldReference> getFields();
  
  public void removeAllNonClinitConstraints();


  /**
   * @return a map of constraint -> methods modifying constraint for each
   *         constraint;
   */
  public Map<Constraint, Set<CGNode>> getModifiersForQuery();

  /**
   * remove all constraints that could be produced in the loop headed by
   * loopHead
   */
  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode);

  /**
   * returns true if any constraints can be produced in the loop headed by
   * loopHead
   */
  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode);

  /**
   * special case for entering a call without being able to do direct parameter
   * binding
   */
  public void enterCallFromJump(CGNode callee);

  public List<DependencyRule> getWitnessList();
  
  public Map<Constraint, Set<CGNode>> getRelevantNodes();
  
  public boolean initializeInstanceFieldsToDefaultValues(CGNode constructor);
  
  public PointerVariable getPointedTo(PointerVariable var);

  
  /**
   * to be called after exiting class initializers; write default values to *all*
   * static fields
   */
  public void intializeStaticFieldsToDefaultValues();
  
  public void dispose();

  /**
   * Query that is always refuted (cannot be witnessed)
   */
  /*
  public class FalseQuery extends AbstractQuery {
    public FalseQuery() {
    }

    @Override
    public boolean containsConstraint(Constraint c) {
      return false;
    }

    @Override
    public boolean foundWitness() {
      return false;
    }

    @Override
    public boolean isFeasible() {
      return true;
    }

    @Override
    public IQuery deepCopy() {
      return new FalseQuery();
    }

    @Override
    public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranchFeasible) {
      // Util.Unimp("adding constraint from branch point");
      return true;
    }
    
    public void enterCallFromJump(CGNode callee) { }


    @Override
    public void intersect(IQuery other) {
      // do nothing; this query has no constraints, so nothing to intersect!
    }

    public List<DependencyRule> getWitnessList() {
      return null;
    }
    
    @Override
    public void dispose() { }

    @Override
    public AbstractDependencyRuleGenerator getDepRuleGenerator() { return null; }
    
    @Override
    public int hashCode() {
      return 5;
    }

    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FalseQuery))
        return false;
      return this.hashCode() == other.hashCode();
    }

    // @Override
    public int compareTo(Object other) {
      if (!(other instanceof FalseQuery))
        return -1;
      int thisHash = this.hashCode(), otherHash = other.hashCode();
      if (thisHash < otherHash)
        return -1;
      else if (thisHash > otherHash)
        return 1;
      return 0;
    }
  }
  */
}

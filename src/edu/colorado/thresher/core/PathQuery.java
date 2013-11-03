package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeBT.BinaryOpInstruction;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.shrikeBT.IComparisonInstruction.Operator;
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAArrayLengthInstruction;
import com.ibm.wala.ssa.SSAArrayLoadInstruction;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAComparisonInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAConversionInstruction;
import com.ibm.wala.ssa.SSAGetCaughtExceptionInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSALoadMetadataInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.microsoft.z3.AST;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

/**
 * Query regarding path feasibility containing formulae acquired from path
 * conditions
 * 
 * @author sam
 */
public class PathQuery implements IQuery {

  final AbstractDependencyRuleGenerator depRuleGenerator;
  final HeapModel heapModel;
  // set of path constraints; implicit AND exists between all of them
  // final TreeSet<AtomicPathConstraint> constraints; // these need to be
  // ordered for comparison
  final Set<AtomicPathConstraint> constraints; // these need to be ordered for
                                               // comparison
  
  // TMP! because Scwala needs it
  public Set<AtomicPathConstraint> getConstraints() { return constraints; }

  // set of path constraints that we have had in our constraint set at some
  // point
  final List<AtomicPathConstraint> witnessList;

  // list of path constraints that make this query unsatisfiable; lazily
  // instantiated
  List<AtomicPathConstraint> unsatCore;

  // set of variables contained in our path constraints. used for relevancy
  // lookups
  public final Set<PointerVariable> pathVars;

  // Z3Context shared among all paths. do not make copies of this unless you dispose of them properly!
  //final Z3Context ctx;
  final Context ctx;
  final Solver solver;
  
  // a z3 representation of the z3 assumption tied to the current path
  // constraints
  //Z3AST currentPathAssumption;
  BoolExpr currentPathAssumption;

  boolean fakeWitness = false;
  boolean feasible = true;

  // constructor to be used from the outside
  public PathQuery(AbstractDependencyRuleGenerator depRuleGenerator) {
    this.depRuleGenerator = depRuleGenerator;
    this.heapModel = depRuleGenerator.getHeapModel();
    // this should be the only place Z3Context's are created unless they are disposed of carefully
    //this.ctx = new Z3Context(new Z3Config());
    Context tmpCtx = null;
    Solver tmpSolver = null;
    try {
      tmpCtx = new Context();
      tmpSolver = tmpCtx.MkSolver();
    } catch (Z3Exception e) {
      Util.Assert(false, "problem with z3 " + e);      
    }
    this.ctx = tmpCtx;
    this.solver = tmpSolver;
    this.constraints = HashSetFactory.make(); 
    this.pathVars = HashSetFactory.make(); 
    this.witnessList = new LinkedList<AtomicPathConstraint>();
    this.currentPathAssumption = null;
  }
  
  // if the context is not copied, this will clear all memory Z3 is using
  public void dispose() { ctx.Dispose(); } //ctx.delete(); }

  // constructor for deep copying only
  // PathQuery(TreeSet<AtomicPathConstraint> constraints, Set<PointerVariable>
  // pathVars, List<AtomicPathConstraint> witnessList,
  PathQuery(Set<AtomicPathConstraint> constraints, Set<PointerVariable> pathVars, List<AtomicPathConstraint> witnessList,
      AbstractDependencyRuleGenerator depRuleGenerator, Context ctx, Solver solver) {
    this.constraints = constraints;
    this.pathVars = pathVars;
    this.witnessList = witnessList;
    this.depRuleGenerator = depRuleGenerator;
    this.heapModel = depRuleGenerator.getHeapModel();
    this.ctx = ctx; 
    this.solver = solver;
    this.currentPathAssumption = null;
    rebuildZ3Constraints();
  }

  @Override
  public PathQuery deepCopy() {
    // return new PathQuery(Util.deepCopyTreeSet(constraints),
    // Util.deepCopySet(pathVars), Util.deepCopyList(witnessList),
    // depRuleGenerator);//, ctx);
    return new PathQuery(Util.deepCopySet(constraints), Util.deepCopySet(pathVars), Util.deepCopyList(witnessList),
        depRuleGenerator, ctx, solver);// , ctx);
  }

  @Override
  public boolean containsStaleConstraints(CGNode currentNode) {
    List<PointerVariable> toDrop = new LinkedList<PointerVariable>();
    for (PointerVariable var : pathVars) {
      if (var.isLocalVar() && currentNode.equals(var.getNode())) {
        // TODO: hack! for now, we simply drop stale constraints... they can
        // appear in rare cases, such as
        // when a path constraint involves the return value of a call that does
        // not resolve to any call sites.
        if (Options.DEBUG) Util.Debug("found stale constraint on var " + var + " in path constraints " + this + " ; refuting");
        toDrop.add(var);
      }
    }
    for (PointerVariable var : toDrop) dropConstraintsContaining(var);
    return false;
  }

  /**
   * can the call produce or affect any constraints in this query?
   */
  @Override
  public boolean isCallRelevant(SSAInvokeInstruction instr, CGNode caller, CGNode callee, CallGraph cg) {
    Util.Unimp("checking relevance for path constraints");
    return true;
  }

  @Override
  public void dropConstraintsProduceableInCall(SSAInvokeInstruction instr, CGNode caller, CGNode callee, boolean dropPtConstraints) {
    Util.Unimp("dropping constraints produced in call for path constraints");
  }
  
  @Override
  public void dropReturnValueConstraintsForCall(SSAInvokeInstruction instr, CGNode caller) {
    if (instr.hasDef()) {
      PointerVariable retval = new ConcretePointerVariable(caller, instr.getDef(), this.heapModel);
      dropConstraintsContaining(retval);
    }
  }

  @Override
  public boolean containsLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    /*
     * Set<DependencyRule> nodeRules =
     * depRuleGenerator.getRulesForNode(currentNode); for (DependencyRule rule :
     * nodeRules) { SSACFG.BasicBlock ruleBlk = rule.getBlock();
     * Util.Assert(ruleBlk != null, "no basic block for rule " + rule); if
     * (WALACFGUtil.isInLoopBody(ruleBlk, loopHead, rule.getNode().getIR())) {
     * return true; } }
     */
    return false;
  }

  @Override
  public void removeLoopProduceableConstraints(SSACFG.BasicBlock loopHead, CGNode currentNode) {
    Util.Unimp("removing loop produceable constraints");
    Set<DependencyRule> loopRules = Util.getRulesForLoop(loopHead, currentNode, depRuleGenerator, depRuleGenerator.getCallGraph());

    for (DependencyRule rule : loopRules) {
      SSACFG.BasicBlock ruleBlk = rule.getBlock();
      Util.Assert(ruleBlk != null, "no basic block for rule " + rule);
      if (WALACFGUtil.isInLoopBody(ruleBlk, loopHead, rule.getNode().getIR())) {
        this.dropConstraintsContaining(rule.getShown().getSource());
      }
    }
  }
  
  @Override
  public void removeAllNonClinitConstraints() {
    Set<AtomicPathConstraint> toRemove = HashSetFactory.make();
    Set<String> indexConstraintNames = HashSetFactory.make();

    for (AtomicPathConstraint constraint : this.constraints) {
      if (constraint.isClinitConstraint()) {
        for (FieldReference fld : constraint.getFields()) {
          if (isArrayIndexField(fld)) {
            String indexConstraintName = fld.getName().toString();
            indexConstraintNames.add(indexConstraintName);
            break;
          }
        }
        continue;
      }
      toRemove.add(constraint);
    }
    for (AtomicPathConstraint removeMe : toRemove) {
      // remove this constraint as long as it is not an array index constraint associated with a constraint we want to keep
      if (!removeMe.isArrayIndexConstraint() || 
          !indexConstraintNames.contains(((SimplePathTerm) removeMe.lhs).getObject().getInstanceKey())) {
        removeConstraint(removeMe);
      }
    }
  }
  
  
  public Pair<FieldReference,List<AtomicPathConstraint>> getIndexConstraintsFor(AtomicPathConstraint c) {
    Util.Assert(c.getLhs() instanceof SimplePathTerm); 
    SimplePathTerm arrTerm = (SimplePathTerm) c.getLhs();
    Util.Assert(arrTerm.getFirstField() != null && isArrayIndexField(arrTerm.getFirstField()));
    FieldReference indexField = arrTerm.getFirstField(); // find the term with the path var
    List<AtomicPathConstraint> indexConstraints = getIndexConstraintsFor(indexField);
    return Pair.make(indexField,indexConstraints);
  }
  
  @Override
  public List<AtomicPathConstraint> getIndexConstraintsFor(FieldReference fld) {
    Util.Pre(isArrayIndexField(fld));
    List<AtomicPathConstraint> indexConstraints = new LinkedList<>();
    for (AtomicPathConstraint constraint : this.constraints) {
      if (constraint.isArrayIndexConstraint() && 
          ((SimplePathTerm) constraint.lhs).getObject().getInstanceKey().equals(fld.getName().toString())) {
        //return constraint;
        indexConstraints.add(constraint);
      }
    }
    return indexConstraints;
  }

  /**
   * rebuild Z3 constraints to reflect update to constraint set
   */
  /*
   * void rebuildZ3Constraints() { pathVars.clear(); if (constraints.size() > 0)
   * { Z3AST[] constraintsArr = new Z3AST[constraints.size()]; int i = 0; for
   * (AtomicPathConstraint constraint : constraints) {
   * pathVars.addAll(constraint.getVars()); Z3AST z3Constraint =
   * constraint.toZ3AST(ctx); constraintsArr[i++] = z3Constraint; } Z3AST
   * pathConstraint = ctx.mkAnd(constraintsArr); Z3AST newAssumption =
   * Util.makeFreshPropositionalVar(ctx);
   * ctx.assertCnstr(ctx.mkImplies(newAssumption, pathConstraint));
   * this.currentPathAssumption = newAssumption; } // else, do nothing; no
   * constraints to work with }
   */

  void rebuildZ3Constraints() {
    pathVars.clear();
    if (constraints.size() > 0) {
      // ctx.delete();
      //AST[] constraintsArr = new AST[constraints.size()];
      BoolExpr[] constraintsArr = new BoolExpr[constraints.size()];
      int i = 0;
      for (AtomicPathConstraint constraint : constraints) {
        pathVars.addAll(constraint.getVars());
        AST z3Constraint = constraint.toZ3AST(ctx);
        constraintsArr[i++] = (BoolExpr) z3Constraint;
      }
      try {
        //AST pathConstraint = ctx.mkAnd(constraintsArr);
        BoolExpr pathConstraint = ctx.MkAnd(constraintsArr);
        BoolExpr newAssumption = Util.makeFreshPropositionalVar(ctx);
        solver.Assert(ctx.MkImplies(newAssumption, pathConstraint));
        //ctx.assertCnstr(ctx.mkImplies(newAssumption, pathConstraint));
        this.currentPathAssumption = newAssumption;
      } catch (Z3Exception e) {
        Util.Assert(false, "problem with z3 " + e);
      }
      
    } // else, do nothing; no constraints to work with
  }

  public boolean visit(SSAArrayLengthInstruction instr, CGNode node) {
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {
      SimplePathTerm arrLength = new SimplePathTerm(new ConcretePointerVariable(node, instr.getUse(0),
          this.heapModel), SimplePathTerm.LENGTH);
      substituteExpForVar(arrLength, varName);
      return isFeasible();
    }
    return true;
  }

  boolean visit(SSAGetInstruction instr, CGNode node) {
    Util.Assert(instr.getNumberOfDefs() == 1, "Expecting only 1 def!");
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {
      SimplePathTerm toSub = null;
      if (instr.isStatic()) { // static field get
        IField staticField = depRuleGenerator.getCallGraph().getClassHierarchy().resolveField(instr.getDeclaredField());
        PointerKey key = this.heapModel.getPointerKeyForStaticField(staticField);
        PointerVariable var = Util.makePointerVariable(key);
        toSub = new SimplePathTerm(var);
      } else { // non-static get
        PointerVariable objRead = makeVarFromUse(node, instr.getUse(0));
        toSub = new SimplePathTerm(objRead, instr.getDeclaredField());
      }
      substituteExpForVar(toSub, varName);
      return isFeasible();
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  /**
   * helper for visiting static puts, which are a bit odd
   */
  boolean visitStaticPut(SSAPutInstruction instr, CGNode node, SymbolTable tbl) {
    Util.Pre(instr.isStatic(), "should only be called on static puts!");
    Util.Pre(instr.getNumberOfUses() == 1, "put " + instr + " has " + instr.getNumberOfUses() + " uses! expected 1");
    IField staticField = depRuleGenerator.getCallGraph().getClassHierarchy().resolveField(instr.getDeclaredField());
    if (staticField == null) { // TODO: this shouldn't happen, but it sometimes
                               // does. uncomment and try on NPR app 
      return true;
    }
    PointerVariable staticFieldVar = Util.makePointerVariable(this.heapModel.getPointerKeyForStaticField(
        staticField));
    if (pathVars.contains(staticFieldVar)) {
      int use = instr.getUse(0);
      if (tbl.isConstant(use)) {
        if (tbl.isIntegerConstant(use)) { // assigning constant to field
          if (Options.DEBUG)
            Util.Debug("subbing constant " + tbl.getIntValue(use) + " for " + staticField);
          // substituteExpForVar(new
          // SimplePathTerm(tbl.getIntValue(instr.getUse(1))), staticFieldVar);
          substituteExpForVar(new SimplePathTerm(tbl.getIntValue(use)), staticFieldVar);
        } else if (tbl.isNumberConstant(use)) {
          substituteExpForVar(SimplePathTerm.NULL, staticFieldVar);
        } else { // don't know how to sub this kind of constant. just drop
                 // instead.
          // TODO: implement other kinds of subbing
          // can't sub...drop constraints c
          dropConstraintsContaining(staticFieldVar);
        }
      } else { // assigning var to field
        // PointerVariable rhsVarName = new ConcretePointerVariable(node,
        // instr.getUse(1), this.heapModel);
        PointerVariable rhsVarName = new ConcretePointerVariable(node, use, this.heapModel);
        substituteExpForVar(new SimplePathTerm(rhsVarName), staticFieldVar);
      }
      return isFeasible();
    }    
    return true;
  }

  boolean visit(SSAPutInstruction instr, CGNode node, SymbolTable tbl) {
    if (instr.isStatic()) return visitStaticPut(instr, node, tbl); // static field
    // else, non-static field
    PointerVariable varName = new ConcretePointerVariable(node, instr.getUse(0), this.heapModel); 
    if (pathVars.contains(varName)) {
      FieldReference fieldName = instr.getDeclaredField();
      int use = instr.getUse(1);
      if (tbl.isConstant(use)) {
        if (tbl.isIntegerConstant(use)) { // assigning constant to field
          if (Options.DEBUG) {
            Util.Debug("subbing constant " + tbl.getIntValue(use) + " for " + varName + "." + fieldName);
          }
          substituteExpForFieldRead(new SimplePathTerm(tbl.getIntValue(use)), varName, fieldName);
        } else if (tbl.isNullConstant(use)) {
          substituteExpForFieldRead(SimplePathTerm.NULL, varName, fieldName);
        } else if (tbl.isLongConstant(use)) {
          // TODO: can cause overflow. just adding to get easy initializations of longs to 0. will fix later
          substituteExpForFieldRead(new SimplePathTerm(new Long(tbl.getLongValue(use)).intValue()), varName, fieldName);
        } else { // don't know how to sub this kind of constant. just drop instead
          // check if this is writing to a field in our constraints
          for (AtomicPathConstraint constraint : this.constraints) {
            Set<SimplePathTerm> terms = constraint.getTerms();
            for (SimplePathTerm term : terms) {
              if (term.getVars().contains(varName) &&
                  term.hasField() && term.getFirstField().equals(fieldName)) {
                // TODO: implement other kinds of subbing
                // can't sub...drop constraints c
                dropConstraintsContaining(varName);
              }
            }
          }
          // doesn't write to a field we care about; no need to drop
          return true;
        }
      } else { // assigning var to field
        // TODO: write test where name being substituted is active at multiple locations
        PointerVariable rhsVarName = new ConcretePointerVariable(node, instr.getUse(1), this.heapModel);
        substituteExpForFieldRead(new SimplePathTerm(rhsVarName), varName, fieldName);
      }
      return isFeasible();
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  boolean visit(SSAInvokeInstruction instr, CGNode callee, CGNode caller) {
    if (instr.hasDef()) {
      PointerVariable returnValue = new ConcretePointerVariable(caller, instr.getDef(), this.heapModel);
      if (pathVars.contains((returnValue))) {
        // substituteExpForVar(new
        // SimplePathTerm(Util.makeReturnValuePointer(instr.getDeclaredTarget())),
        // returnValue);
        substituteExpForVar(new SimplePathTerm(Util.makeReturnValuePointer(callee, this.heapModel)),
            returnValue);
        return isFeasible();
      }
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  boolean visit(SSAReturnInstruction instr, CGNode node, SymbolTable tbl) {
    int resultNum = instr.getResult();
    if (resultNum >= 0) { // if the function is a non-void function
      PointerVariable retvalName = Util.makeReturnValuePointer(node, this.heapModel);
      if (pathVars.contains(retvalName)) {
        if (tbl.isConstant(resultNum)) {
          if (tbl.isIntegerConstant(resultNum)) {
            substituteExpForVar(new SimplePathTerm(tbl.getIntValue(resultNum)), retvalName);
          } else if (tbl.isNullConstant(resultNum))
            substituteExpForVar(SimplePathTerm.NULL, retvalName);
          else if (tbl.isStringConstant(resultNum))
            substituteExpForVar(SimplePathTerm.NON_NULL, retvalName); // Util.Unimp("subbing string consts");
          else if (tbl.isDoubleConstant(resultNum) || tbl.isFloatConstant(resultNum) || tbl.isLongConstant(resultNum)) {
            // TODO: add handling for this
            dropConstraintsContaining(retvalName);
          }

          else
            Util.Unimp("subbing non-integer constants");
        } else {
          PointerVariable result = new ConcretePointerVariable(node, resultNum, this.heapModel);
          substituteExpForVar(new SimplePathTerm(result), retvalName);
        }
        return isFeasible();
      }
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  boolean visit(SSANewInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable local = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(local)) {
      if (instr.getNewSite().getDeclaredType().isArrayType()) { // special case
                                                                // for arrays
        // may need to update path constraints with the length of this array
        SimplePathTerm arrLength;
        if (tbl.isConstant(instr.getUse(0)))
          arrLength = new SimplePathTerm(tbl.getIntValue(instr.getUse(0)));
        else
          arrLength = new SimplePathTerm(new ConcretePointerVariable(node, instr.getUse(0), this.heapModel));
        substituteExpForFieldRead(arrLength, local, SimplePathTerm.LENGTH);

      } else { // not an array
        // all a new() instr can do for us is resolve a constraint of the form
        // "x != null"
        substituteExpForVar(SimplePathTerm.NON_NULL, local);
      }
      return isFeasible();
    }
    return true; // didn't add any constraints, can't be infeasible
  }

  boolean visit(SSAUnaryOpInstruction instr, CGNode node) {
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {
      PointerVariable negated = new ConcretePointerVariable(node, instr.getUse(0), this.heapModel);
      IUnaryOpInstruction.IOperator op = instr.getOpcode();
      if (op == IUnaryOpInstruction.Operator.NEG) {
        // replace x with 0 - x
        PathTermWithBinOp binExp = new PathTermWithBinOp(0, negated, BinaryOpInstruction.Operator.SUB);
        substituteExpForVar(binExp, varName);
      } else
        Util.Unimp("operator " + op);
      return isFeasible();
    }
    return true;
  }

  boolean visit(SSABinaryOpInstruction instr, CGNode node, SymbolTable tbl) {
    Util.Assert(instr.getNumberOfDefs() == 1, "Expecting only 1 def; found " + instr.getNumberOfDefs());
    Util.Assert(instr.getNumberOfUses() == 2, "Expecting only 2 uses; found " + instr.getNumberOfUses());
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {

      if (!(instr.getOperator() instanceof BinaryOpInstruction.Operator)) {
        if (Options.DEBUG)
          Util.Debug("dropping constraints due to unsupported op " + instr.getOperator());
        dropConstraintsContaining(varName);
        return true;
      }
      BinaryOpInstruction.Operator op = (BinaryOpInstruction.Operator) instr.getOperator();
      // TODO: not currently supporting XOR or bitwise AND/OR; would require
      // using Z3 bitvector theory
      if (op == BinaryOpInstruction.Operator.XOR || op == BinaryOpInstruction.Operator.AND || op == BinaryOpInstruction.Operator.OR) {
        // TODO: even if we don't want to represent everything as Z3 bitvectors,
        // we can just translate this constraint to "true:
        // TODO: in Z3 and keep our own local representation so we can do bw and
        // etc on constants
        if (Options.DEBUG)
          Util.Debug("dropping constraints due to unsupported op " + op);
        dropConstraintsContaining(varName);
        return true;
        // Util.Unimp("operator " + op);
      }

      boolean lhsConstant = tbl.isConstant(instr.getUse(0)), rhsConstant = tbl.isConstant(instr.getUse(1));
      if (lhsConstant && rhsConstant) { // constants on both sides of operator;
                                        // evaluate!
        if (tbl.isIntegerConstant(instr.getUse(0)) && tbl.isIntegerConstant(instr.getUse(1))) {
          int lhs = tbl.getIntValue(instr.getUse(0)), rhs = tbl.getIntValue(instr.getUse(1));
          int value = -1;
          switch (op) {
            case ADD:
              value = lhs + rhs;
              break;
            case SUB:
              value = lhs - rhs;
              break;
            case MUL:
              value = lhs * rhs;
              break;
            case DIV:
              value = lhs / rhs;
              break;
            case REM:
              value = lhs % rhs;
              break;
            case XOR:
              value = lhs ^ rhs;
              break;
            case AND:
              value = lhs & rhs;
              break;
            default:
              Util.Unimp("unrecognized op" + op);
          }
          SimplePathTerm constant = new SimplePathTerm(value);
          substituteExpForVar(constant, varName);
        } else {
          // TODO: implemenet
          // unhanlded constants; drop ths constraint
          // Util.Unimp("evaluation of non-integer constant binops in instr " +
          // instr);
          dropConstraintsContaining(varName);
          return true;
        }
      } else if (lhsConstant) { // constant on left side of binary operator only
        PathTermWithBinOp binExp = new PathTermWithBinOp(tbl.getIntValue(instr.getUse(0)), new ConcretePointerVariable(node,
            instr.getUse(1), this.heapModel), op);
        substituteExpForVar(binExp, varName);
      } else if (rhsConstant) { // constant on right of binary operator only
        PathTermWithBinOp binExp = new PathTermWithBinOp(new ConcretePointerVariable(node, instr.getUse(0),
            this.heapModel), tbl.getIntValue(instr.getUse(1)), op);
        substituteExpForVar(binExp, varName);
      } else { // no constants
        PointerVariable lhs = new ConcretePointerVariable(node, instr.getUse(0), this.heapModel);
        PointerVariable rhs = new ConcretePointerVariable(node, instr.getUse(1), this.heapModel);
        substituteExpForVar(new PathTermWithBinOp(lhs, rhs, op), varName);
      }
      return isFeasible();
    }
    return true;
  }
  
  // comparing floats, longs, or doubles. TODO: implement this
  boolean visit(SSAComparisonInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {
      int use0 = instr.getUse(0), use1 = instr.getUse(1);
      if (tbl.isConstant(use0) && tbl.isConstant(use1)) { // comparison of
                                                          // constants
        Operator op = instr.getOperator();
        if (tbl.isDoubleConstant(use0)) {
          switch (op) {
            case CMP:
              return tbl.getDoubleValue(use0) == tbl.getDoubleValue(use1);
            case CMPL:
              return tbl.getDoubleValue(use0) < tbl.getDoubleValue(use1);
            case CMPG:
              return tbl.getDoubleValue(use0) > tbl.getDoubleValue(use1);
            default:
              Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN COMPARISON");
          }
        } else if (tbl.isFloatConstant(use0)) {
          switch (op) {
            case CMP:
              return tbl.getFloatValue(use0) == tbl.getFloatValue(use1);
            case CMPL:
              return tbl.getFloatValue(use0) < tbl.getFloatValue(use1);
            case CMPG:
              return tbl.getFloatValue(use0) > tbl.getFloatValue(use1);
            default:
              Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN COMPARISON");
          }
        } else if (tbl.isLongConstant(use0)) {
          switch (op) {
            case CMP:
              return tbl.getLongValue(use0) == tbl.getLongValue(use1);
            case CMPL:
              return tbl.getLongValue(use0) < tbl.getLongValue(use1);
            case CMPG:
              return tbl.getLongValue(use0) > tbl.getLongValue(use1);
            default:
              Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN COMPARISON");
          }
        } else
          Util.Unimp("unexpected const type in comparison " + instr);
      } else { // not a constant
        // TODO: we don't currently support this case... can only store integer
        // constants in path constraints.
        // just drop the constraint that contains this var
        dropConstraintsContaining(varName);
      }
    }
    return true;
  }
  
  private void dropConstraints(List<AtomicPathConstraint> toDrop) {
    for (AtomicPathConstraint constraint : toDrop) {
      if (Options.DEBUG)
        Util.Debug("dropping constraint " + constraint);
      // constraints.remove(constraint);
      removeConstraint(constraint);
    }
    rebuildZ3Constraints();
  }
  
  void dropConstraintsContaining(PointerVariable varName, IField fld) {
    List<AtomicPathConstraint> toRemove = new ArrayList<AtomicPathConstraint>();

    for (AtomicPathConstraint constraint : this.constraints) {
      if (constraint.getVars().contains(varName)) {
        Set<FieldReference> fields = constraint.getFields();
        if (fields.contains(fld.getReference())) {
          toRemove.add(constraint);
        }
      }
    }
   dropConstraints(toRemove);
  }
  
  public void dropConstraintsContaining(PointerVariable varName) {
    List<AtomicPathConstraint> toRemove = new ArrayList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : this.constraints) {  
      if (constraint.getVars().contains(varName)) {
        toRemove.add(constraint);
      }
    }
    dropConstraints(toRemove);
  }
  
  @Override
  public void dropConstraintsContaining(Set<PointerVariable> vars) {
    List<AtomicPathConstraint> toRemove = new ArrayList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : this.constraints) {  
      //if (constraint.getVars().contains(varName)) {
      if (Util.intersectionNonEmpty(vars, constraint.getVars())) {
        toRemove.add(constraint);
      }
    }
    dropConstraints(toRemove);
  }

  boolean visit(SSAArrayLoadInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable varName = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(varName)) {
      // can model array write as (array name).array.i, where i is the index of
      // interest
     
      if (Options.INDEX_SENSITIVITY) {
        PointerVariable arrayVar = new ConcretePointerVariable(node, instr.getArrayRef(), this.heapModel);
        //PointerVariable indexVar = new ConcretePointerVariable(node, instr.getIndex(), this.heapModel);
        //FieldReference indexRef = getFieldForIndex(instr.getIndex(), instr.getElementType());//FieldReference.findOrCreate(ClassLoaderReference.Primordial, "__fakeField", "v" + instr.getIndex(), 
            //instr.getElementType().toString());
        int index = instr.getIndex();
        SimplePathTerm indexExpr = tbl.isIntegerConstant(index) ? new SimplePathTerm(tbl.getIntValue(index)) : 
          new SimplePathTerm(new ConcretePointerVariable(node, index, this.heapModel));
        FieldReference indexFld = getFieldForIndex(instr.getElementType(), tbl);
        
        SimplePathTerm toSub = new SimplePathTerm(arrayVar, indexFld);      
        if (substituteExpForVar(toSub, varName)) {
          // add index fld name == index expr constraint
          this.addConstraint(new AtomicPathConstraint(new SimplePathTerm(new ConcretePointerVariable(indexFld.getName().toString())), 
              indexExpr, IConditionalBranchInstruction.Operator.EQ));
        }
        return isFeasible();
      } else {
        if (Options.DEBUG) {
          Util.Debug("we don't handle path queries with arrays precisely; dropping constraints. this arrayLoad insruction " + instr
              + " might matter for " + this);
        }
        // drop this constraint; we can't prove or disprove it
        dropConstraintsContaining(varName);
      }
      
    }
    return true;
  }
  
  public List<AtomicPathConstraint> getConstraintsWithVar(PointerVariable var) {
    List<AtomicPathConstraint> constraintsWithVar = new LinkedList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : this.constraints) {
      if (constraint.getVars().contains(var)) {
        constraintsWithVar.add(constraint);
      }
    }
    return constraintsWithVar;
  }
  
  public static boolean isArrayIndexField(FieldReference fld) {
    return fld.getDeclaringClass().getName().toString().equals(ARRAY_INDEX);
  }
  
  public static boolean isArrayLengthField(FieldReference fld) {
    return fld == SimplePathTerm.LENGTH;
  }
  
  public static boolean isArrayIndexVariable(PointerVariable var) {
    return (var.getInstanceKey() instanceof String) && 
            isArrayIndexVariableName((String) var.getInstanceKey());
  }
  
  public static boolean isArrayIndexVariableName(String name) {
    return name.contains(ARRAY_INDEX);
  }
  
  private static final String ARRAY_INDEX = "__arrIndex";
  
  private static int indexCounter = 0;
  static FieldReference getFieldForIndex(TypeReference arrType, SymbolTable tbl) {
    //String indexStr = tbl.isIntegerConstant(index) ? "" + tbl.getIntValue(index) : "v" + index;
    return FieldReference.findOrCreate(ClassLoaderReference.Primordial, ARRAY_INDEX, (indexCounter++) + ARRAY_INDEX, arrType.toString());
  }

  boolean visit(SSAArrayStoreInstruction instr, CGNode node, SymbolTable tbl) {
    PointerVariable arrayVar = new ConcretePointerVariable(node, instr.getArrayRef(), this.heapModel);    
    if (pathVars.contains(arrayVar)) {      
      if (Options.DEBUG) {
        Util.Debug("we don't handle path queries with arrays precisely; dropping constraints. this arrayStore insruction " + instr
              + " might matter for " + this);
      }
      dropConstraintsContaining(arrayVar);
    }
    return true;
  }
  
  // TODO: just assuming conversion goes through and is for integers at this point--should add check
  public boolean visit(SSAConversionInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(lhsVar)) {
      // for now conversions are unchecked; just sub the rhs for the lhs
      PointerVariable rhsVar = new ConcretePointerVariable(node, instr.getUse(0), this.heapModel);
      substituteExpForVar(new SimplePathTerm(rhsVar), lhsVar);
    }
    return true;
  }

  // drop constraints
  public boolean visit(SSALoadMetadataInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(lhsVar)) {
        dropConstraintsContaining(lhsVar);
    }
    return true;
  }


  public boolean visit(SSACheckCastInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(lhsVar)) {
      Util.Print("subbing path constraint check cast");
      // TODO: add constraint for checking casts?
      // for now casts are unchecked; just sub the rhs for the lhs
      PointerVariable rhsVar = new ConcretePointerVariable(node, instr.getVal(), this.heapModel);
      substituteExpForVar(new SimplePathTerm(rhsVar), lhsVar);
      return isFeasible();
    }
    return true;
  }

  public boolean visit(SSAInstanceofInstruction instr, CGNode node) {
    PointerVariable lhsVar = new ConcretePointerVariable(node, instr.getDef(), this.heapModel);
    if (pathVars.contains(lhsVar)) {
      // TODO: we don't have enough type information to check this constraint
      // right now, so just drop it
      dropConstraintsContaining(lhsVar);    
    }
    return true;
  }
  
  // TODO: track catches so that thrown exceptions aren't necessarily an instant
  // refutation
  public boolean visit(SSAThrowInstruction instr, CGNode node) {
    if (Options.DEBUG)
      Util.Debug("refuted by thrown exception!");
    this.feasible = false;
    return false;
  }

  /**
   * replace the variable subFor with the expression toSub (i.e, sub y.f for x)
   */
  boolean substituteExpForVar(PathTerm toSub, PointerVariable subFor) {
    if (Options.DEBUG)
      Util.Debug("subsExpForVar subbing " + toSub + " for " + subFor);
    SimplePathTerm subForTerm = new SimplePathTerm(subFor);
    Set<AtomicPathConstraint> toAdd = HashSetFactory.make(); //new HashSet<AtomicPathConstraint>();
    List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : constraints) {
      // AtomicPathConstraints are (almost) pure, so we can't do substitution in-place
      AtomicPathConstraint newConstraint;
      if (toSub instanceof SimplePathTerm && !toSub.isIntegerConstant())
        newConstraint = constraint.heapSubstitute((SimplePathTerm) toSub, subForTerm);
      else
        newConstraint = constraint.substitute(toSub, subForTerm);
      if (newConstraint.substituted()) {
        if (newConstraint == AtomicPathConstraint.FALSE) {
          if (Options.DEBUG)
            Util.Debug("refuted by path constraint");
          makeUnsatCore(constraint);
          this.feasible = false;
          return false;
        }
        if (newConstraint != AtomicPathConstraint.TRUE)
          toAdd.add(newConstraint);
        toRemove.add(constraint);
      }
    }
    // remove old (pre-substitution) constraints
    for (AtomicPathConstraint constraint : toRemove) {
      removeConstraint(constraint);
    }
    // add new (post-substitution) constraints
    for (AtomicPathConstraint constraint : toAdd) {
      addConstraint(constraint);
    }
    return !toRemove.isEmpty() || !toAdd.isEmpty();
  }

  /**
   * replace the field read expression subFor.fieldName with the expression
   * toSub (i.e., sub 1 for x.f)
   */
  public void substituteExpForFieldRead(SimplePathTerm toSub, PointerVariable subFor, FieldReference fieldName) {
    List<AtomicPathConstraint> toAdd = new LinkedList<AtomicPathConstraint>();
    List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : constraints) {
      AtomicPathConstraint newConstraint = constraint.substituteExpForFieldRead(toSub, subFor, fieldName);
      if (newConstraint.substituted()) {
        if (newConstraint == AtomicPathConstraint.FALSE) {
          if (Options.DEBUG)
            Util.Debug("refuted by path constraint");
          makeUnsatCore(constraint);
          this.feasible = false;
          return;
        }
        if (newConstraint != AtomicPathConstraint.TRUE)
          toAdd.add(newConstraint);
        toRemove.add(constraint);
      }
    }

    for (AtomicPathConstraint constraint : toRemove)
      removeConstraint(constraint);
    for (AtomicPathConstraint constraint : toAdd)
      addConstraint(constraint);
  }

  /**
   * adding constraints should always be done through this method
   * 
   * @param constraint
   *          - constraint to add
   * @return - true if constraint was successfully added, false if we already
   *         have it in our set
   */
  boolean addConstraint(AtomicPathConstraint constraint) {
    // decline adding path constraints if we already have more than the max number
    if (constraints.size() >= Options.MAX_PATH_CONSTRAINT_SIZE) {
      Util.Print("not adding constraint " + constraint + " due to size restrictions");
      return true;
    }
    //Util.Print("trying to add constraint " + constraint);
    /*
    if (constraint.isEqualityConstraint()) {
      // other constraints might become more precise from substitution here
      SimplePathTerm lhs = (SimplePathTerm) constraint.getLhs(), rhs = (SimplePathTerm) constraint.getRhs();
      SimplePathTerm nonConstantTerm = null;
      int intTerm = 0;
      if (lhs.isIntegerConstant() && rhs.getObject() != null) {
        substituteExpForVar(lhs, rhs.getObject());
        nonConstantTerm = rhs;
        intTerm = lhs.getIntegerConstant();
      } else if (rhs.isIntegerConstant() && lhs.getObject() != null) {
        substituteExpForVar(rhs, lhs.getObject());
        nonConstantTerm = lhs;
        intTerm = rhs.getIntegerConstant();
      }
      List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
      // if we have a constant inequality constraint on the same var, we should remove it (unless it refutes!)
      for (AtomicPathConstraint c : this.constraints) {
        if (c.isInequalityConstraint()) {
          SimplePathTerm lhs0 = (SimplePathTerm) constraint.getLhs(), rhs0 = (SimplePathTerm) constraint.getRhs();
          if (lhs0.isIntegerConstant() && lhs0.getIntegerConstant() != intTerm && rhs.equals(nonConstantTerm)) toRemove.add(c);
          else if (rhs0.isIntegerConstant() && rhs0.getIntegerConstant() != intTerm && lhs.equals(nonConstantTerm)) toRemove.add(c);
        }
      }
      
      for (AtomicPathConstraint removeMe : toRemove) this.constraints.remove(removeMe);
    } else if (constraint.isInequalityConstraint()) {
      List<AtomicPathConstraint> toAdd = new LinkedList<AtomicPathConstraint>();
      // if we already have an constant equality constraint on the same var, don't want to add the inequality constraint 
      // (unless it refutes!) because it will be less precise
      SimplePathTerm lhs = (SimplePathTerm) constraint.getLhs(), rhs = (SimplePathTerm) constraint.getRhs();
      SimplePathTerm nonConstantTerm = null;
      int intTerm = 0;
      if (lhs.isIntegerConstant()) {
        nonConstantTerm = rhs;
        intTerm = lhs.getIntegerConstant();
      } else if (rhs.isIntegerConstant()) {
        nonConstantTerm = lhs;
        intTerm = rhs.getIntegerConstant();
      }
      if (nonConstantTerm != null) {
        for (AtomicPathConstraint c : this.constraints) {
          if (c.isEqualityConstraint()) {
            SimplePathTerm lhs0 = (SimplePathTerm) c.getLhs(), rhs0 = (SimplePathTerm) c.getRhs();
            if (lhs0.isIntegerConstant() && lhs0.getIntegerConstant() != intTerm && rhs0.equals(nonConstantTerm)) {
              System.out.println("not adding " + constraint + " because we have " + c);
              return true; // skip adding
            } else if (rhs0.isIntegerConstant() && rhs0.getIntegerConstant() != intTerm && lhs0.equals(nonConstantTerm)) {
              System.out.println("not adding " + constraint + " because we have " + c);
              return true;
            } else if (rhs0.equals(nonConstantTerm)) { 
              // we have x == y in the constraints, and our new constraint is y != c for some constant c
              // add constraint x != c as well
              AtomicPathConstraint addMe = new AtomicPathConstraint(lhs0, new SimplePathTerm(intTerm), ConditionalBranchInstruction.Operator.NE);
              Util.Print("adding extra constraint1 " + addMe);
              toAdd.add(addMe);
            } else if (lhs0.equals(nonConstantTerm)) {
              AtomicPathConstraint addMe = new AtomicPathConstraint(rhs0, new SimplePathTerm(intTerm), ConditionalBranchInstruction.Operator.NE);
              Util.Print("adding extra constraint2 " + addMe);
              toAdd.add(addMe);
            }
          }
        }
      }
      for (AtomicPathConstraint addMe : toAdd) this.constraints.add(addMe);
    }
    */
        
    if (constraints.add(constraint)) {
      rebuildZ3Constraints();
      return true;
    }
    return false;
  }

  /**
   * removing constraints should always be done through this method
   * 
   * @param constraint
   *          - constraint to remove
   * @return - true if constraint was successfully removed, false otherwise
   */
  boolean removeConstraint(AtomicPathConstraint constraint) {
    if (constraints.remove(constraint)) {
      rebuildZ3Constraints();
      return true;
    } else {
      for (AtomicPathConstraint con : constraints) {
        Util.Debug(con + " eq " + constraint + " ?" + con.equals(constraint) + " compared " + con.compareTo(constraint));
      }
      Util.Unimp("couldn't remove " + constraint + " from " + Util.printCollection(this.constraints) + " contains? "
          + constraints.contains(constraint));
    }
    return false;
  }

  @Override
  public List<IQuery> returnFromCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    // if (callee.getMethod().isInit()) {
    if (WALACFGUtil.isConstructor(instr)) { // if this is a constructor
      Util.Debug("initializing fields to default values");
      // returning from constructors is a special case because we have to
      // initialize all untouched fields to their default values
      // the "this" var is always v1
      final int THIS = 1;
      PointerVariable thisVar = new ConcretePointerVariable(callee, THIS, this.heapModel); 
      List<FieldReference> toSub = new LinkedList<FieldReference>();
      for (AtomicPathConstraint constraint : constraints) {
        Set<SimplePathTerm> terms = constraint.getTerms();
        for (SimplePathTerm term : terms) {
          if (term.getObject() != null && term.hasField() && term.getObject().equals(thisVar)) {
            toSub.add(term.getFirstField());
          }
        }
      }
      
      // init to default values
      for (FieldReference field : toSub) {
        if (Options.DEBUG) Util.Debug("initializing " + field + " to default value");
        substituteExpForFieldRead(new SimplePathTerm(0), thisVar, field);
        // check if substitution made query infeasible
        if (!this.isFeasible()) return IQuery.INFEASIBLE;
      }
    }
    if (WALACFGUtil.isClassInit(instr) || WALACFGUtil.isConstructor(instr)) {
      if (Options.DEBUG)
        Util.Debug("initializing static fields to default values");
      List<PointerVariable> toSub = new LinkedList<PointerVariable>();
      // initialize static fields to default values
      for (AtomicPathConstraint constraint : constraints) {
        if (constraint.getLhs() instanceof SimplePathTerm) {
          SimplePathTerm constraintLHS = (SimplePathTerm) constraint.getLhs();
          PointerKey ptr = constraintLHS.getPointer();
          if (ptr instanceof StaticFieldKey) {
            StaticFieldKey sfk = (StaticFieldKey) ptr;
            if (sfk.getField().getDeclaringClass().equals(callee.getMethod().getDeclaringClass())) {
              Util.Assert(constraintLHS.getObject() != null, "should have obj here");
              toSub.add(constraintLHS.getObject());
            }
          }
        }

        if (constraint.getRhs() instanceof SimplePathTerm) {
          SimplePathTerm constraintRHS = (SimplePathTerm) constraint.getRhs();
          PointerKey ptr = constraintRHS.getPointer();
          if (ptr instanceof StaticFieldKey) {
            StaticFieldKey sfk = (StaticFieldKey) ptr;
            if (sfk.getField().getDeclaringClass().equals(callee.getMethod().getDeclaringClass())) {
              Util.Assert(constraintRHS.getObject() != null, "should have obj here");
              toSub.add(constraintRHS.getObject());
            }
          }
        }
      }
      for (PointerVariable var : toSub) {
        // we model 0 == null == false all as the integer 0. each is the default
        // value for its respective type
        this.substituteExpForVar(new SimplePathTerm(0), var);
      }
    }

    // done initializing to default values; now do substitution
    if (!substituteActualsForFormals(instr, currentPath.getCurrentNode(), callee, currentPath.getCurrentNode().getIR()
        .getSymbolTable())) {
      return IQuery.INFEASIBLE;
    }
    Util.Post(!this.containsStaleConstraints(callee), "should not contain stale constraints after substitution!");
    return IQuery.FEASIBLE;
  }

  @Override
  public boolean isDispatchFeasible(SSAInvokeInstruction instr, CGNode caller, CGNode callee) {
    if (!callee.getMethod().isStatic()) {
      PointerVariable receiver = Util.makePointerVariable(
          this.heapModel.getPointerKeyForLocal(caller, instr.getReceiver()));
      if (this.pathVars.contains(receiver)) {
        // check for null constraint on receiver
        for (AtomicPathConstraint constraint : this.constraints) {
          if (constraint.isNullConstraintForLocal(receiver)) {
            Util.Debug("refuted by dispatch on null! " + constraint + " " + instr);
            // TODO: ok?
            //this.feasible = false;
            return false;
          }
        }
      }
    }
    return true;
  }
  
  @Override
  public boolean foundWitness() {
    if (fakeWitness) return fakeWitness;
    if (Options.SYNTHESIS) return false;
    return constraints.isEmpty(); // can't have a witness while there are still
                                  // path constraints to produce
  }
  
  // TODO: hack! but z3 really slows things down once it can't decide
  private static boolean z3Panic = false;
  
  @Override
  public boolean isFeasible() {
    if (!feasible) {
      // if (!deleted) ctx.delete(); //occasionally causes Z3 to die
      return false;
    }
    
    if (z3Panic) {
      // problem with z3 -- don't try to use it to check constraints
      return true;
    }
        
    if (currentPathAssumption == null) return true;
    // call Z3 to check for feasibility
    //Z3AST[] assumptionsArr = new Z3AST[] { currentPathAssumption };
    //Boolean result = ctx.checkAssumptionsNoModel(assumptionsArr);
    Expr[] assumptionsArr = new Expr[] { currentPathAssumption };
    Status status = null;
    try {
      status = solver.Check(assumptionsArr);
    } catch (Z3Exception e) {
      Util.Assert(false, "problem with z3 " + e);
    }
    
    //if (result == null) {
    if (status == Status.UNKNOWN) {
      if (Options.DEBUG) Util.Debug("Z3 decidability problem. giving up on z3 checking");
      // z3 can't solve our current constraints. give up
      z3Panic = true;
      return true; 
    } else if (status == Status.UNSATISFIABLE) {
      this.feasible = false;
      if (Options.DEBUG) Util.Debug("refuted by path constraint!");
      //ctx.delete();
      // deleted = true;
      return false;
    }
    // else, sat
    return true;
    //return result;
  }

  @Override
  public boolean addConstraintFromBranchPoint(IBranchPoint point, boolean trueBranchFeasible) {
    return addConstraintFromConditional(point.getInstr(), point.getMethod(), trueBranchFeasible);
  }
  
  @Override
  public boolean addConstraintFromConditional(SSAConditionalBranchInstruction instruction, 
                                               CGNode node, boolean trueBranchFeasible) {
    SymbolTable tbl = node.getIR().getSymbolTable();
    // is this a comparison of constants?
    if (instruction.isIntegerComparison() && tbl.isConstant(instruction.getUse(0)) && tbl.isConstant(instruction.getUse(1))) {
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
      AtomicPathConstraint constraint = getPathConstraintFromGuard(instruction, tbl, node, !trueBranchFeasible);
      if (addConstraint(constraint))
        return isFeasible();
      return true; // else, constraint already in set; no need to check
                   // feasibility
    }
  }

  /**
   * @param instruction
   *          - instruction containing comparison
   * @return - result of comparison between two integer constants
   */
  boolean evaluateGuard(SSAConditionalBranchInstruction instruction, SymbolTable tbl, boolean negate) {
    // Util.Assert(instruction.isIntegerComparison(),
    // "FOUND NON INTEGER COMPARISON");
    Util.Pre(instruction.getNumberOfUses() == 2, "ONLY EXPECTING TWO USES");
    int use0 = instruction.getUse(0), use1 = instruction.getUse(1);
    Util.Assert(tbl.isConstant(use0) && tbl.isConstant(use1), "both need to be constants in order to evaluate!");

    boolean result = false;
    ConditionalBranchInstruction.Operator op = (ConditionalBranchInstruction.Operator) instruction.getOperator();
    if (instruction.isIntegerComparison() || (tbl.isBooleanOrZeroOneConstant(use0) && tbl.isBooleanOrZeroOneConstant(use1))) {
      int lhsValue = tbl.getIntValue(use0), rhsValue = tbl.getIntValue(use1);
      switch (op) {
        case LE:
          result = lhsValue <= rhsValue;
          break;
        case LT:
          result = lhsValue < rhsValue;
          break;
        case EQ:
          result = lhsValue == rhsValue;
          break;
        case NE:
          result = lhsValue != rhsValue;
          break;
        case GE:
          result = lhsValue >= rhsValue;
          break;
        case GT:
          result = lhsValue > rhsValue;
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN GUARD");
      }
    } else if (tbl.isNullConstant(use0) && tbl.isNullConstant(use1)) {
      switch (op) {
        case EQ:
          result = true;
          break;
        case NE:
          result = false;
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " for null comparison IN GUARD");
      }
    } else if (tbl.isDoubleConstant(use0) && tbl.isDoubleConstant(use1)) {
      double lhsValue = tbl.getDoubleValue(use0), rhsValue = tbl.getDoubleValue(use1);
      switch (op) {
        case LE:
          result = lhsValue <= rhsValue;
          break;
        case LT:
          result = lhsValue < rhsValue;
          break;
        case EQ:
          result = lhsValue == rhsValue;
          break;
        case NE:
          result = lhsValue != rhsValue;
          break;
        case GE:
          result = lhsValue >= rhsValue;
          break;
        case GT:
          result = lhsValue > rhsValue;
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN GUARD");
      }
    } else if (tbl.isFloatConstant(use0) && tbl.isFloatConstant(use1)) {
      float lhsValue = tbl.getFloatValue(use0), rhsValue = tbl.getFloatValue(use1);
      switch (op) {
        case LE:
          result = lhsValue <= rhsValue;
          break;
        case LT:
          result = lhsValue < rhsValue;
          break;
        case EQ:
          result = lhsValue == rhsValue;
          break;
        case NE:
          result = lhsValue != rhsValue;
          break;
        case GE:
          result = lhsValue >= rhsValue;
          break;
        case GT:
          result = lhsValue > rhsValue;
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN GUARD");
      }
    } else if (tbl.isLongConstant(use0) && tbl.isLongConstant(use1)) {
      long lhsValue = tbl.getLongValue(use0), rhsValue = tbl.getLongValue(use1);
      switch (op) {
        case LE:
          result = lhsValue <= rhsValue;
          break;
        case LT:
          result = lhsValue < rhsValue;
          break;
        case EQ:
          result = lhsValue == rhsValue;
          break;
        case NE:
          result = lhsValue != rhsValue;
          break;
        case GE:
          result = lhsValue >= rhsValue;
          break;
        case GT:
          result = lhsValue > rhsValue;
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN GUARD");
      }
    } else if (tbl.isStringConstant(use0) && tbl.isStringConstant(use1)) {
      String lhsValue = tbl.getStringValue(use0), rhsValue = tbl.getStringValue(use1);
      switch (op) {
        case EQ:
          result = lhsValue.equals(rhsValue);
          break;
        case NE:
          result = !lhsValue.equals(rhsValue);
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN GUARD");
      }
    } else if ((tbl.isStringConstant(use0) && tbl.isNullConstant(use1)) ||
              (tbl.isNullConstant(use0) && tbl.isStringConstant(use1))) { 
      switch (op) {
        case EQ:
          result = false;
          break;
        case NE:
          result = true;
          break;
        default:
          Util.Assert(false, "UNSUPPORTED OPERATOR " + op + " IN GUARD");
      }
    } else {
      Util.Debug("null const? " + tbl.isNullConstant(use0));
      Util.Debug("number const? " + tbl.isNumberConstant(use0));
      Util.Debug("obj comparison? " + instruction.isObjectComparison());
      Util.Debug("param? " + tbl.isParameter(use0));
      Util.Debug("USE0: " + tbl.getConstantValue(use0));
      Util.Debug("USE1: " + tbl.getConstantValue(use1));
      Util.Unimp("odd comparison " + instruction);
    }

    if (negate) result = !result;
    if (!result) this.feasible = false;
    if (Options.DEBUG) Util.Debug("primitive comparison result: " + result);
    return result;
  }

  /**
   * @param negate
   *          - should we flip the operator in the instruction?
   * @return path constraint extracted from instruction
   */
  AtomicPathConstraint getPathConstraintFromGuard(SSAConditionalBranchInstruction instruction, SymbolTable tbl, CGNode node,
      boolean negate) {
    int uses = instruction.getNumberOfUses();
    Util.Assert(uses == 2, "ONLY TWO USES please");
    Util.Assert(!(tbl.isConstant(instruction.getUse(0)) && tbl.isConstant(instruction.getUse(1))),
        "AT LEAST ONE USE SHOULD NOT BE A CONSTANT!");
    int use0 = instruction.getUse(0), use1 = instruction.getUse(1);

    AtomicPathConstraint constraint;
    ConditionalBranchInstruction.Operator op;
    if (negate)
      op = Util.negateOperator((ConditionalBranchInstruction.Operator) instruction.getOperator());
    else
      op = (ConditionalBranchInstruction.Operator) instruction.getOperator();

    if (tbl.isNullConstant(use0)) {
      PointerVariable var1 = new ConcretePointerVariable(node, use1, this.heapModel);
      constraint = new AtomicPathConstraint(SimplePathTerm.NULL, new SimplePathTerm(var1), op);
    } else if (tbl.isNullConstant(use1)) {
      PointerVariable var0 = new ConcretePointerVariable(node, use0, this.heapModel);
      constraint = new AtomicPathConstraint(new SimplePathTerm(var0), SimplePathTerm.NULL, op);
    } else if (tbl.isIntegerConstant(use0)) { // lhs is integer constant
      PointerVariable var1 = makeVarFromUse(node, use1);
      constraint = new AtomicPathConstraint(new SimplePathTerm(tbl.getIntValue(use0)), new SimplePathTerm(var1), op);
    } else if (tbl.isIntegerConstant(use1)) { // rhs is integer constant
      PointerVariable var0 = makeVarFromUse(node, use0);
      constraint = new AtomicPathConstraint(new SimplePathTerm(var0), new SimplePathTerm(tbl.getIntValue(use1)), op);
    } else if (tbl.isConstant(use0) || tbl.isConstant(use1)) { // one or both
                                                               // vars are some
                                                               // kind of
                                                               // non-int
                                                               // constant
      // Util.Unimp("comparison of non-int constants: " + instruction);
      // TODO: implement this case
      constraint = null; // don't add the constraint
    } else { // both vars are variables
      PointerVariable var0 = makeVarFromUse(node, use0), var1 = makeVarFromUse(node, use1);
      constraint = new AtomicPathConstraint(var0, var1, op);
    }
    return constraint;
  }

  PointerVariable makeVarFromUse(CGNode node, int useNum) {
    return new ConcretePointerVariable(node, useNum, this.heapModel);
  }

  /**
   * substitute actuals for formals in our constraint set (i.e., when returning
   * from call)
   * 
   * @param callerSymbolTable
   *          - symbol table for the caller
   */
  boolean substituteActualsForFormals(SSAInvokeInstruction instr, CGNode callerMethod, CGNode calleeMethod,
      SymbolTable callerSymbolTable) {
    //Util.Pre(!calleeMethod.equals(callerMethod), "recursion should be handled elsewhere");
    if (Options.DEBUG)
      Util.Debug("substituting actuals for formals in path query");
    for (int i = 0; i < instr.getNumberOfParameters(); i++) {
      PointerVariable formal = new ConcretePointerVariable(calleeMethod, i + 1, this.heapModel);
      int use = instr.getUse(i);
      if (i == -1)
        continue; // insurance for WALA crash that sometimes happens here
      SimplePathTerm actual = null;
      if (callerSymbolTable.isIntegerConstant(use))
        actual = new SimplePathTerm(callerSymbolTable.getIntValue(use));
      else if (callerSymbolTable.isNullConstant(use))
        actual = SimplePathTerm.NULL;
      else if (callerSymbolTable.isStringConstant(use))
        actual = SimplePathTerm.NON_NULL; // the only modeling we do of strings
                                          // is that they are non-null
      else if (callerSymbolTable.isConstant(use)) {
        // TODO: implement other kinds of constants. for now, just drop
        dropConstraintsContaining(formal);
        continue;
      } else
        actual = new SimplePathTerm(
            new ConcretePointerVariable(callerMethod, instr.getUse(i), this.heapModel));
      if (Options.DEBUG)
        Util.Debug("subbing " + actual + " for " + formal);
      substituteExpForVar(actual, formal);
    }
    return isFeasible();
  }

  /**
   * substitute formals for actuals in our constraint set (i.e., when entering
   * call
   */
  boolean substituteFormalsForActuals(SSAInvokeInstruction instr, CGNode callerMethod, CGNode calleeMethod) {
    //Util.Pre(!calleeMethod.equals(callerMethod), "recursion should be handled elsewhere");
    if (Options.DEBUG)
      Util.Debug("substituting formals for actuals in path query");
    for (int i = 0; i < instr.getNumberOfParameters(); i++) {
      PointerVariable actual = new ConcretePointerVariable(callerMethod, instr.getUse(i), this.heapModel);
      PointerVariable formal = new ConcretePointerVariable(calleeMethod, i + 1, this.heapModel);
      SimplePathTerm formalTerm = new SimplePathTerm(formal);
      substituteExpForVar(formalTerm, actual);
    }
    return isFeasible();
  }

  @Override
  public List<IQuery> enterCall(SSAInvokeInstruction instr, CGNode callee, IPathInfo currentPath) {
    boolean result = substituteFormalsForActuals(instr, currentPath.getCurrentNode(), callee);
    if (!result)
      return IQuery.INFEASIBLE;
    result = visit(instr, callee, currentPath.getCurrentNode());
    if (!result)
      return IQuery.INFEASIBLE;
    return IQuery.FEASIBLE;
  }

  // nothing to do here
  @Override
  public void enterCallFromJump(CGNode callee) { }

  @Override
  public List<IQuery> visitPhi(SSAPhiInstruction instr, int phiIndex, IPathInfo currentPath) {
    CGNode currentMethod = currentPath.getCurrentNode();
    // lhsVar is the x in x = phi(y,z)
    PointerVariable lhsVar = new ConcretePointerVariable(currentMethod, instr.getDef(), this.heapModel); 

    if (pathVars.contains(lhsVar)) {
      Util.Assert(instr.getNumberOfDefs() == 1, "expecting one def");
      int use = instr.getUse(phiIndex);
      SymbolTable tbl = currentPath.getCurrentNode().getIR().getSymbolTable();
      SimplePathTerm toSub = null;
      if (tbl.isIntegerConstant(use))
        toSub = new SimplePathTerm(tbl.getIntValue(use));
      else if (tbl.isNullConstant(use))
        toSub = SimplePathTerm.NULL;
      else if (tbl.isStringConstant(use))
        toSub = SimplePathTerm.NON_NULL; // the only modeling we do of strings
                                         // is that they are non-nul
      else if (tbl.isConstant(use))
        Util.Unimp("other kinds of constants"); // TODO: support other constants
      // one of the y_i's in x = phi(y_1,y_2,...)
      else
        toSub = new SimplePathTerm(new ConcretePointerVariable(currentMethod, use, this.heapModel));
      substituteExpForVar(toSub, lhsVar); // sub the LHS of the phi for the
                                          // appropriate term on the right
      if (!isFeasible()) {
        this.feasible = false;
        return IQuery.INFEASIBLE;
      }
    }
    return IQuery.FEASIBLE;
  }
  
  public boolean visit(SSAInvokeInstruction instr, CGNode currentNode) {
    Util.Pre(Options.SYNTHESIS);
    if (instr.hasDef()) {
      Util.Assert(!instr.isStatic()); // unimplemented for now
      HeapModel hm = this.heapModel;
   
      ConcretePointerVariable receiver = new ConcretePointerVariable(currentNode, instr.getUse(0), hm);
      // special ghost variable corresponding to the call
      FieldReference ghost = FieldReference.findOrCreate(instr.getDeclaredTarget().getDeclaringClass().getClassLoader(), 
                                                         instr.getDeclaredTarget().getDeclaringClass().getName().toString(),
                                                         instr.getDeclaredTarget().getSelector().toString(),
                                                         instr.getDeclaredResultType().getName().toString());  
      substituteExpForVar(new SimplePathTerm(receiver, ghost), new ConcretePointerVariable(currentNode, instr.getDef(), hm));
    }
    return true;
  }

  @Override
  public List<IQuery> visit(SSAInstruction instr, IPathInfo currentPath) {
    CGNode node = currentPath.getCurrentNode();
    SymbolTable tbl = currentPath.getCurrentNode().getIR().getSymbolTable();
    boolean result = false;

    if (instr instanceof SSAArrayStoreInstruction)
      result = visit((SSAArrayStoreInstruction) instr, node, tbl);
    else if (instr instanceof SSAUnaryOpInstruction)
      result = visit((SSAUnaryOpInstruction) instr, node);
    else if (instr instanceof SSAArrayLengthInstruction)
      result = visit((SSAArrayLengthInstruction) instr, node);
    else if (instr instanceof SSAArrayLoadInstruction)
      result = visit((SSAArrayLoadInstruction) instr, node, tbl);
    else if (instr instanceof SSABinaryOpInstruction)
      result = visit((SSABinaryOpInstruction) instr, node, tbl);
    else if (instr instanceof SSACheckCastInstruction)
      result = visit((SSACheckCastInstruction) instr, node);
    else if (instr instanceof SSAGetInstruction)
      result = visit((SSAGetInstruction) instr, node);
    else if (instr instanceof SSAPutInstruction)
      result = visit((SSAPutInstruction) instr, node, tbl);
    else if (instr instanceof SSAGotoInstruction)
      return IQuery.FEASIBLE; // goto's are a nop for us
    else if (instr instanceof SSASwitchInstruction)
      //result = visit((SSASwitchInstruction) instr, node, tbl);
      return IQuery.FEASIBLE; // switch is a nop
    else if (instr instanceof SSALoadMetadataInstruction)
      result = visit((SSALoadMetadataInstruction) instr, node);
    else if (instr instanceof SSAConversionInstruction)
      result = visit((SSAConversionInstruction) instr, node);
    else if (instr instanceof SSAInstanceofInstruction)
      result = visit((SSAInstanceofInstruction) instr, node);
    else if (instr instanceof SSAComparisonInstruction)
      result = visit((SSAComparisonInstruction) instr, node, tbl);
    else if (instr instanceof SSAMonitorInstruction)
      return IQuery.FEASIBLE; // have no idea what this is. nop!
    else if (instr instanceof SSAGetCaughtExceptionInstruction)
      return IQuery.FEASIBLE; // TODO: handle this properly
    else if (instr instanceof SSAThrowInstruction)
      result = visit((SSAThrowInstruction) instr, node);
    else if (instr instanceof SSAInvokeInstruction) {
      //Util.Assert(false, "should this happen?");
      result = visit((SSAInvokeInstruction) instr, node);
    } else if (instr instanceof SSANewInstruction)
      result = visit((SSANewInstruction) instr, node, tbl);
    else if (instr instanceof SSAReturnInstruction)
      result = visit((SSAReturnInstruction) instr, node, tbl);
    // else if (instr instanceof SSAStoreIndirectInstruction) return
    // query.visit((SSAStoreIndirectInstruction) instr);

    else {
      Util.Unimp("visiting instr " + instr);
    }
    /*
     * // SANITY CHECK Iterator<AtomicPathConstraint> iter =
     * constraints.descendingIterator(); AtomicPathConstraint last = null; while
     * (iter.hasNext()) { AtomicPathConstraint next = iter.next(); if (last !=
     * null) { Util.Assert(last.compareTo(next) > 0, "constraint " + last +
     * " not greater than " + next); } last = next; }
     */

    if (!result) {
      this.feasible = false;
      return IQuery.INFEASIBLE;
    }
    return IQuery.FEASIBLE;
  }

  // no context-sensitivity to reflect in path constraints
  @Override
  public boolean addContextualConstraints(CGNode node, IPathInfo currentPath) {
    return true;
  }

  @Override
  public void declareFakeWitness() {
    this.fakeWitness = true;
  }

  @Override
  public void intersect(IQuery other) {
    Util.Assert(other instanceof PathQuery, "intersecting with non-PathQuery " + other.getClass());
    PathQuery otherQuery = (PathQuery) other;
    this.constraints.retainAll(otherQuery.constraints);
    rebuildZ3Constraints();
  }

  public boolean symbContains(PathQuery other) {
    if (other.constraints.isEmpty()) return true;
    if (this.constraints.isEmpty()) return false;
    Status result = null;
    try {
      // TODO: refactor to use existing context
      // temporary context for performing implication checking
      //final Z3Context tmp = new Z3Context(new Z3Config());
      Context tmp = new Context();
      //final Z3AST[] conjuncts0 = new Z3AST[constraints.size()], conjuncts1 = new Z3AST[other.constraints.size()];
      final BoolExpr[] conjuncts0 = new BoolExpr[constraints.size()], conjuncts1 = new BoolExpr[other.constraints.size()];
      
      int i = 0;
      for (AtomicPathConstraint constraint : this.constraints) {
        //conjuncts0[i++] = constraint.toZ3AST(tmp);
        conjuncts0[i++] = (BoolExpr) constraint.toZ3AST(tmp);
      }
      i = 0;
      for (AtomicPathConstraint constraint : other.constraints) {
        //conjuncts1[i++] = constraint.toZ3AST(tmp);
        conjuncts1[i++] = (BoolExpr) constraint.toZ3AST(tmp);
      }
   
      //final Z3AST implLHS = tmp.mkAnd(conjuncts0);
      //final Z3AST implRHS = tmp.mkAnd(conjuncts1);
      final BoolExpr implLHS = tmp.MkAnd(conjuncts0), implRHS = tmp.MkAnd(conjuncts1);
      // ask: is there some assignment for which LHS does not imply RHS?
      Solver s = tmp.MkSolver();
      s.Assert(tmp.MkNot(tmp.MkImplies(implLHS, implRHS)));
      //tmp.assertCnstr(tmp.mkNot(tmp.mkImplies(implLHS, implRHS)));
      // if not, then we know LHS => RHS for all values
      //boolean result = !tmp.check();
      result = s.Check();

      if (result == Status.UNKNOWN) {
        Util.Assert(false, "z3 decidability problem");
        return false;
      } else {
        boolean boolResult = result == Status.UNSATISFIABLE;
        tmp.Dispose();
        return boolResult;
      }
    } catch (Z3Exception e) {
      Util.Assert(false, " problem with z3 " + e);
      return false;
    }
    
    
    //tmp.delete();
    //return result;//!tmp.check();
  }

  @Override
  public void removeAllLocalConstraints() {
    List<AtomicPathConstraint> toRemove = new LinkedList<AtomicPathConstraint>();
    for (AtomicPathConstraint constraint : constraints) {
      for (PointerVariable var : constraint.getVars()) {
        if (var.isLocalVar())
          toRemove.add(constraint);
        break;
      }
    }
    for (AtomicPathConstraint constraint : toRemove) {
      if (Options.DEBUG)
        Util.Debug("removing local constraint " + constraint);
      removeConstraint(constraint);
      // constraints.remove(constraint);
    }
  }

  @Override
  public void intializeStaticFieldsToDefaultValues() {
    Set<PointerVariable> toSub = HashSetFactory.make(); //new HashSet<PointerVariable>();
    for (PointerVariable var : pathVars) {
      if (var.getInstanceKey() instanceof StaticFieldKey)
        toSub.add(var);
    }

    for (PointerVariable var : toSub) {
      substituteExpForVar(new SimplePathTerm(0), var);
    }
  }
  
  @Override
  public boolean addPathConstraintFromSwitch(SSAConditionalBranchInstruction switchCase, CGNode currentNode, boolean negated) {
    IConditionalBranchInstruction.Operator op = negated ? ConditionalBranchInstruction.Operator.NE :  ConditionalBranchInstruction.Operator.EQ;
    SimplePathTerm matchedTerm = new SimplePathTerm(new ConcretePointerVariable(currentNode, switchCase.getUse(0), this.heapModel));
    //AtomicPathConstraint switchConstraint = new AtomicPathConstraint(matchedTerm, new SimplePathTerm(switchCase.getUse(1)), op);
    SymbolTable tbl = currentNode.getIR().getSymbolTable();
    Util.Assert(tbl.isIntegerConstant(switchCase.getUse(1)));
    AtomicPathConstraint switchConstraint = new AtomicPathConstraint(matchedTerm, new SimplePathTerm(tbl.getIntValue(switchCase.getUse(1))), op);
    Util.Assert(isFeasible());
    Util.Print("adding switch constraint " + switchConstraint);
    this.addConstraint(switchConstraint);
    return isFeasible();
  }
  
  @Override
  public List<IQuery> addPathConstraintFromSwitch(SSASwitchInstruction instr, SSACFG.BasicBlock lastBlock, CGNode currentNode) {
    IR ir = currentNode.getIR();
    SSACFG cfg = ir.getControlFlowGraph();
    SymbolTable tbl = ir.getSymbolTable();
    // TODO: handle the easy case where we switch on a constant
    Util.Assert(!tbl.isConstant(instr.getUse(0)));
    // TODO: exclude string/byte/enum cases?

    // instr is switch(switchTarget)
    PointerVariable switchTarget = new ConcretePointerVariable(currentNode, instr.getUse(0), this.heapModel);
    SimplePathTerm switchTargetTerm = new SimplePathTerm(switchTarget);
           
    List<IQuery> cases = new ArrayList<IQuery>();
    int[] casesAndLabels = instr.getCasesAndLabels();
    
    if (cfg.getBlockForInstruction(instr.getDefault()) == lastBlock) {
      // this is the default label. add negation of all other cases
      for (int i = 0; i < casesAndLabels.length; i += 2) {
        AtomicPathConstraint negated = new AtomicPathConstraint(switchTargetTerm, new SimplePathTerm(casesAndLabels[i]), 
            ConditionalBranchInstruction.Operator.NE); 
        this.addConstraint(negated);
      }
      if (isFeasible()) return IQuery.FEASIBLE;
      return IQuery.INFEASIBLE;
    } // else, not the default label
    
    boolean first = true, found = false;
    // copy to make copies of
    PathQuery original = this.deepCopy();
    for (int i = 0; i < casesAndLabels.length; i += 2) {
      // find the switch cases that dispatch to the last block we visited
      if (cfg.getBlockForInstruction(casesAndLabels[i + 1]) == lastBlock) {
        found = true;
        PathQuery copy;
        if (first) {
          copy = this;
          first = false;
        } else {
          copy = original.deepCopy();
          cases.add(copy);
        }
        
        // create a path constraint based on this label        
        AtomicPathConstraint switchConstraint = new AtomicPathConstraint(switchTargetTerm, new SimplePathTerm(casesAndLabels[i]), 
                                                                         ConditionalBranchInstruction.Operator.EQ);
        copy.addConstraint(switchConstraint);
        Util.Assert(copy.isFeasible(), "adding constraint " + switchConstraint + " to " + copy + " made it infeasible"); // need to do something fancier if one of these is infeasible
      }
    }
  
    Util.Assert(found, "couldn't find label for " + this + " last block " + lastBlock + " IR " + ir);
    return cases;
  }
  
  /**
   * return the set of methods that can potentially produce / affect some part
   * of this query
   */
  @Override
  public Map<Constraint, Set<CGNode>> getModifiersForQuery() {
    Map<PointerKey, Set<CGNode>> reversedModRef = this.depRuleGenerator.getReversedModRef();
    Map<Constraint, Set<CGNode>> constraintModMap = HashMapFactory.make(); 
    for (AtomicPathConstraint constraint : this.constraints) {
      Set<CGNode> nodes = HashSetFactory.make();
      Util.Debug("getting pointer keys for " + constraint);
      for (PointerKey key : constraint.getPointerKeys(this.depRuleGenerator)) {
        Util.Debug("POINTER KEY " + key);
        nodes.addAll(reversedModRef.get(key));
      }
      constraintModMap.put(constraint, nodes);
    }

    return constraintModMap;
  }
  
  @Override
  public Map<Constraint, Set<CGNode>> getRelevantNodes() {
    Map<Constraint, Set<CGNode>> constraintRelevantMap = HashMapFactory.make();
    IClassHierarchy cha = this.depRuleGenerator.getClassHierarchy();
    HeapGraph hg = this.depRuleGenerator.getHeapGraph();
    for (AtomicPathConstraint constraint : this.constraints) {
      Set<CGNode> nodes = HashSetFactory.make();
      for (SimplePathTerm term : constraint.getTerms()) {
        if (!term.isIntegerConstant()) {
          // TODO: how to handle multiple fields?
          Util.Assert(term.getFields() == null || term.getFields().size() == 1);
          PointerVariable var = term.getObject();
          
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
  

  void makeUnsatCore(AtomicPathConstraint constraint) {
    unsatCore = new LinkedList<AtomicPathConstraint>();
    unsatCore.add(constraint);
  }

  public List<AtomicPathConstraint> getUnsatCore() {
    Util.Pre(!this.feasible, "can't get unsat core for feasible query!");
    // return core if we've already constructed it via evaluating a constraint
    // to false
    if (unsatCore != null)
      return unsatCore;
    // else, unsatisfiability came from Z3; use it to construct unsat core
    Util.Unimp("getting constraints from z3 unsat core");
    // Z3AST[] core = new Z3AST[1];
    // this.ctx.checkAssumptions(this.currentPathAssumption, new Z3Model(),
    // core);
    return null;
  }
  
  @Override
  public List<DependencyRule> getWitnessList() {
    return null;
  }
  
  @Override
  public AbstractDependencyRuleGenerator getDepRuleGenerator() { 
    return depRuleGenerator;
  }
  
  @Override
  public Iterator<? extends Constraint> constraints() {
    return constraints.iterator();
  }

  @Override
  public boolean containsConstraint(Constraint constraint) {
    if (!(constraint instanceof AtomicPathConstraint))
      return false;
    /*
     * int id = ((AtomicPathConstraint) constraint).getId(); // TODO: this can
     * be made more efficient... for (AtomicPathConstraint con :
     * this.constraints) { if (con.getId() == id) return true; } return false;
     */
    return this.constraints.contains(constraint);
  }
  
  @Override
  public Set<FieldReference> getFields() {
    Set<FieldReference> fields = HashSetFactory.make();
    for (AtomicPathConstraint constraint : this.constraints) {
      fields.addAll(constraint.getFields());
    }
    return fields;
  }

  @Override
  public boolean contains(IQuery other) {
    if (!(other instanceof PathQuery))
      return false;
    PathQuery otherQuery = (PathQuery) other;
    return this.constraints.containsAll(otherQuery.constraints);
  }

  @Override
  public String toString() {
    String s = "{ (";
    for (AtomicPathConstraint constraint : constraints) {
      s = s + " " + constraint.toHumanReadableString() + " ^ ";
    }
    s = s + ") }";
    return s;
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
    PathQuery other = (PathQuery) obj;
    if (constraints == null) {
      if (other.constraints != null)
        return false;
    } else if (!constraints.equals(other.constraints))
      return false;
    return true;
  }

}

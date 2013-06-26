package edu.colorado.thresher.core;

import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

import z3.java.Z3AST;
import z3.java.Z3Context;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.util.collections.HashSetFactory;

/**
 * disjunct-free path constraint
 * 
 * @author sam
 */

public class AtomicPathConstraint implements Constraint { // , Comparable {
  public static boolean DEBUG = Options.DEBUG;

  public static AtomicPathConstraint TRUE = new AtomicPathConstraint();
                                                                       
  public static AtomicPathConstraint FALSE = new AtomicPathConstraint();
                                                                        
  final PathTerm lhs, rhs;
  final Set<PointerVariable> vars;
  final ConditionalBranchInstruction.Operator op;
  // final String uniqueId;
  boolean substituted = false;

  private final int id; // unique constraint id that persists across
                        // substitution
  private final int hash;
  private static int idCounter = 0;

  public AtomicPathConstraint() {
    this.lhs = null;
    this.rhs = null;
    this.vars = null;
    this.op = null;
    this.id = idCounter++;
    this.hash = makeHash();
    // this.uniqueId = "id";
  }

  // public constructors for creating entirely new constraints
  public AtomicPathConstraint(PointerVariable lhs, PointerVariable rhs, ConditionalBranchInstruction.Operator op) {
    this(lhs, rhs, op, idCounter++);
  }

  public AtomicPathConstraint(PathTerm lhs, PathTerm rhs, ConditionalBranchInstruction.Operator op) {
    this(lhs, rhs, op, idCounter++);
  }

  // private constructors for maintaining id across substitution
  private AtomicPathConstraint(PointerVariable lhs, PointerVariable rhs, ConditionalBranchInstruction.Operator op, int id) {
    Util.Assert(lhs != null && rhs != null, "CAN'T CONSTRUCT A PATH VAR FROM NULL!");
    // TODO: maintain canonical forms here
    /*
     * // maintain canonical form; vars should be lexicographically ordered if
     * (lhs.compareTo(rhs) > 0) { // lhs is lexicographically greater than
     * rhs...flip it this.lhs = new SimplePathTerm(rhs); this.rhs = new
     * SimplePathTerm(lhs); if (Util.isCommutative(op)) this.op = op; else
     * this.op = Util.reverseOperator(op); } else { this.lhs = new
     * SimplePathTerm(lhs); this.rhs = new SimplePathTerm(rhs); this.op = op; }
     */
    this.lhs = new SimplePathTerm(lhs);
    this.rhs = new SimplePathTerm(rhs);
    this.op = op;
    this.id = id;
    this.vars = HashSetFactory.make();
    vars.add(lhs);
    vars.add(rhs);
    this.hash = makeHash();
  }

  private AtomicPathConstraint(PathTerm lhs, PathTerm rhs, ConditionalBranchInstruction.Operator op, int id) {
    Util.Assert(lhs != null && rhs != null, "PATH VARIABLES CANNOT BE NULL!");
    // TODO: maintain canonical forms here
    /*
     * // maintain canonical form; terms should be lexicographically ordered if
     * (lhs.compareTo(rhs) > 0) { // lhs is lexicographically greater than
     * rhs...flip it this.lhs = rhs; this.rhs = lhs; if (Util.isCommutative(op))
     * this.op = op; else this.op = Util.reverseOperator(op); } else { this.lhs
     * = lhs; this.rhs = rhs; this.op = op; }
     */
    this.lhs = lhs;
    this.rhs = rhs;
    this.op = op;
    this.id = id;
    this.vars = HashSetFactory.make();
    vars.addAll(lhs.getVars());
    vars.addAll(rhs.getVars());
    this.hash = makeHash();
    
    if (Options.DEBUG) {
      // sanity check to make sure path conditions aren't growing extremely large
      if (lhs.size() > 8 || rhs.size() > 8) {
        Util.Assert(false, "unusually large path constraint " + this + "; possible nontermination");
      }
    }
    
  }

  public AtomicPathConstraint heapSubstitute(SimplePathTerm toSub, SimplePathTerm subFor) {
    //Util.Debug("heapSub: toSub " + toSub + " subFor " + subFor);
    Util.Pre(!toSub.isIntegerConstant(), "constants should be subsituted using different method");
    PathTerm newLHS = lhs.heapSubstitute(toSub, subFor);
    boolean lhsSubstituted = newLHS.substituted(); // DO NOT MOVE THIS! if lhs
                                                   // and rhs are the same,
                                                   // mutability of PathTerms
                                                   // can cause unexpected
                                                   // behavior
    PathTerm newRHS = rhs.heapSubstitute(toSub, subFor);
    boolean rhsSubstituted = newRHS.substituted();
    if (lhsSubstituted || rhsSubstituted) {
      AtomicPathConstraint newPathConstraint = new AtomicPathConstraint(newLHS, newRHS, op, id);
      if (newPathConstraint.isConstant()) {
        Util.Debug("evaluating!");
        if (newPathConstraint.evaluate())
          newPathConstraint = TRUE;// makeTruePathConstraint(); // constraint
                                   // evaluated to true
        else
          newPathConstraint = FALSE; // makeFalsePathConstraint(); // constraint
                                     // evaluated to false
      } // normal case; no evaluation
      newPathConstraint.setSubstituted(true);
      return newPathConstraint;
    } else {
      this.setSubstituted(false);
      // AtomicPathConstraint tmp = new
      // AtomicPathConstraint(this.lhs.deepCopy(), this.rhs.deepCopy(), op);
      // tmp.setSubstituted(false);
      // return tmp;
      return this;
    }
  }

  public AtomicPathConstraint substitute(PathTerm toSub, SimplePathTerm subFor) {
    PathTerm newLHS = lhs.substitute(toSub, subFor);
    // DO NOT MOVE THIS! if lhs and rhs of the same, mutability of PathTerms can
    // cause unexpected behavior
    boolean lhsSubstituted = newLHS.substituted();
    PathTerm newRHS = rhs.substitute(toSub, subFor);
    boolean rhsSubstituted = newRHS.substituted();
    if (lhsSubstituted || rhsSubstituted) {
      // normal case; no evaluation
      AtomicPathConstraint newPathConstraint = new AtomicPathConstraint(newLHS, newRHS, op, id); 
      if (newPathConstraint.isConstant()) {
        Util.Debug("evaluating!");
        if (newPathConstraint.evaluate())
          newPathConstraint = TRUE; // constraint evaluated to true
        else
          newPathConstraint = FALSE; // constraint evaluated to false
      } // normal case; no evaluation
      newPathConstraint.setSubstituted(true);
      return newPathConstraint;
    } else {
      this.setSubstituted(false);
      return this;
    }
  }

  /**
   * substitute the expression toSub for the field read subFor.subForFieldName
   * 
   * @return - a new path constraint if substitution occurred, the same
   *         constraint otherwise
   */
  public AtomicPathConstraint substituteExpForFieldRead(SimplePathTerm toSub, PointerVariable subFor, FieldReference fieldName) {
    PathTerm newLHS = lhs.substituteExpForFieldRead(toSub, subFor, fieldName);
    if (newLHS == SimplePathTerm.FALSE) { // refuted by subbing null for a field
                                          // that's deref'd in the constraints
      AtomicPathConstraint newPathConstraint = FALSE;
      newPathConstraint.setSubstituted(true);
      return newPathConstraint;
    }
    boolean lhsSubstituted = newLHS.substituted(); // DO NOT MOVE THIS! if lhs
                                                   // and rhs are the same,
                                                   // mutability of PathTerms
                                                   // can cause unexpected
                                                   // behavior
    PathTerm newRHS = rhs.substituteExpForFieldRead(toSub, subFor, fieldName);
    if (newRHS == SimplePathTerm.FALSE) { // refuted by subbing null for a field
                                          // that's deref'd in the constraints
      AtomicPathConstraint newPathConstraint = FALSE;
      newPathConstraint.setSubstituted(true);
      return newPathConstraint;
    }
    boolean rhsSubstituted = newRHS.substituted(); // DO NOT MOVE THIS! if lhs
                                                   // and rhs are the same,
                                                   // mutability of PathTerms
                                                   // can cause unexpected
                                                   // behavior
    if (lhsSubstituted || rhsSubstituted) {
      AtomicPathConstraint newPathConstraint = new AtomicPathConstraint(newLHS, newRHS, op, id);
      if (newPathConstraint.isConstant()) {
        if (newPathConstraint.evaluate())
          newPathConstraint = TRUE;// makeTruePathConstraint(); // constraint
                                   // evaluated to true
        else
          newPathConstraint = FALSE; // makeFalsePathConstraint(); // constraint
                                     // evaluated to false
      } // normal case; no evaluation
      newPathConstraint.setSubstituted(true);
      return newPathConstraint;
    } else {
      this.setSubstituted(false);
      return this;
    }
  }

  public AtomicPathConstraint deepCopy() {
    return this;
  } // ok since AtomicPathConstraints are immutable

  public boolean symbContains(AtomicPathConstraint other) {
    return this.op.equals(other.op) && lhs.symbContains(other.lhs) && rhs.symbContains(other.rhs);
  }

  // public boolean isConstant() { return lhs.isNullConstant() ||
  // rhs.isNullConstant() || (lhs.isIntegerConstant() &&
  // rhs.isIntegerConstant()); }
  // public boolean isConstant() { return (lhs.isIntegerConstant() &&
  // rhs.isIntegerConstant()); }
  public boolean isConstant() {
    if (lhs.isIntegerConstant() && rhs.isIntegerConstant()) return true;
    else if (this.op == ConditionalBranchInstruction.Operator.EQ || 
             this.op == ConditionalBranchInstruction.Operator.NE) {
      return (lhs.isIntegerConstant() && rhs.isHeapLocation()) ||
             (lhs.isHeapLocation() && rhs.isIntegerConstant());
    }
    return false;
  }

  public boolean isSimple() {
    return this.lhs instanceof SimplePathTerm && this.rhs instanceof SimplePathTerm;
  }

  public boolean substituted() {
    return substituted;
  }

  public void setSubstituted(boolean substituted) {
    this.substituted = substituted;
  }

  public PathTerm getLhs() {
    return lhs;
  }

  public PathTerm getRhs() {
    return rhs;
  }

  public ConditionalBranchInstruction.Operator getOp() {
    return op;
  }

  // @Override
  public int getId() {
    return id;
  }

  public String toHumanReadableString() {
    return lhs.toHumanReadableString() + " " + Util.opToString(op) + " " + rhs.toHumanReadableString();
    // return lhs.toString() + " " + Util.opToString(op) + " " + rhs.toString();
  }

  public Set<PointerVariable> getVars() {
    return vars;
  }

  /**
   * constraint consists of constants; we can evaluate it
   * 
   * @return result of constraint evaluation
   */
  boolean evaluate() {
    if (lhs.isIntegerConstant() && rhs.isIntegerConstant()) {
      switch (this.op) {
        case LT:
          return lhs.evaluate() < rhs.evaluate();
        case LE:
          return lhs.evaluate() <= rhs.evaluate();
        case GT:
          return lhs.evaluate() > rhs.evaluate();
        case GE:
          return lhs.evaluate() >= rhs.evaluate();
        case EQ:
          return lhs.evaluate() == rhs.evaluate();
        case NE:
          return lhs.evaluate() != rhs.evaluate();
        default:
          Util.Unimp("evaluating op " + op);
      }
    } else if (lhs.isIntegerConstant() && rhs.isHeapLocation()) { 
      int lhsVal = ((SimplePathTerm) lhs).getIntegerConstant();
      switch (this.op) {
        case EQ: return lhsVal != 0 ; // we had heapLoc == lhsVal; lhsVal can't be zero or we refute
        case NE: return lhsVal == 0; // we had heapLoc != lhsVal; lhsVal must zero or we refute
        default:  Util.Unimp("unsupported op for obj comparison " + op);
      }
    } else if (lhs.isHeapLocation() && rhs.isIntegerConstant()) {
      int rhsVal = ((SimplePathTerm) rhs).getIntegerConstant();
      switch (this.op) {
        case EQ: return rhsVal != 0 ; // we had heapLoc == lhsVal; lhsVal can't be zero or we refute
        case NE: return rhsVal == 0; // we had heapLoc != lhsVal; lhsVal must zero or we refute
        default:  Util.Unimp("unsupported op for obj comparison " + op);
      }
    }
    Util.Unimp("should not be evaluating non-const constraint " + this);
    return true;
  }

  public Z3AST toZ3AST(Z3Context ctx) {
    Z3AST z3LHS = lhs.toZ3AST(ctx, false);
    Z3AST z3RHS = rhs.toZ3AST(ctx, false);

    switch (this.op) {
      case LT:
        return ctx.mkLT(z3LHS, z3RHS);
      case LE:
        return ctx.mkLE(z3LHS, z3RHS);
      case GT:
        return ctx.mkGT(z3LHS, z3RHS);
      case GE:
        return ctx.mkGE(z3LHS, z3RHS);
      case EQ:
        return ctx.mkEq(z3LHS, z3RHS);
      case NE:
        return ctx.mkNot(ctx.mkEq(z3LHS, z3RHS));
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return null;
  }

  public Set<SimplePathTerm> getTerms() {
    Set<SimplePathTerm> set = new TreeSet<SimplePathTerm>();
    set.addAll(lhs.getTerms());
    set.addAll(rhs.getTerms());
    return set;
  }

  public static AtomicPathConstraint makeFalsePathConstraint() {
    return new AtomicPathConstraint(new SimplePathTerm(0), new SimplePathTerm(0), ConditionalBranchInstruction.Operator.NE);
  }

  public static AtomicPathConstraint makeTruePathConstraint() {
    return new AtomicPathConstraint(new SimplePathTerm(0), new SimplePathTerm(0), ConditionalBranchInstruction.Operator.EQ);
  }
  
  /**
   * is this a constraint of the form var == 0?
   */
  public boolean isNullConstraintForLocal(PointerVariable var) {
    Util.Pre(var.isLocalVar());
    if (this.vars.contains(var) && this.getFields() == null || this.getFields().isEmpty()) {
      if (this.op == ConditionalBranchInstruction.Operator.EQ) {
        if (this.lhs == SimplePathTerm.NULL) {
          if (this.rhs instanceof SimplePathTerm) {
            return ((SimplePathTerm) rhs).getObject().equals(var);
          }
        } else if (this.rhs == SimplePathTerm.NULL) {
          if (this.lhs instanceof SimplePathTerm) {
            return ((SimplePathTerm) lhs).getObject().equals(var);
          }
        }
      }
    }
    return false;
  }
  
  /**
   * is this a constraint of the form var == 0 or var.f == 0?
   */
  public boolean isNullConstraintFor(PointsToEdge edge) {
    if (this.vars.contains(edge.getSource())) {
      if (this.op == ConditionalBranchInstruction.Operator.EQ) {
        if (this.lhs == SimplePathTerm.NULL) {
          if (this.rhs instanceof SimplePathTerm) {
            return Util.equal(((SimplePathTerm) rhs).getFirstField(), 
                                edge.getFieldRef());
          }
        } else if (this.rhs == SimplePathTerm.NULL) {
          if (this.lhs instanceof SimplePathTerm) {
            return Util.equal(((SimplePathTerm) lhs).getFirstField(), 
                edge.getFieldRef());
          }
        }
      }
    }
    return false;
  }
  
  public boolean isPointsToConstraint() {
    return (this.op == ConditionalBranchInstruction.Operator.EQ ||
           this.op == ConditionalBranchInstruction.Operator.NE) &&
           (this.lhs.isHeapLocation() ||
           this.rhs.isHeapLocation());
  }
  
  public PointsToEdge makePointsToEdge(HeapGraph hg) {
    Util.Pre(isPointsToConstraint());
    Set<PointerVariable> heapVars, localVars;    
    
    if (this.lhs.isHeapLocation()) {
      heapVars = this.lhs.getVars();
      localVars = this.rhs.getVars();
    } else {
      heapVars = this.rhs.getVars();
      localVars = this.lhs.getVars();
    }
    
    Util.Assert(heapVars.size() == 1);
    Util.Assert(localVars.size() == 1);
    PointerVariable lhs = localVars.iterator().next();
    PointerVariable rhs = heapVars.iterator().next();
    Util.Assert(lhs.isLocalVar());
    Util.Assert(rhs.isHeapVar());
    
    if (this.op == ConditionalBranchInstruction.Operator.NE) {
      // negative pts-to constraint; change heapVars to be pt(localVars) \ heapVars
      Set<InstanceKey> possibleVals = rhs.getPossibleValues();
      Set<InstanceKey> newHeapVars = HashSetFactory.make();
      for (Iterator<Object> succs = hg.getSuccNodes(lhs.getInstanceKey()); succs.hasNext();) {
        InstanceKey succ = (InstanceKey) succs.next();
        if (!possibleVals.contains(succ)) newHeapVars.add(succ);
      }
      Util.Assert(!possibleVals.isEmpty());
      rhs = SymbolicPointerVariable.makeSymbolicVar(possibleVals);
    }
    return new PointsToEdge(lhs, rhs);

  }

  public Set<FieldReference> getFields() {
    Set<FieldReference> fields = HashSetFactory.make(); //new HashSet<FieldReference>();
    if (lhs.getFields() != null)
      fields.addAll(lhs.getFields());
    if (rhs.getFields() != null)
      fields.addAll(rhs.getFields());
    return fields;
  }
  
  
  private Set<PointerKey> getPointerKeys() {
    Set<PointerKey> keys = HashSetFactory.make(); //new HashSet<PointerKey>();
    keys.addAll(lhs.getPointerKeys());
    keys.addAll(rhs.getPointerKeys());
    return keys;
  }
  
  /**
   * @return - set of *all* pointer keys associated with constraint
   */
  public Set<PointerKey> getPointerKeys(AbstractDependencyRuleGenerator depRuleGenerator) {
    ClassHierarchy cha = depRuleGenerator.getClassHierarchy();
    HeapModel hm = depRuleGenerator.getHeapModel();
    Set<PointerKey> keysForConstraint = HashSetFactory.make();
    // add pointer keys already known to be associated with this constraint
    keysForConstraint.addAll(this.getPointerKeys());

    // resolve fields to get additional keys
    Set<SimplePathTerm> terms = this.getTerms();
    for (SimplePathTerm term : terms) {
      if (term.getObject() != null && term.getFields() != null) {
        PointerVariable pointedTo = term.getObject();
        if (pointedTo != null) {
          if (pointedTo.getInstanceKey() instanceof InstanceKey) {
            FieldReference fieldRef = term.getFirstField();
            if (fieldRef == null) continue;
            IField fld = cha.resolveField(fieldRef);
            if (fld == null) continue;
            PointerKey fieldKey = hm.getPointerKeyForInstanceField((InstanceKey) pointedTo.getInstanceKey(), fld);
            if (fieldKey == null) continue;
            keysForConstraint.add(fieldKey);
          } else if (pointedTo != null && pointedTo.getInstanceKey() instanceof LocalPointerKey) {
            LocalPointerKey lpk = (LocalPointerKey) pointedTo.getInstanceKey();
            FieldReference fieldRef = term.getFirstField();
            if (fieldRef == null) continue;
            IField fld = cha.resolveField(fieldRef);
            if (fld == null) continue;
            HeapGraph hg = depRuleGenerator.getHeapGraph();
            // TODO: use points-to constraints here when applicable
            Iterator<Object> succs = hg.getSuccNodes(lpk);
            while (succs.hasNext()) {
              Object next = succs.next();
              if (next instanceof InstanceKey) {
                PointerKey fieldKey = hm.getPointerKeyForInstanceField((InstanceKey) next, fld);
                if (fieldKey == null) continue;
                keysForConstraint.add(fieldKey);
              }
                /*
              } else if (next instanceof InstanceFieldKey) {
                InstanceFieldKey fieldKey = (InstanceFieldKey) next;
                // only add if the field matches the field of the path term
                if (fieldKey.getField().equals(fld)) keysForConstraint.add((InstanceFieldKey) next);
              } else if (next instanceof StaticFieldKey) {
                StaticFieldKey fieldKey = (StaticFieldKey) next;
                // only add if the field matches the field of the path term
                if (fieldKey.getField().equals(fld)) keysForConstraint.add((StaticFieldKey) next);
              } 
              */
            }
          }
        }
      }
    }
    return keysForConstraint;
  }

  @Override
  public String toString() {
    return lhs.toString() + " " + Util.opToString(op) + " " + rhs.toString();
  }

  @Override
  public boolean equals(Object other) {
    if (other == null) return false;
    AtomicPathConstraint pc = (AtomicPathConstraint) other;
    return pc.getLhs().equals(lhs) && pc.getOp() == op && pc.getRhs().equals(rhs);
  }

  // @Override
  public int compareTo(Object other) {
    AtomicPathConstraint pc = (AtomicPathConstraint) other;
    // Util.Debug("comparing " + this + " to " + other);
    final int lhsComparison = lhs.compareTo(pc.getLhs());
    // System.err.println("lhs's eq: " + lhsComparison);
    if (lhsComparison != 0)
      return lhsComparison;
    final int rhsComparison = rhs.compareTo(pc.getRhs());
    // System.err.println("rhs's eq: " + rhsComparison);
    if (rhsComparison != 0)
      return rhsComparison;

    // DEBUG
    // int opComparison = op.compareTo(pc.getOp());
    // System.err.println("op comparison");
    // if (DEBUG) System.err.println("ops eq: " + op.compareTo(pc.getOp()));

    return op.compareTo(pc.getOp());
  }

  private int makeHash() {
    String hashString = lhs + " " + op + " " + rhs;
    return hashString.hashCode();
  }

  @Override
  public int hashCode() {
    return hash;
  }
}

package edu.colorado.thresher.core;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.shrikeBT.BinaryOpInstruction;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.util.collections.HashSetFactory;
import com.microsoft.z3.AST;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Z3Exception;

public class PathTermWithBinOp implements PathTerm {

  private final PathTerm lhs;
  private final PathTerm rhs;
  private final BinaryOpInstruction.Operator binOp;
  private final Set<PointerVariable> vars = new TreeSet<PointerVariable>();
  private boolean substituted = false;

  public PathTermWithBinOp(PointerVariable lhs, int rhs, BinaryOpInstruction.Operator binOp) {
    this.lhs = new SimplePathTerm(lhs);
    this.rhs = new SimplePathTerm(rhs);
    this.binOp = binOp;
    vars.add(lhs);
  }

  public PathTermWithBinOp(int lhs, PointerVariable rhs, BinaryOpInstruction.Operator binOp) {
    this.lhs = new SimplePathTerm(lhs);
    this.rhs = new SimplePathTerm(rhs);
    this.binOp = binOp;
    vars.add(rhs);
  }

  public PathTermWithBinOp(PointerVariable lhs, PointerVariable rhs, BinaryOpInstruction.Operator binOp) {
    this.lhs = new SimplePathTerm(lhs);
    this.rhs = new SimplePathTerm(rhs);
    this.binOp = binOp;
    vars.add(lhs);
    vars.add(rhs);
  }

  private PathTermWithBinOp(PathTerm lhs, PathTerm rhs, BinaryOpInstruction.Operator binOp) {
    this.lhs = lhs;
    this.rhs = rhs;
    this.binOp = binOp;
    vars.addAll(lhs.getVars());
    vars.addAll(rhs.getVars());
  }

  public PathTerm heapSubstitute(SimplePathTerm toSub, SimplePathTerm subFor) {
    PathTerm newLHS = lhs.heapSubstitute(toSub, subFor);
    PathTerm newRHS = rhs.heapSubstitute(toSub, subFor);
    PathTermWithBinOp newPathTerm = new PathTermWithBinOp(newLHS, newRHS, binOp);
    newPathTerm.setSubstituted(newLHS.substituted() || newRHS.substituted());
    return newPathTerm;
  }

  @Override
  public boolean symbContains(PathTerm other) {
    // TODO: for now, just simple equality check
    if (other instanceof SimplePathTerm)
      return false;
    return this.equals(other);
  }

  // TODO: add simplification of literals
  public PathTerm substitute(PathTerm toSub, SimplePathTerm subFor) {
    // System.err.println("trying to substitute " + toSub + " for " + subFor);
    PathTerm newLHS = lhs.substitute(toSub, subFor);
    PathTerm newRHS = rhs.substitute(toSub, subFor);
    PathTermWithBinOp newPathTerm = new PathTermWithBinOp(newLHS, newRHS, binOp);
    newPathTerm.setSubstituted(newLHS.substituted() || newRHS.substituted());
    return newPathTerm;
  }

  /**
   * substitute the expression toSub for the field read subFor.subForFieldName
   * 
   * @return - a new path term if substitution occurred, the same path term
   *         otherwise
   */
  @Override
  public PathTermWithBinOp substituteExpForFieldRead(SimplePathTerm toSub, PointerVariable subFor, FieldReference fieldName) {
    PathTerm newLHS = lhs.substituteExpForFieldRead(toSub, subFor, fieldName);
    PathTerm newRHS = rhs.substituteExpForFieldRead(toSub, subFor, fieldName);
    if (newLHS.substituted() || newRHS.substituted()) {
      PathTermWithBinOp newPathTerm = new PathTermWithBinOp(newLHS, newRHS, binOp);
      newPathTerm.setSubstituted(true);
      return newPathTerm;
    }
    this.substituted = false;
    return this;
  }

  @Override
  public boolean isIntegerConstant() {
    return lhs.isIntegerConstant() && rhs.isIntegerConstant();
  }

  @Override
  public boolean substituted() {
    return substituted;
  }

  @Override
  public void setSubstituted(boolean substituted) {
    this.substituted = substituted;
  }

  @Override
  public PathTermWithBinOp deepCopy() {
    return this; // ok because PathTermWithBinOp is immutable
  }

  public String toHumanReadableString() {
    return lhs.toHumanReadableString() + " " + Util.binOpToString(binOp) + " " + rhs.toHumanReadableString();
  }

  @Override
  public List<FieldReference> getFields() {
    List<FieldReference> fields = new LinkedList<FieldReference>();
    if (lhs.getFields() != null)
      fields.addAll(lhs.getFields());
    if (rhs.getFields() != null)
      fields.addAll(rhs.getFields());
    return fields;
  }

  @Override
  public Set<PointerKey> getPointerKeys() {
    Set<PointerKey> keys = HashSetFactory.make();//new HashSet<PointerKey>();
    keys.addAll(lhs.getPointerKeys());
    keys.addAll(rhs.getPointerKeys());
    return keys;
  }

  public PathTerm getLHS() {
    return lhs;
  }

  public PathTerm getRHS() {
    return rhs;
  }

  public BinaryOpInstruction.Operator getBinOp() {
    return binOp;
  }

  @Override
  // TODO: change to account for commutativity etc
  public boolean equals(Object other) {
    PathTerm pt = (PathTerm) other;
    if (pt instanceof PathTermWithBinOp) {
      PathTermWithBinOp ptBinOp = (PathTermWithBinOp) pt;
      return lhs.equals(ptBinOp.getLHS()) && rhs.equals(ptBinOp.getRHS()) && binOp == ptBinOp.getBinOp();
    }
    return false;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((binOp == null) ? 0 : binOp.hashCode());
    result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
    result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
    return result;
  }

  @Override
  public int compareTo(Object other) {
    if (other instanceof SimplePathTerm)
      return -1;
    PathTermWithBinOp otherTerm = (PathTermWithBinOp) other;
    int lhsComparison = lhs.compareTo(otherTerm.getLHS());
    if (lhsComparison != 0)
      return lhsComparison;
    // System.err.println("lhses ok");
    int rhsComparison = rhs.compareTo(otherTerm.getRHS());
    if (rhsComparison != 0)
      return rhsComparison;
    // System.err.println("rhses ok");
    BinaryOpInstruction.Operator otherOp = otherTerm.getBinOp();
    return binOp.compareTo(otherOp);
  }

  @Override
  public int evaluate() {
    Util.Pre(isIntegerConstant(), "only call when this is a constant!");
    int lhsVal = lhs.evaluate(), rhsVal = rhs.evaluate();
    switch (this.binOp) {
      case ADD:
        return lhsVal + rhsVal;
      case SUB:
        return lhsVal - rhsVal;
      case MUL:
        return lhsVal * rhsVal;
      case DIV:
        return lhsVal / rhsVal;
      case REM:
        return lhsVal % rhsVal;
      default:
        Util.Unimp("evaluating op " + binOp);
        return -1;
    }
  }

  public AST toZ3AST(Context ctx, boolean boolVar) {
    AST binOpLHS = lhs.toZ3AST(ctx, boolVar);
    AST binOpRHS = rhs.toZ3AST(ctx, boolVar);
    try {
      switch (this.binOp) {
        case ADD:
          return ctx.MkAdd(new ArithExpr[] { (ArithExpr) binOpLHS, (ArithExpr) binOpRHS } );
          //return ctx.mkAdd(binOpLHS, binOpRHS);
        case SUB:
          return ctx.MkSub(new ArithExpr[] { (ArithExpr) binOpLHS, (ArithExpr) binOpRHS } );
          //return ctx.mkSub(binOpLHS, binOpRHS);
        case MUL:
          return ctx.MkMul(new ArithExpr[] { (ArithExpr) binOpLHS, (ArithExpr) binOpRHS } );
          //return ctx.mkMul(binOpLHS, binOpRHS);
        case DIV:
          return ctx.MkDiv((ArithExpr) binOpLHS, (ArithExpr) binOpRHS);
          //return ctx.mkDiv(binOpLHS, binOpRHS);
        case AND:
          Util.Unimp("bw and");
          // make boolean vars, not int vars
          binOpLHS = lhs.toZ3AST(ctx, true);
          binOpRHS = rhs.toZ3AST(ctx, true);
          //return ctx.mkAnd(binOpLHS, binOpRHS);
          return null;
        case OR: {
          Util.Unimp("bw or");
          // make boolean vars, not int vars
          binOpLHS = lhs.toZ3AST(ctx, true);
          binOpRHS = rhs.toZ3AST(ctx, true);
          //return ctx.mkOr(binOpLHS, binOpRHS);
          return null;
        }
        case XOR: {
          Util.Unimp("xor");
          // make boolean vars, not int vars
          binOpLHS = lhs.toZ3AST(ctx, true);
          binOpRHS = rhs.toZ3AST(ctx, true);
          //return ctx.mkXor(binOpLHS, binOpRHS);
          return null;
        }
        case REM:
          return ctx.MkRem((IntExpr) binOpLHS, (IntExpr) binOpRHS);
          //return ctx.mkRem(binOpLHS, binOpRHS);
        default:
          Util.Unimp("unsupported bin op " + binOp);
      }
    } catch (Z3Exception e) {
      Util.Assert(false, "problem with z3 " + e);
    }
    return null;
  }

  public Set<PointerVariable> getVars() {
    return vars;
  }
  
  @Override
  public int size() {
    return lhs.size() + rhs.size();
  }

  @Override
  public boolean isHeapLocation() {
    return false;
  } // this is never just a heap location because it contains a bin op

  @Override
  public Set<SimplePathTerm> getTerms() {
    Set<SimplePathTerm> set = new TreeSet<SimplePathTerm>();
    set.addAll(this.lhs.getTerms());
    set.addAll(this.rhs.getTerms());
    return set;
  }

  @Override
  public String toString() {
    return lhs + " " + binOp + " " + rhs;
  }

}

package edu.colorado.thresher.core;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.types.FieldReference;
import com.microsoft.z3.AST;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Z3Exception;

public class DisjunctivePathTerm implements PathTerm {

  final Collection<AtomicPathConstraint> disjuncts;
  
  public DisjunctivePathTerm(Collection<AtomicPathConstraint> disjuncts) {
    this.disjuncts = disjuncts;
  }
  
  public AST toZ3AST(Context ctx, boolean boolVar) {
    try {
      BoolExpr[] z3Disjuncts = new BoolExpr[this.disjuncts.size()];
      int i = 0;      
      for (AtomicPathConstraint disjunct : this.disjuncts) {
        z3Disjuncts[i++] = (BoolExpr) disjunct.toZ3AST(ctx);
      }
      return ctx.MkOr(z3Disjuncts);
    } catch (Z3Exception e) {
      Util.Assert(false, "problem with z3 " + e);
      return null;
    }
  }

  @Override
  public PathTerm deepCopy() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public String toHumanReadableString() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Set<PointerVariable> getVars() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public List<FieldReference> getFields() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Set<PointerKey> getPointerKeys() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public PathTerm substituteExpForFieldRead(SimplePathTerm toSub,
      PointerVariable subFor, FieldReference fieldName) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public PathTerm substitute(PathTerm toSub, SimplePathTerm subFor) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public PathTerm heapSubstitute(SimplePathTerm toSub, SimplePathTerm subFor) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public int evaluate() {
    // TODO Auto-generated method stub
    return 0;
  }

  @Override
  public boolean substituted() {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public boolean isIntegerConstant() {
    return false;
  }

  @Override
  public void setSubstituted(boolean substituted) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public Set<SimplePathTerm> getTerms() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public boolean symbContains(PathTerm other) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public boolean isHeapLocation() {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public int size() {
    return disjuncts.size();
  }

  @Override
  public int compareTo(Object other) {
    // TODO Auto-generated method stub
    return 0;
  }
}

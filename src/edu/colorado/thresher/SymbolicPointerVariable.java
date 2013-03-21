package edu.colorado.thresher;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;

public class SymbolicPointerVariable implements PointerVariable { 
  private static int symbCounter = 0;
  // private final String name;
  private final Set<InstanceKey> possibleValues;
  // private int instanceNum = PointerVariable.ANY_INSTANCE_NUM;
  private final int id;

  public static PointerVariable makeSymbolicVar(Set<InstanceKey> possibleValues) {
    // can't make symbolic var from the empty set
    Util.Pre(!possibleValues.isEmpty());
    if (possibleValues.size() == 1) return Util.makePointerVariable(possibleValues.iterator().next());
    return new SymbolicPointerVariable(possibleValues);
  }

  private SymbolicPointerVariable(Set<InstanceKey> possibleValues) {
    // this.name = makeNewSymbolicVariable();
    this.id = symbCounter++;
    Util.Assert(possibleValues.size() > 1, "possible values is size 1; should make concrete var instead");
    this.possibleValues = possibleValues;
    if (Options.DEBUG) {
      Util.Debug("Possible values for " + id + "symb:");
      Util.Debug(Util.printCollection(possibleValues));
    }
  }

  public CGNode getNode() {
    return null;
  }

  public InstanceKey getInstanceKey() {
    return null;
  }

  public PointerVariable deepCopy() {
    // all fields are immutable; no need to copy
    return this;
  }

  public String toString() {
    if (possibleValues.size() == 1)
      return "symb: " + possibleValues.iterator().next().toString();
    return id + "symb"; // name;
    // return parseToHumanReadable(name) + "<" + id + "-T" + typeId + ">";
    // return name + "<" + id + "-T" + typeId + ">";
  }

  /*
   * public String toFormattedPointsToConstraint() { return name; }
   */

  @Override
  public Set<InstanceKey> getPossibleValues() {
    return possibleValues;
  }
  
  /**
   * @return - list of PointerKey's corresponding to fld for each possibleValue
   */
  public Collection<PointerKey> getPossibleFields(IField fld, HeapModel hm) {
    Collection<PointerKey> possibleFields = new ArrayList<PointerKey>(possibleValues.size());
    
    if (fld == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) {
      for (InstanceKey key : possibleValues) {
        possibleFields.add(hm.getPointerKeyForArrayContents(key));  
      }
    } else {
      for (InstanceKey key : possibleValues) {
        possibleFields.add(hm.getPointerKeyForInstanceField(key, fld));  
      }
    }    
    return possibleFields;
  }

  public String getName() {
    return id + "symb";// name;
  }

  public boolean isSymbolic() {
    return true;
  }

  public String makeNewSymbolicVariable() {
    return (symbCounter++) + "symb";
  }

  public int getSymbCounter() {
    return symbCounter;
  }

  public int getCallId() {
    return -2;
  }

  public boolean isLocalVar() {
    return false;
  }

  public boolean isHeapVar() {
    Util.Assert(false, "untested");
    return true;
  }

  public String parseToHumanReadable(String str) {
    // System.err.println("INPUT:" + str);
    if (str.contains("symb") || !str.contains("-") || str.equals("-1"))
      return str;
    // || str.contains("<init>") || str.contains("<clinit>")) return str;

    String split0[] = str.split(",");
    // System.err.println(split0[0]);
    // System.err.println(split0[1]);
    // System.err.println(split0[2]);
    String split1[] = split0[2].split("[(]");
    String fun_name = split1[0];
    String split2[] = split1[1].split(">-");
    String varNum = split2[1];
    // System.err.println(fun_name);
    // System.err.println(varNum);
    String toReturn = fun_name + "-" + varNum;
    // System.err.println("RETURN " + toReturn);
    return toReturn;
  }

  
  // TODO: these names (symbEq and symbContains) are dumb...they mean the opposite of what one would think
  
  @Override
  public boolean symbEq(PointerVariable other) {
    if (other instanceof SymbolicPointerVariable) {
      SymbolicPointerVariable symb = (SymbolicPointerVariable) other;
      return Util.intersectionNonEmpty(possibleValues, symb.getPossibleValues());
    } else if (other instanceof ConcretePointerVariable) {
      return this.possibleValues.contains(other.getInstanceKey());
    }
    return false;
  }

  /**
   * this symbContains other if it represents more possible values than other
   */
  @Override
  public boolean symbContains(PointerVariable other) {
    if (other instanceof SymbolicPointerVariable) {
      SymbolicPointerVariable symb = (SymbolicPointerVariable) other;
      return this.getPossibleValues().containsAll(symb.getPossibleValues());
    } else if (other instanceof ConcretePointerVariable) {
      return this.possibleValues.contains(other.getInstanceKey());
    }
    return false;
  }

  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SymbolicPointerVariable))
      return false;
    SymbolicPointerVariable p = (SymbolicPointerVariable) other;
    Set<InstanceKey> otherPossibleValues = p.possibleValues;
    if (this.possibleValues.size() != otherPossibleValues.size())
      return false;
    for (InstanceKey key : this.possibleValues) {
      if (!otherPossibleValues.contains(key))
        return false;
    }
    return true;
  }

  @Override
  public int hashCode() {
    return id;// name.hashCode();
  }

  @Override
  public int compareTo(Object other) {
    if (other instanceof ConcretePointerVariable)
      return -1;
    else if (other instanceof SymbolicPointerVariable) {
      SymbolicPointerVariable var = (SymbolicPointerVariable) other;
      /*
       * if (this.possibleValues.size() > var.possibleValues.size()) return 1;
       * else if (possibleValues.size() < var.possibleValues.size()) return -1;
       */
      // TODO: fix
      return this.id - var.id;
    } else {
      Util.Assert(false, "comparing to non-ptr var " + other);
      return 1;
    }
  }

}

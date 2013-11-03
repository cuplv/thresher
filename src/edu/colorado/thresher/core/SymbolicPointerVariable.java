package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.intset.OrdinalSet;

public class SymbolicPointerVariable implements PointerVariable { 
  private static int symbCounter = 0;
  // private final String name;
  private final Set<InstanceKey> possibleValues;
  // private int instanceNum = PointerVariable.ANY_INSTANCE_NUM;
  private final int id;

  public static PointerVariable makeSymbolicVar(OrdinalSet<InstanceKey> possibleValues) {
    Set<InstanceKey> possibleVals = HashSetFactory.make();
    for (Iterator<InstanceKey> iter = possibleValues.iterator(); iter.hasNext();) {
      possibleVals.add(iter.next());
    }
    return makeSymbolicVar(possibleVals);
  }
  
  public static PointerVariable makeSymbolicVar(Set<InstanceKey> possibleValues) {
    // can't make symbolic var from the empty set
    Util.Pre(!possibleValues.isEmpty());
    if (possibleValues.size() == 1) return Util.makePointerVariable(possibleValues.iterator().next());
    return new SymbolicPointerVariable(possibleValues);
  }
  
  /**
   * make a symbolic variable from the points-to set of @param key in @param hg
   */
  public static PointerVariable makeSymbolicVar(Object key, HeapGraph hg) {
    Set<InstanceKey> possibleValues = HashSetFactory.make();
    for (Iterator<Object> succs = hg.getSuccNodes(key); succs.hasNext();) {
      possibleValues.add((InstanceKey) succs.next());
    }
    if (possibleValues.isEmpty()) return null;
    return makeSymbolicVar(possibleValues);
  }

  /**
   * make a symbolic variable from the points-to set of @param key in @param hg, but only include allocation sites of type @param typ
   */
  public static PointerVariable makeSymbolicVar(Object key, TypeReference typ, IClassHierarchy cha, HeapGraph hg) {
    Set<InstanceKey> possibleValues = HashSetFactory.make();
    IClass desiredTyp = cha.lookupClass(typ);   
    for (Iterator<Object> succs = hg.getSuccNodes(key); succs.hasNext();) {
      InstanceKey ik = (InstanceKey) succs.next();
      // filter pts-to set by desiredTyp
      if (desiredTyp == null || cha.isSubclassOf(ik.getConcreteType(), desiredTyp)) {
        possibleValues.add(ik);
      }
    }
    if (possibleValues.isEmpty()) return null;
    return makeSymbolicVar(possibleValues);
  }
  
  /**
   * @return PointerVariabe representing intersection of possible value sets if nonempty, null otherwise
   */
  public static PointerVariable mergeVars(PointerVariable var0, PointerVariable var1) {
    // can't make symbolic var from the empty set
    Set<InstanceKey> newVals = Util.deepCopySet(var0.getPossibleValues());
    newVals.retainAll(var1.getPossibleValues());
    if (newVals.size() == 0) return null;
    if (Options.DEBUG) Util.Debug("merged " + var0 + " and " + var1 + " into " + (symbCounter + 1) + "symb");
    return makeSymbolicVar(newVals);
  }

  public SymbolicPointerVariable(Set<InstanceKey> possibleValues) {
    this.id = symbCounter++;
    Util.Assert(possibleValues.size() > 1, "possible values is size 1; should make concrete var instead");
    this.possibleValues = possibleValues;
    
    //if (Options.DEBUG) {
      //Util.Print("Possible values for " + id + "symb:");
      //Util.Print(Util.printCollection(possibleValues));
    //}
    
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
    //if (possibleValues.size() == 1)
     // return "symb: " + possibleValues.iterator().next().toString();
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
  
  /**
   * @return instance keys that may point through field fld to this symbolic variable 
   */
  @Override
  public Set<InstanceKey> getPointsAtSet(HeapGraph hg, IField fld) {
    Util.Pre(!fld.isStatic());
    Set<InstanceKey> pointsAtSet = HashSetFactory.make();
    boolean arrayFld = fld.equals(AbstractDependencyRuleGenerator.ARRAY_CONTENTS);
    for (InstanceKey key : possibleValues) {
      for (Iterator<Object> fldIter = hg.getPredNodes(key); fldIter.hasNext();) {
        Object fldKey = fldIter.next();
        boolean match = false;
        if (arrayFld) match = fldKey instanceof ArrayContentsKey;
        else if (fldKey instanceof InstanceFieldKey) {
          // instance field
          InstanceFieldKey ifk = (InstanceFieldKey) fldKey;
          match = ifk.getField().equals(fld);
        }
        if (match) {
          for (Iterator<Object> keyIter = hg.getPredNodes(fldKey); keyIter.hasNext();) {
            pointsAtSet.add((InstanceKey) keyIter.next());
          }
        }
      }
    }
    // this shouldn't be empty... indicates bad usage or problem with pts-to analysis
    Util.Post(!pointsAtSet.isEmpty()); 
    return pointsAtSet;
  }
  
  /**
   * @return instance keys that this symbolic variable may point to through field fld 
   */
  @Override
  public Set<InstanceKey> getPointsToSet(HeapGraph hg, IField fld) {
    return ConcretePointerVariable.getPointsToSet(possibleValues, fld, hg);

    /*
    Util.Pre(!fld.isStatic());
    Set<InstanceKey> pointsToSet = HashSetFactory.make();
    boolean arrayFld = fld.equals(AbstractDependencyRuleGenerator.ARRAY_CONTENTS);
    for (InstanceKey key : possibleValues) {
      for (Iterator<Object> fldIter = hg.getSuccNodes(key); fldIter.hasNext();) {
        Object fldKey = fldIter.next();
        boolean match = false;
        if (arrayFld) match = fldKey instanceof ArrayContentsKey;
        else {
          // instance field
          InstanceFieldKey ifk = (InstanceFieldKey) fldKey;
          match = ifk.getField().equals(fld);
        }
        if (match) {
          for (Iterator<Object> keyIter = hg.getSuccNodes(fldKey); keyIter.hasNext();) {
            pointsToSet.add((InstanceKey) keyIter.next());
          }
        }
      }
    }
    // this shouldn't be empty... indicates bad usage or problem with pts-to analysis
    Util.Post(!pointsToSet.isEmpty()); 
    return pointsToSet;*/
  }

  @Override
  public Set<InstanceKey> getPointsToSet(HeapGraph hg) {
    Util.Unimp("should never call this on symbolic var!");
    return null;
  }

  
  @Override
  public boolean isParameter() {
    return false;
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
    
    if (!Options.NARROW_FROM_CONSTRAINTS) {
      return false; // can't compare for equality
    }
    
    if (other instanceof SymbolicPointerVariable) {
      SymbolicPointerVariable symb = (SymbolicPointerVariable) other;
      boolean containsAll = this.getPossibleValues().containsAll(symb.getPossibleValues());
      Util.Print("checking if " + this + " symbContains " + other + " " + containsAll);

      return containsAll;
      //return this.getPossibleValues().containsAll(symb.getPossibleValues());
    } else if (other instanceof ConcretePointerVariable) {
      return this.possibleValues.contains(other.getInstanceKey());
    }
    return false;
  }

  @Override
  public boolean isClinitVar() {
    // TODO: just assuming that it's not; we'd need the callgraph to determine otherwise
    return false;
  }


  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SymbolicPointerVariable)) return false;
    SymbolicPointerVariable p = (SymbolicPointerVariable) other;
    Set<InstanceKey> otherPossibleValues = p.possibleValues;
    
    if (!Options.NARROW_FROM_CONSTRAINTS) {
      return Util.intersectionNonEmpty(this.possibleValues, otherPossibleValues);
    }
    
    if (this.possibleValues.size() != otherPossibleValues.size()) return false;
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

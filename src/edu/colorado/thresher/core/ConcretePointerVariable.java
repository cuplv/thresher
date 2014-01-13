package edu.colorado.thresher.core;

import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.propagation.AllocationSite;
import com.ibm.wala.ipa.callgraph.propagation.AllocationSiteInNode;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.ConcreteTypeKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.MultiNewArrayInNode;
import com.ibm.wala.ipa.callgraph.propagation.NormalAllocationInNode;
import com.ibm.wala.ipa.callgraph.propagation.ReturnValueKey;
import com.ibm.wala.ipa.callgraph.propagation.SmushedAllocationSiteInNode;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.util.collections.HashSetFactory;

public class ConcretePointerVariable implements PointerVariable { // implements
                                                                  // Comparable
                                                                  // {

  public final static ConcretePointerVariable NEVER_EQ = new ConcretePointerVariable();

  private final String name;
  //private final int id;
  // private final int typeId;

  private final CGNode node;
  private final IMethod method;
  private final Object instanceKey;
  private final int useNum;

  // special tag corresponding to instance number of constraint. introduced only
  // when needed
  // private final int instanceNum;

  private ConcretePointerVariable() {
    this.name = null;
    //this.id = -1;
    // this.typeId = -1;
    this.node = null;
    this.useNum = -5;
    this.instanceKey = null;
    // this.instanceNum = PointerVariable.ANY_INSTANCE_NUM;
    this.method = null;
  }

  // public ConcretePointerVariable(CGNode node, int useNum,
  // AbstractDependencyRuleGenerator gen, int nodeNum) {
  public ConcretePointerVariable(CGNode node, int useNum, HeapModel hm) {
    this.node = node;
    this.useNum = useNum;
    this.name = Util.makeLocalVarName(node, useNum);

    // this.typeId = Util.getIdForType(name);
    // if (useNum != -1) Util.Assert(name.indexOf('@') == -1, "weird var name "
    // + name + " " + useNum);
    // this.instanceKey = gen.getHeapModel().getPointerKeyForLocal(node,
    // useNum);
    this.instanceKey = hm.getPointerKeyForLocal(node, useNum);

    // this.id = gen.getHeapGraph().getNumber(instanceKey);

    // Util.Assert(instanceKey != null, "couldn't find pointerkey for " + node +
    // " -v " + useNum);
    //this.id = instanceKey.toString().hashCode();// Util.getIdForVar(name);
    // Util.Assert(((LocalPointerKey) instanceKey).getNode().equals(node),
    // "nodes don't match!");

    // this.instanceNum = PointerVariable.ANY_INSTANCE_NUM;
    this.method = null;
  }  

  public ConcretePointerVariable(Object key, CGNode node) {
    this.node = node;
    this.useNum = -1;
    this.name = null;
    this.instanceKey = key;
    //this.id = instanceKey.toString().hashCode();
    this.method = null;
  }

  public ConcretePointerVariable(Object key, CGNode node, int useNum) {
    this.node = node;
    this.useNum = useNum;
    this.name = null;
    // if (name.contains("synthetic")) {
    // name = name.replace("synthetic ", "");
    // }
    // this.name = name;
    // this.id = Util.getIdForVar(name);
    // this.typeId = typeId;
    // Util.Assert(!name.contains("synthetic"), "evil synthetic var name " +
    // name);
    // if (useNum != -1) Util.Assert(name.indexOf('@') == -1, "weird var name "
    // + name + " " + useNum);
    this.instanceKey = key;
    //this.id = instanceKey.toString().hashCode();
    // this.instanceNum = PointerVariable.ANY_INSTANCE_NUM;
    this.method = null;
  }

  public ConcretePointerVariable(Object walaKey, CGNode node, String name) {
    this.node = node;
    this.useNum = -1;
    this.name = name;
    // this.id = Util.getIdForVar(name);
    // this.typeId = typeId;
    this.instanceKey = walaKey;
    //this.id = instanceKey.toString().hashCode();
    // this.instanceNum = PointerVariable.ANY_INSTANCE_NUM;
    this.method = null;
  }

  // for static fields / allocation sites with no context
  public ConcretePointerVariable(Object walaKey, IMethod method, String name) {
    this.node = null;
    this.useNum = -1;
    this.name = name;
    // this.id = Util.getIdForVar(name);
    // this.typeId = typeId;
    this.instanceKey = walaKey;
    //this.id = instanceKey.toString().hashCode();
    // this.instanceNum = -1;
    this.method = method;
  }

  // for types
  public ConcretePointerVariable(Object walaKey, String name) {
    this.node = null;
    this.useNum = -1;
    this.name = name;
    // this.id = Util.getIdForVar(name);
    // this.typeId = typeId;
    this.instanceKey = walaKey;
    //this.id = instanceKey.toString().hashCode();
    // this.instanceNum = -1;
    this.method = null;
  }

  // for constants
  public ConcretePointerVariable(String name) {
    this.node = null;
    this.useNum = -1;
    this.name = name;
    // this.id = Util.getIdForVar(name);
    // this.typeId = typeId;
    //this.instanceKey = null;
    this.instanceKey = name;
    //this.id = name.hashCode();
    // this.instanceNum = -1;
    this.method = null;
  }
  
  public static PointerVariable make(Object key) {
    return Util.makePointerVariable(key);
  }

  public Object getInstanceKey() {
    return instanceKey;
  }

  public PointerVariable deepCopy() {
    // all the fields are immutable or primitive, so there's no need to make a
    // copy
    return this;
  }

  /*
   * public int getInstanceNum() { return instanceNum; }
   */

  @Override
  public Set<InstanceKey> getPossibleValues() {
    if (this.instanceKey instanceof InstanceKey) {
      return Collections.singleton((InstanceKey) this.instanceKey);
    } 
    //Util.Print("asked for possible values of " + this.instanceKey + " returning null.");
    return null;
  }
  
  /**
   * @return instance keys that may point through field @param fld to this symbolic variable 
   */
  @Override
  public Set<InstanceKey> getPointsAtSet(HeapGraph hg, IField fld) {
    Set<InstanceKey> pointsAtSet = HashSetFactory.make();
    Util.Pre(!fld.isStatic(), "what to do here?");
    boolean arrayFld = fld.equals(AbstractDependencyRuleGenerator.ARRAY_CONTENTS);
    for (Iterator<Object> fldIter = hg.getPredNodes(this.instanceKey); fldIter.hasNext();) {
      Object fldKey = fldIter.next();
      boolean match = false;
      if (arrayFld) match = fldKey instanceof ArrayContentsKey;
      else {
        if (fldKey instanceof InstanceFieldKey) {
          InstanceFieldKey ifk = (InstanceFieldKey) fldKey;
          match = ifk.getField().equals(fld);
        }
      }
      if (match) {
        for (Iterator<Object> keyIter = hg.getPredNodes(fldKey); keyIter.hasNext();) {
          pointsAtSet.add((InstanceKey) keyIter.next());
        }
      }
    }
    // this shouldn't be empty... indicates bad usage or problem with pts-to analysis
    Util.Post(!pointsAtSet.isEmpty(), "empty points-at set for " + fld); 
    return pointsAtSet;
  }

  /**
   * @return instance keys that may point through field @param fld to this symbolic variable 
   */
  @Override
  public Set<InstanceKey> getPointsToSet(HeapGraph hg, IField fld) {
    /*
    Set<InstanceKey> pointsToSet = HashSetFactory.make();
    boolean arrayFld = fld.equals(AbstractDependencyRuleGenerator.ARRAY_CONTENTS);
    boolean staticFld = fld.isStatic();
    for (Iterator<Object> fldIter = hg.getSuccNodes(this.instanceKey); fldIter.hasNext();) {
      Object fldKey = fldIter.next();
      boolean match = false;
      if (arrayFld) match = fldKey instanceof ArrayContentsKey;
      else if (staticFld) pointsToSet.add((InstanceKey) fldKey);
      else { //if (!(fldKey instanceof ConcreteTypeKey)) {
        // instance field key
        InstanceFieldKey ifk = (InstanceFieldKey) fldKey;
        match = ifk.getField().equals(fld);
      }
      if (!staticFld && match) {
        for (Iterator<Object> keyIter = hg.getSuccNodes(fldKey); keyIter.hasNext();) {
          pointsToSet.add((InstanceKey) keyIter.next());
        }
      }
    }
    // this shouldn't be empty... indicates bad usage or problem with pts-to analysis
    Util.Post(!pointsToSet.isEmpty()); 
    return pointsToSet;
    */
    // if the var is a local var, we should get the points-to set of the local, *then* get
    // the points-to set of the field    
    Util.Pre(!this.isLocalVar());
    return getPointsToSet(Collections.singleton(this.instanceKey), fld, hg);
  }
  
  public static Set<InstanceKey> getPointsToSet(Set keys, IField fld, HeapGraph hg) {
    Util.Pre(fld != null);
    Set<InstanceKey> pointsToSet = HashSetFactory.make();
    boolean arrayFld = fld.equals(AbstractDependencyRuleGenerator.ARRAY_CONTENTS);
    boolean staticFld = fld.isStatic();
    
    for (Object key : keys) {
      for (Iterator<Object> fldIter = hg.getSuccNodes(key); fldIter.hasNext();) {
        Object fldKey = fldIter.next();

        boolean match = false;
        if (arrayFld) match = fldKey instanceof ArrayContentsKey;
        else if (staticFld) pointsToSet.add((InstanceKey) fldKey);
        else {
          // instance field
          InstanceFieldKey ifk = (InstanceFieldKey) fldKey;
          match = ifk.getField().getReference().equals(fld.getReference());
        }
        if (!staticFld && match) {
          for (Iterator<Object> keyIter = hg.getSuccNodes(fldKey); keyIter.hasNext();) {
            pointsToSet.add((InstanceKey) keyIter.next());
          }
        }
      }
    }
    // this shouldn't be empty... indicates bad usage or problem with pts-to analysis
    if (pointsToSet.isEmpty()) Util.Assert(false," bad usage -- pts to set for " + Util.printCollection(keys) + "." + fld + " empty");
    return pointsToSet;
  }
  
  /**
   * 
   * @param hg
   * @return - the set of instance keys that this local var may point to
   */
  @Override
  public Set<InstanceKey> getPointsToSet(HeapGraph hg) {
    Util.Pre(this.isLocalVar());
    Set<InstanceKey> keys = HashSetFactory.make();
    for (Iterator<Object> succs = hg.getSuccNodes(this.instanceKey); succs.hasNext();) {
      keys.add((InstanceKey) succs.next());
    }    
    //Util.Print("Points-to set of " + this + ": " + Util.printCollection(keys));
    
    return keys;
  }
  
  public Set<InstanceKey> getFilteredPointsToSet(PointerVariable filterBy, HeapGraph hg) {
    Util.Pre(this.isLocalVar());
    Set<InstanceKey> filterSet = filterBy.getPossibleValues();
    Set<InstanceKey> keys = HashSetFactory.make();
    for (Iterator<Object> succs = hg.getSuccNodes(this.instanceKey); succs.hasNext();) {
      InstanceKey succ = (InstanceKey) succs.next();
      if (filterSet.contains(succ)) keys.add(succ);
    }    
    //Util.Print("Points-to set of " + this + ": " + Util.printCollection(keys));
    
    return keys;
  }
  
  @Override
  public boolean isParameter() {
    if (!isLocalVar()) return false;
    if (this.instanceKey instanceof LocalPointerKey) {
      return ((LocalPointerKey) this.instanceKey).isParameter();
    }
    return false;
  }
  
  public String toString() {
    // note than changing between forms doesn't affect the correctness of the
    // program; only the readability of the error reports!
    // human-readable form; may make vars from different methods appear to be
    // the same var
    // return parseToHumanReadable(name) + "<" + id + "-T" + typeId + ">";
    // long form of variable - includes full function name
    // return name + "<" + id + "-T" + typeId + ">";

    return toHumanReadableString();
     //if (instanceKey != null) return instanceKey.toString();
     //return name;
    // else return parseToHumanReadable(name) + "<" + id + "-T" + typeId + ">";
  }

  public String toHumanReadableString() {
    if (instanceKey instanceof LocalPointerKey) {
      LocalPointerKey lpk = (LocalPointerKey) instanceKey;
      return lpk.getNode().getMethod().getName().toString() + "-v" + lpk.getValueNumber();// +
                                                                                          // " R: "
                                                                                          // +
                                                                                          // lpk.getNode().getContext().get(ContextKey.RECEIVER);
    } else if (instanceKey instanceof AllocationSiteInNode) {
      AllocationSiteInNode alloc = (AllocationSiteInNode) instanceKey;
      // return node.getMethod().getName() + "-" + alloc.getSite().toString() +
      // " R: " + alloc.getNode().getContext().get(ContextKey.RECEIVER);
      return node.getMethod().getName() + "-" + alloc.getSite().toString();// +
                                                                           // " R: "
                                                                           // +
                                                                           // alloc.getNode().getContext().get(ContextKey.RECEIVER);
    } else if (instanceKey instanceof StaticFieldKey) {
      StaticFieldKey sfk = (StaticFieldKey) instanceKey;
      return sfk.getField().toString();
    }
    if (instanceKey != null)
      return instanceKey.toString();
    return name;
  }

  @Override
  public boolean symbEq(PointerVariable other) {
    if (other instanceof SymbolicPointerVariable) {
      SymbolicPointerVariable symb = (SymbolicPointerVariable) other;
      return symb.getPossibleValues().contains(this.instanceKey);
    } else if (other instanceof ConcretePointerVariable) {
      return this.equals(other);
    }
    return false;
  }

  /**
   * does this represent more possible values than other?
   */
  @Override
  public boolean symbContains(PointerVariable other) {
    if (other instanceof SymbolicPointerVariable) {
      SymbolicPointerVariable symb = (SymbolicPointerVariable) other;
      // symbolic pointer variables always represent at least two values; can't possibly contain
      return false;
      //return symb.getPossibleValues().size() == 1 && symb.getPossibleValues().contains(this.instanceKey);
    } else if (other instanceof ConcretePointerVariable) {
      return this.equals(other);
    }
    return false;
  }

  @Override
  public int compareTo(Object other) {
    if (other instanceof SymbolicPointerVariable)
      return 1;
    else if (other instanceof ConcretePointerVariable) {
      ConcretePointerVariable p = (ConcretePointerVariable) other;      
      //return this.id - p.id;
      return this.instanceKey.toString().compareTo(p.instanceKey.toString());
    } else {
      Util.Unimp("comparing to non-pointer " + other);
      return 1;
    }
  }

  @Override
  public boolean equals(Object other) {
    if (other instanceof ConcretePointerVariable) {
      ConcretePointerVariable p = (ConcretePointerVariable) other;
      //return this.id == p.id;
      return this.instanceKey.equals(p.instanceKey);
      /*
       * // return this.id == p.id; if (instanceKey != null && p.instanceKey !=
       * null) { //return
       * instanceKey.toString().equals(p.instanceKey.toString()); return this.id
       * == p.id; } else if (this.method != null && p.method != null) {
       * Util.Assert(false, "bad pointer vars " + other + " " + this); return
       * this.method.toString().equals(p.method.toString()); //return
       * this.method.hashCode() == p.method.hashCode(); } //return
       * this.toString().equals(p.toString());
       */
    }
    return false;
  }

  public int getUseNum() {
    return useNum;
  }

  public IMethod getMethod() {
    return method;
  }

  public CGNode getNode() {
    return node;
  }

  public boolean IsInitializerOrClassInititializer() {
    return node.getMethod().isInit() || node.getMethod().getName().toString().contains("<clinit>");
  }

  public boolean isLocalVar() {
    // return useNum != -1;
    return instanceKey != null && (instanceKey instanceof LocalPointerKey || 
                                   instanceKey instanceof ReturnValueKey);
  }
  
  @Override
  public boolean isClinitVar() {
    return this.node != null && this.node.getMethod().isClinit();
  }

  public boolean isHeapVar() {
    return instanceKey != null
        && (instanceKey instanceof AllocationSiteInNode ||
            instanceKey instanceof ArrayContentsKey ||
            instanceKey instanceof StaticFieldKey ||
            instanceKey instanceof ConcreteTypeKey||
            instanceKey instanceof AllocationSite || 
            instanceKey instanceof MultiNewArrayInNode ||
            instanceKey instanceof NormalAllocationInNode ||
            instanceKey instanceof SmushedAllocationSiteInNode); 
  }

  @Override
  public int hashCode() {
    // String hashString = this.method.toString() + " " + this.name + " " +
    // this.instanceNum;
    // return hashString.hashCode();
    // return name.hashCode();
    if (instanceKey != null)
      return instanceKey.hashCode(); // return
                                     // instanceKey.toString().hashCode();
    return name.hashCode();
  }

  // public String getName() { return name; }
  /*
   * public int getId() { return id; }
   */

  public boolean isSymbolic() {
    return false;
  }

  // public int getTypeId() { return typeId; }

  /*
   * // ugly, nasty, terrible method to print shorter form of pointer variable
   * public String parseToHumanReadable(String str) {
   * //System.err.println("INPUT:" + str); if (str == null ||
   * str.contains("symb") || !str.contains("-") || str.equals("-1")) return str;
   * //|| str.contains("<init>") || str.contains("<clinit>")) return str;
   * 
   * String split0[] = str.split(","); //System.err.println(split0[0]);
   * //System.err.println(split0[1]); //System.err.println(split0[2]); String
   * split1[] = split0[2].split("[(]"); String fun_name = split1[0]; String
   * split2[] = split1[1].split(">-"); String varNum = split2[1];
   * //System.err.println(fun_name); //System.err.println(varNum); String
   * toReturn = fun_name + "-" + varNum; //System.err.println("RETURN " +
   * toReturn); return toReturn; }
   */

}

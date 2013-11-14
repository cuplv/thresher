package edu.colorado.thresher.core;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.types.annotations.Annotation;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.strings.Atom;
import com.microsoft.z3.AST;
import com.microsoft.z3.Context;
import com.microsoft.z3.Z3Exception;

// a path variable is one of three things: a constant, an object, or an object and an access path
public class SimplePathTerm implements PathTerm {

  public static final SimplePathTerm NULL = new SimplePathTerm(0);
  public static final SimplePathTerm NON_NULL = new SimplePathTerm(1);

  public static boolean DEBUG = Options.DEBUG;
  public static final FieldReference LENGTH = FieldReference
      .findOrCreate(ClassLoaderReference.Primordial, "array", "length", "Int");
  
  private final int constant;
  // either a local pointer to an object or a heap location
  private final PointerVariable object; 
                                    
  private final PointerKey pointer; 
                                    
  // list of field references from (derefs closer to base obj occur earlier)
  private final LinkedList<FieldReference> fields;
  private final Set<PointerVariable> vars = new TreeSet<PointerVariable>();
  private boolean substituted = false;

  private final String repr;

  public static SimplePathTerm FALSE = new SimplePathTerm();

  private SimplePathTerm() {
    this.constant = -1;
    this.object = null;
    this.pointer = null;
    this.fields = null;
    this.repr = "";
  }

  public SimplePathTerm(PointerVariable object) { // local pointer or heap var
    Util.Pre(object != null, "obj should not be null!");
    this.object = object;
    // Util.Assert(object.getInstanceKey() instanceof PointerKey, "found weird "
    // + object);
    if (object.getInstanceKey() instanceof PointerKey)
      this.pointer = (PointerKey) object.getInstanceKey();
    else
      this.pointer = null;
    this.fields = null;
    vars.add(object);
    this.constant = -1;
    this.repr = this.toString();
  }

  // constant
  public SimplePathTerm(int constant) { 
    this.object = null;
    this.pointer = null;
    this.fields = null;
    this.constant = constant;
    this.repr = this.toString();
  }

  // field read with single level of dereference
  public SimplePathTerm(PointerVariable object, FieldReference field) { 
    Util.Pre(field != null, "field should never be null here!");
    Util.Pre(object != null, "obj should not be null here");
    this.object = object;
    // Util.Assert(object.getInstanceKey() instanceof PointerKey, "found weird "
    // + object);
    if (object.getInstanceKey() instanceof PointerKey) {
      this.pointer = (PointerKey) object.getInstanceKey();
    } else
      this.pointer = null;
    this.fields = new LinkedList<FieldReference>();
    fields.add(field);
    vars.add(object);
    this.constant = -1;
    this.repr = this.toString();
  }

  SimplePathTerm(PointerVariable object, LinkedList<FieldReference> fields) {
    Util.Pre(fields == null || object != null, "obj should not be null when fields is non-null!");
    this.object = object;
    // Util.Assert(object.getInstanceKey() instanceof PointerKey, "found weird "
    // + object);
    if (object.getInstanceKey() instanceof PointerKey)
      this.pointer = (PointerKey) object.getInstanceKey();
    else
      this.pointer = null;
    this.fields = fields;
    Util.Assert(fields == null || !this.fields.isEmpty(), "should never have empty fields list!");
    vars.add(object);
    this.constant = -1;
    this.repr = this.toString();
  }

  public PathTerm heapSubstitute(SimplePathTerm toSub, SimplePathTerm subFor) {
    // Util.Debug("heap substitute! " + toSub + " for " + subFor +
    // ". heap loc is " + subFor.getObject());

    if (!this.isIntegerConstant() && object.equals(subFor.getObject())) { //
      SimplePathTerm newTerm;
      if (toSub.getFields() == null) { // no fields; subbing in variable y
        if (subFor.getFields() == null) {
          // subbing y for x
          LinkedList<FieldReference> newFields = null;
          if (this.fields != null)
            newFields = Util.deepCopyStackList(this.fields);
          newTerm = new SimplePathTerm(toSub.getObject().deepCopy(), newFields);
        } else {
          // subbing y for x.f
          if (this.fields == null) {
            // can't be this PathTerm; it has no fields
            this.setSubstituted(false);
            return this;
          } else {
            FieldReference toRemove = subFor.getFieldsAsLinkedList().get(0);
            if (toRemove.equals(this.fields.getFirst())) {
              LinkedList<FieldReference> newFields = Util.deepCopyStackList(this.fields);
              newFields.removeFirst();
              newTerm = new SimplePathTerm(toSub.getObject().deepCopy(), newFields);
            } else { // fields don't match
              this.setSubstituted(false);
              return this;
            }
          }
        }
      } else { // toSub has fields subbing in y.f
        if (subFor.getFields() == null) {
          // subbing y.f for x
          if (this.fields == null) {
            newTerm = new SimplePathTerm(toSub.getObject().deepCopy(), Util.deepCopyStackList(toSub.getFieldsAsLinkedList()));
          } else {
            // see if we already have f in our fields
            FieldReference toAdd = toSub.getFieldsAsLinkedList().get(0);
            //if (toAdd.getName().equals(this.fields.getFirst().getName())) {
            if (toAdd.equals(this.fields.getFirst())) {
              // already have the field, don't add it again
              LinkedList<FieldReference> newFields = Util.deepCopyStackList(this.fields);
              newTerm = new SimplePathTerm(toSub.getObject().deepCopy(), newFields);
            } else { // don't have this field; add it whole
              LinkedList<FieldReference> newFields = null;
              if (this.fields != null)
                newFields = Util.deepCopyStackList(this.fields);
              newFields.addFirst(toSub.getFields().get(0));
              newTerm = new SimplePathTerm(toSub.getObject().deepCopy(), newFields);
            }
          }
        } else {
          // subbing y.f for x.f; this shouldn't be possible in a single
          // instruction at the bytecode level
          Util.Unimp("this should be impossible");
          newTerm = null;
        }
      }
      newTerm.setSubstituted(true);
      return newTerm;
    }
    this.setSubstituted(false);
    return this;
  }

  /**
   * substitute the expression toSub for the field read subFor.subForFieldName
   * 
   * @return - a new path term if substitution occurred, the same path term
   *         otherwise
   */
  @Override
  public PathTerm substituteExpForFieldRead(SimplePathTerm toSub, PointerVariable subFor, FieldReference subForFieldName) {
    // Util.Debug("TOSUB: " + toSub + "; SUBFOR: " + subFor + "; FIELD " +
    // subForFieldName + "; THIS: " + this);
    if (this.isIntegerConstant()) { // if this path term is a constant, it can't
                                    // be a field read!
      this.setSubstituted(false); // this.substituted = false;
      return this;
    } else if (this.object.equals(subFor) && this.fields != null && this.fields.getFirst().equals(subForFieldName)) {
      //Util.Debug("substitution successful! subbing in " + toSub);
      // we found the field read we are looking for. make the substitution
      LinkedList<FieldReference> newFields = null;
      SimplePathTerm newTerm;

      if (fields.size() > 1) { // more than one field; need to rebuild field
                               // list
        if (toSub.getObject() == null)
          return SimplePathTerm.FALSE; // we're subbing null for a obj whose
                                       // field we are dereferencing... refute
        newFields = Util.deepCopyStackList(fields);
        newFields.removeFirst(); // remove field that we are subbing for
        newTerm = new SimplePathTerm(toSub.getObject(), newFields);
      } else
        newTerm = toSub; // else, field is implictly removed by returning null
                         // list. substitution reduces term to toSub
      newTerm.setSubstituted(true);
      return newTerm;
    }
    this.setSubstituted(false);
    // this.substituted = false;
    return this;
  }

  // TODO: eliminate this. it's terrible
  public PathTerm substituteWithFieldName(PathTerm toSub, PointerVariable subFor, FieldReference fieldName) {
    Util.Unimp("don't call this method");
    /*
     * if (this.isIntegerConstant()) { this.setSubstituted(false);
     * //this.substituted = false; return this; } else if (this.object != null
     * && this.object.equals(subFor) && this.fields != null &&
     * this.fields.getFirst().equals(fieldName)) { if (toSub instanceof
     * SimplePathTerm) { SimplePathTerm term = (SimplePathTerm) toSub;
     * PointerVariable termObj = term.getObject(); PointerVariable otherObj =
     * this.object; if (termObj != null && termObj.equals(otherObj) &&
     * this.field != null) { SimplePathTerm newTerm = new
     * SimplePathTerm(term.getObject()); newTerm.setSubstituted(true); return
     * newTerm; } // else termObj is a constant, can't sub for a constant } else
     * { Util.Assert(false, "unhandled: subbing in complex constraint " +
     * toSub.toHumanReadableString()); } } this.setSubstituted(false);
     * //this.substituted = false;
     */
    return this;
  }

  /*
   * public PathTerm substitute(PathTerm toSub, SimplePathTerm subFor) {
   * Util.Debug("comparing " + subFor + " and " + this); if
   * (!this.isIntegerConstant() && this.getObject().equals(subFor.getObject())
   * && this.fields.getFirst().equals(subFor.getFields().getFirst())) if
   * (subFor.equals(this)) { Util.Debug("eq"); toSub.setSubstituted(true);
   * return toSub; } this.setSubstituted(false); return this; }
   */

  // TODO: is this ok with multiple levels of field deref?
  public PathTerm substitute(PathTerm toSub, SimplePathTerm subFor) {
    // Util.Debug("comparing " + subFor + " and " + this);
    if (subFor.equals(this)) {
      toSub.setSubstituted(true);
      return toSub;
    }
    
    this.setSubstituted(false);
    return this;
  }
  

  @Override
  public boolean symbContains(PathTerm other) {
    // TODO: for now, just simple equality check
    if (other instanceof PathTermWithBinOp)
      return false;
    return this.equals(other);
  }

  @Override
  public SimplePathTerm deepCopy() {
    return this; // ok because SimplePathTerm's are immutable
    /*
     * if (this.isConstant()) return new SimplePathTerm(constant); if (field ==
     * null) return new SimplePathTerm(object.deepCopy()); //new
     * SimplePathTerm(new String(object)); //if (arrayLength) return new
     * SimplePathTerm(object.deepCopy(), true); return new
     * SimplePathTerm(object.deepCopy(), field);//new SimplePathTerm(new
     * String(object), new String(field));
     */
  }

  @Override
  public boolean equals(Object other) {
    if (other instanceof PathTermWithBinOp)
      return false;
    SimplePathTerm pv = (SimplePathTerm) other;
    boolean fieldsNull = fields == null, otherFieldsNull = pv.getFields() == null;
    if (fieldsNull != otherFieldsNull)
      return false;
    if (fields != null) {
      if (!object.equals(pv.getObject()))
        return false; // compare obj's
      // compare fields;
      if (fields.size() != pv.getFields().size())
        return false;
      Iterator<FieldReference> iter1 = fields.iterator();
      Iterator<FieldReference> iter2 = pv.getFields().iterator();
      while (iter1.hasNext() && iter2.hasNext()) {
        if (!iter1.next().equals(iter2.next()))
          return false;
      }
      return true;
    } else if (pv.isIntegerConstant() && this.isIntegerConstant())
      return pv.getIntegerConstant() == constant;
    // else if (this.arrayLength != pv.isArrayLength()) return false;
    return Util.equal(object, pv.getObject());
  }

  @Override
  public int compareTo(Object other) {
    if (other instanceof PathTermWithBinOp)
      return 1;
    return this.repr.compareTo(((SimplePathTerm) other).repr);
    // return this.toString().compareTo(other.toString());
    /*
     * SimplePathTerm pv = (SimplePathTerm) other;
     * //System.err.println("comparing " + this + " and " + pv); //String
     * otherObject = pv.getObject(); PointerVariable otherObject =
     * pv.getObject(); LinkedList<FieldReference> otherFields =
     * pv.getFieldsAsLinkedList(); //System.err.println(this.getObject() + " . "
     * + this.getField()); //System.err.println(pv.getObject() + " . " +
     * pv.getField()); if (object == null && otherObject != null) return -1;
     * else if (object != null && otherObject == null) return 1; else if (object
     * == null && otherObject == null) {
     * //System.err.println("comparing constants"); // both are constants;
     * compare them if (constant > pv.getIntegerConstant()) return 1; else if
     * (constant < pv.getIntegerConstant()) return -1; else return 0; } else {
     * //System.err.println("comparing objs"); // compare objs int objComparison
     * = object.compareTo(otherObject); if (objComparison != 0) return
     * objComparison; // compare fields if (fields == null && otherFields !=
     * null) return -1; else if (fields != null && otherFields == null) return
     * 1; else if (fields == null && otherFields == null) return 0; else { if
     * (fields.size() > otherFields.size()) return 1; else if
     * (otherFields.size() > fields.size()) return -1; Iterator<FieldReference>
     * iter1 = fields.iterator(), iter2 = otherFields.iterator(); while
     * (iter1.hasNext() && iter2.hasNext()) { FieldReference field1 =
     * iter1.next(), field2 = iter2.next(); int comparison =
     * field1.toString().compareTo(field2.toString()); if (comparison != 0)
     * return comparison; } } return 0; }
     */
  }

  public String toHumanReadableString() {
    return this.toString();
    // if (field != null) return parseToHumanReadable(object.toString()) + "." +
    // parseToHumanReadable(field.toString());
    // return parseToHumanReadable(object.toString());
  }

  public void setSubstituted(boolean substituted) {
    this.substituted = substituted;
  }

  public boolean substituted() {
    return substituted;
  }

  public String toString() {
    if (repr != null)
      return repr;
    if (isIntegerConstant())
      return "" + constant;
    if (fields != null) {
      String str = object.toString();
      for (FieldReference field : fields) {
        str += "." + field;
      }
      return str;
    }
    // if (arrayLength) return object.toString() + ".length";
    return object.toString();
  }

  public PointerVariable getObject() {
    return object;
  }

  public LinkedList<FieldReference> getFieldsAsLinkedList() {
    return fields;
  }

  @Override
  public List<FieldReference> getFields() {
    return fields;
  }

  public boolean hasField() {
    return fields != null;
  }

  public FieldReference getFirstField() {
    return fields != null ? fields.getFirst() : null;
  }

  @Override
  public boolean isIntegerConstant() {
    return object == null && fields == null;
  }

  @Override
  public int evaluate() {
    Util.Pre(isIntegerConstant(), "should only eval constants!");
    return constant;
  }

  public int getIntegerConstant() {
    Util.Pre(isIntegerConstant(), "SHOULDN'T ASK FOR CONSTANT IF OBJECT ISN'T A CONST!");
    return constant;
  }

  // this code is terrible, but it's only for debugging
  public String parseToHumanReadable(String str) {
    try {
      if (this.isIntegerConstant())
        return "" + constant;
      // System.err.println("INPUT:" + str);
      if (str.contains("symb") || !str.contains("-"))
        return str;
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
    } catch (ArrayIndexOutOfBoundsException e) {
      return str;
    }
  }

  public AST toZ3AST(Context ctx, boolean boolVar) {
    try {
      if (this.isIntegerConstant()) {
        return ctx.MkInt(this.constant);
        //return Util.makeIntConst(this.constant, ctx);
      } else if (boolVar) {
        return ctx.MkBoolConst(this.toString());
        //return Util.makePropositionalVar(this.toString(), ctx);
      } else {
        return ctx.MkIntConst(this.toString());
        //return Util.makeIntVar(this.toString(), ctx);
      }
    } catch (Z3Exception e) {
      Util.Assert(false, "problem with z3 " + e);
      return null;
    }
  }

  public Set<PointerVariable> getVars() {
    return vars;
  }

  @Override
  public Set<SimplePathTerm> getTerms() {
    Set<SimplePathTerm> singleton = new TreeSet<SimplePathTerm>();
    singleton.add(this);
    return singleton;
  }
  
  // TOOD: make this suck less
  @Override
  public int hashCode() {
    return this.toString().hashCode();
  }

  @Override
  public Set<PointerKey> getPointerKeys() {
    Set<PointerKey> keys = HashSetFactory.make();
    if (pointer != null) keys.add(pointer);
    return keys;
  }

  public PointerKey getPointer() {
    return pointer;
  }
  
  @Override
  public int size() { return 1; }

  @Override
  public boolean isHeapLocation() {
    // need to be careful since we can read null from fields; this is why fields
    // must be null
    return this.object != null && !this.object.isLocalVar() && this.fields == null &&
        !(this.object.getInstanceKey() instanceof StaticFieldKey) && !(this.object.getInstanceKey() instanceof String);
  }

}

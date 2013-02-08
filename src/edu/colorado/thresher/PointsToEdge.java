package edu.colorado.thresher;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.IField;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;

public class PointsToEdge implements Constraint, Comparable {

	private final PointerVariable source;
	private final PointerVariable sink;
	private final PointerKey field;
	private final IField fieldRef;
	private final int fieldId;
	
	private final int hash;
	
	private static final int NONE = -1;
	private static final int ARRAY_CONTENTS = -2;
	
	//private final String uniqueId;
	
	public PointsToEdge(PointerVariable source, PointerVariable sink) {
		//this(source, sink, null);
		this.source = source;
		this.sink = sink;
		this.fieldRef = null;
		this.field = null;
		this.fieldId = NONE;
		this.hash = makeHash();
	}
	
	public PointsToEdge(PointerVariable source, PointerVariable sink, IField fieldRef) {
		this.source = source;
		this.sink = sink;
		this.fieldRef = fieldRef;
		if (fieldRef != null && source.getInstanceKey() != null) {
			this.fieldId = fieldRef.hashCode();
			if (source.getInstanceKey() instanceof StaticFieldKey) this.field = (StaticFieldKey) source.getInstanceKey();
			else if (fieldRef == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) this.field = new ArrayContentsKey((InstanceKey) source.getInstanceKey());
			else this.field = new InstanceFieldKey((InstanceKey) source.getInstanceKey(), fieldRef);
		} else {
			this.field = null;
			this.fieldId = NONE;
		}
		this.hash = makeHash();
	}
	/*
	public PointsToEdge(ConcretePointerVariable source, ConcretePointerVariable sink, IField fieldRef) {
		this.source = source;
		this.sink = sink;
		this.fieldRef = fieldRef;
		if (fieldRef != null) {
			this.fieldId = fieldRef.hashCode();
			if (source.getInstanceKey() instanceof StaticFieldKey) this.field = (StaticFieldKey) source.getInstanceKey();
			else if (fieldRef == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) this.field = new ArrayContentsKey((InstanceKey) source.getInstanceKey());
			else this.field = new InstanceFieldKey((InstanceKey) source.getInstanceKey(), fieldRef);
		} else {
			this.field = null;
			this.fieldId = NONE;
		}
	}
	
	public PointsToEdge(SymbolicPointerVariable source, PointerVariable sink, IField fieldRef) {
		this.source = source;
		this.sink = sink;
		this.field = null;
		this.fieldRef = fieldRef;
		this.fieldId = fieldRef.hashCode();
		//String fieldStr = fieldRef == null ? " " : fieldRef.hashCode() + "";
		//this.uniqueId = "_" + source.hashCode() + "_" + fieldStr + "_" + sink.hashCode();
	}
	
	public PointsToEdge(PointerVariable source, ConcretePointerVariable sink, IField fieldRef) {
		this.source = source;
		this.sink = sink;
		this.fieldRef = fieldRef;
		if (fieldRef != null) {
			this.fieldId = fieldRef.hashCode();
			if (source.getInstanceKey() instanceof StaticFieldKey) this.field = (StaticFieldKey) source.getInstanceKey();
			else if (fieldRef == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) this.field = new ArrayContentsKey((InstanceKey) source.getInstanceKey());
			else this.field = new InstanceFieldKey((InstanceKey) source.getInstanceKey(), fieldRef);
		} else {
			this.field = null;
			this.fieldId = NONE;
		}
		//String fieldStr = fieldRef == null ? " " : fieldRef.hashCode() + "";
		//this.uniqueId = "_" + source.hashCode() + "_" + fieldStr + "_" + sink.hashCode();
	}
	
	public PointsToEdge(ConcretePointerVariable source, PointerVariable sink, IField fieldRef) {
		this.source = source;
		this.sink = sink;
		this.fieldRef = fieldRef;
		if (fieldRef != null) {
			this.fieldId = fieldRef.hashCode();
			if (source.getInstanceKey() instanceof StaticFieldKey) this.field = (StaticFieldKey) source.getInstanceKey();
			else if (fieldRef == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) this.field = new ArrayContentsKey((InstanceKey) source.getInstanceKey());
			else this.field = new InstanceFieldKey((InstanceKey) source.getInstanceKey(), fieldRef);
		} else {
			this.field = null;
			this.fieldId = NONE;
		}
		
		//String fieldStr = fieldRef == null ? " " : fieldRef.hashCode() + "";
		//this.uniqueId = "_" + source.hashCode() + "_" + fieldStr + "_" + sink.hashCode();
	}
	*/
	
	public PointsToEdge(PointerVariable source, PointerVariable sink, PointerKey field) {
		this.source = source;
		this.sink = sink;
		this.field = field;
		if (field != null) {
			if (field instanceof InstanceFieldKey) {
				InstanceFieldKey ifk = (InstanceFieldKey) field;
				this.fieldRef = ifk.getField();		
				this.fieldId = fieldRef.hashCode();
			} else if (field instanceof StaticFieldKey) {
				StaticFieldKey sfk = (StaticFieldKey) field;
				this.fieldRef = sfk.getField();
				this.fieldId = fieldRef.hashCode();
			} else if (field instanceof ArrayContentsKey) {
				this.fieldRef = AbstractDependencyRuleGenerator.ARRAY_CONTENTS;
				this.fieldId = fieldRef.hashCode();
			} else {
				Util.Unimp("unhandled field type " + field);
				this.fieldRef = null;
				this.fieldId = NONE;
			}
		} else {
			this.fieldRef = null;
			this.fieldId = NONE;
		}
		this.hash = makeHash();
		//this.fieldName = fieldName;
		//if (fieldName != null) {
			//this.fieldId = Util.getIdForField(fieldName);
		//}
		//else {
			//this.fieldId = -1;
		//}
		
		// TODO: DEBUG
		/*
		if (field != null) {
			if (field instanceof ArrayContentsKey) {
				ArrayContentsKey ack = (ArrayContentsKey) field;
				Util.Assert(ack.getInstanceKey().equals(source.getInstanceKey()), "bad edge " + this + ". " + source.getInstanceKey() + " and " + ack.getInstanceKey());
			}
			else if (field instanceof InstanceFieldKey) {
				InstanceFieldKey ifk = (InstanceFieldKey) field;
				Util.Assert(ifk.getInstanceKey().equals(source.getInstanceKey()), "bad edge " + this + ". " + source.getInstanceKey() + " and " + ifk.getInstanceKey());
			}
		//} else Util.Assert(source.isLocalVar() || source.getInstanceKey() instanceof StaticFieldKey, "bad edge " + this);
		} else Util.Assert(source.isLocalVar(), "bad edge " + this);
		*/
		// END DEBUG
		
		//String fieldStr = field == null ? " " : field.hashCode() + "";
		//this.uniqueId = "_" + source.hashCode() + "_" + fieldStr + "_" + sink.hashCode();
	}
	
	public static PointsToEdge make(PointerVariable source, PointerVariable sink, PointerKey field) {
		if (source != null && sink != null) {
			return new PointsToEdge(source, sink, field);
		}
		return null;
	}
	
	public PointsToEdge deepCopy() {
		PointerVariable newSource = source.deepCopy();
		PointerVariable newSink = sink.deepCopy();
		return new PointsToEdge(newSource, newSink, field);
	}
	
	public boolean isSymbolic() {
		return source.isSymbolic() || sink.isSymbolic();
	}
	
	/*
	// substitute toSub for subFor in LHS of this edge
	public PointsToEdge substituteMethod(MethodReference toSub, MethodReference subFor) {
		if (this.source instanceof ConcretePointerVariable) {
			ConcretePointerVariable src = (ConcretePointerVariable) this.source;
			if (src.isLocalVar() && subFor.equals(src.getMethod())) {
				String newName = Util.makeLocalVarName(toSub, src.getUseNum());
				int newType = Util.getIdForType(newName);
				ConcretePointerVariable newSrc = new ConcretePointerVariable(toSub, src.getUseNum(), newName, newType);
				return new PointsToEdge(newSrc, this.sink, this.fieldName);
			}
		}
		//Util.Assert(false, "couldn't sub for " + toSub + " in " + this);
		return this;
	}
	*/
	
	@Override
	public String toString() {
		if (field == null) {
			if (fieldRef == null) return source.toString() + " -> " + sink.toString();
			else if (fieldRef == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) return source.toString() + " ->_ARR " + sink.toString();
			//return source.toString() + " ->_" + fieldRef + " " + sink.toString(); 
			return source.toString() + " ->_" + fieldRef.getName() + " " + sink.toString(); // TMP --debug only!
		} else {
			//return source.toString() + " ->_" + field + "<" + fieldId + "> " + sink.toString();
			//return source.toString() + " ->_" + field + " " + sink.toString();
			if (fieldRef == AbstractDependencyRuleGenerator.ARRAY_CONTENTS) return source.toString() + " ->_ARR " + sink.toString();
			return source.toString() + " ->_" + fieldRef.getName() + " " + sink.toString(); // TMP --debug only!
		}
	}
	
	public boolean symbEq(PointsToEdge other) {
		return this.source.symbEq(other.getSource()) && Util.equal(this.fieldRef, other.fieldRef) && this.sink.symbEq(other.getSink());
	}
	
	public boolean symbContains(PointsToEdge other) {
		return this.source.symbContains(other.getSource()) && Util.equal(this.fieldRef, other.fieldRef) && this.sink.symbContains(other.getSink());
	}
	
	/**
	 * 
	 * @param other
	 * @param subMaps
	 * @param alreadySubbed
	 * @param hard - mappings produced here are hard constraints -- add them to alreadySubbed
	 */
	public void getSubsFromEdge(PointsToEdge other, List<Map<SymbolicPointerVariable,PointerVariable>> subMaps , Set<PointerVariable> alreadySubbed, 
								boolean hard) {
		//Util.Debug("getting subs for " + this + " and " + other);
		List<Map<SymbolicPointerVariable,PointerVariable>> toAdd = new LinkedList<Map<SymbolicPointerVariable,PointerVariable>>();
		if (this.source.symbEq(other.getSource()) && Util.equal(this.fieldRef, other.fieldRef) && !alreadySubbed.contains(this.source)) {
			if (this.source.isSymbolic()) {
				for (Map<SymbolicPointerVariable,PointerVariable> subMap : subMaps) {
					PointerVariable sub = subMap.get(this.source); 
					
					if (sub != null && !sub.equals(other.getSource())) { // more than one instantiation choice. must do a case split
						Map<SymbolicPointerVariable,PointerVariable> copy = Util.copyMap(subMap);
						//Util.Debug("adding case split sub relationship " + this.source + " " + other.getSource());
						// the original map already has a value here; make a different choice
						copy.put((SymbolicPointerVariable) this.source, other.getSource());
						toAdd.add(copy);
						//Util.Unimp("did case split!");
					}
					
					//Util.Assert(sub == null || sub.equals(other.getSource()), 
						//		"more than one instantiation choice for " + this.source + ": " + sub + " and " + other.getSource());
					else if (sub == null && this.source != other.getSource()) {
						// add a case split where we do not bind this edge
						Map<SymbolicPointerVariable,PointerVariable> copy = Util.copyMap(subMap);
						//Util.Debug("adding case split where " + this.source + " not bound to " + other.getSource());
						toAdd.add(copy);
						
						//Util.Debug("adding sub relationship " + this.source + " " + other.getSource());
						subMap.put((SymbolicPointerVariable) this.source, other.getSource());
					}
				}
				
				subMaps.addAll(toAdd);
				toAdd.clear();
			}
			
			//Util.Debug("trying symbolic sink " + this.sink); 
			//Util.Debug("symbolic? " + this.sink.isSymbolic() + " symb eq " + other.getSink() + "? " + this.sink.symbEq(other.getSink()));
			if (this.sink.isSymbolic() && this.sink.symbEq(other.getSink()) && !alreadySubbed.contains(this.sink)) {
				for (Map<SymbolicPointerVariable,PointerVariable> subMap : subMaps) {
					PointerVariable sub = subMap.get(this.sink); 
					
					if (sub != null && !sub.equals(other.getSink())) { // more than one instantiation choice. must do a case split
						Map<SymbolicPointerVariable,PointerVariable> copy = Util.copyMap(subMap);
						//Util.Debug("adding case split sub relationship " + this.sink + " " + other.getSink());
						// the original map already has a value here; make a different choice
						copy.put((SymbolicPointerVariable) this.sink, other.getSink());
						toAdd.add(copy);
						//Util.Unimp("did case split!");
					}
					
					//Util.Assert(sub == null || sub.equals(other.getSink()), 
						//		"more than one instantiation choice for " + this.sink + ": " + sub + " and " + other.getSink());
					else if (sub == null && this.sink != other.getSink()) {
						//Util.Debug("adding sub relationship " + this.sink + " " + other.getSink());
						subMap.put((SymbolicPointerVariable) this.sink, other.getSink());
						if (hard) alreadySubbed.add(this.sink); // hard constraints should ot be mapped twiced
					}					
				}
				subMaps.addAll(toAdd);
			}				
		}
	}
	
	@Override
	public int compareTo(Object other) {
		PointsToEdge otherEdge = (PointsToEdge) other;
		int comparisonResult = this.source.compareTo(otherEdge.getSource());
		if (comparisonResult != 0) return comparisonResult;
		// src's eq
		if (this.field != null && otherEdge.field != null) {
			comparisonResult = this.field.toString().compareTo(otherEdge.field.toString());
			if (comparisonResult != 0) return comparisonResult;
		} else if (this.field == null && otherEdge.field != null) return -1;
		else if (this.field != null) return 1;
		// else, both are null/equal
		// fields eq; compare snk
		return this.sink.compareTo(otherEdge.getSink());
	}
	
	private int makeHash() {
		String hashStr = source.hashCode() + "_" + fieldId + "_" + sink.hashCode();
		return hashStr.hashCode();
	}
	
	@Override
	public int hashCode() {
		return hash;
		//return uniqueId.hashCode();
	}
	
	@Override
	public boolean equals(Object other) {
		if (other == null) return false;
		PointsToEdge p = (PointsToEdge) other;
		//return source.equals(p.getSource()) && Util.equal(this.field, p.field) && sink.equals(p.getSink());
		return source.equals(p.getSource()) && this.fieldId == p.fieldId && sink.equals(p.getSink());
	}
	
	public PointerVariable getSource() {
		return source;
	}
	
	public Set<SymbolicPointerVariable> getSymbolicVars() {
		Set<SymbolicPointerVariable> symbolicVars = new HashSet<SymbolicPointerVariable>();
		if (this.source.isSymbolic()) symbolicVars.add((SymbolicPointerVariable) this.source);
		if (this.sink.isSymbolic()) symbolicVars.add((SymbolicPointerVariable) this.sink);
		return symbolicVars;
	}
	
	/*
	public int getSourceId() {
		return sourceId;
	}
	
	public int getSinkId() {
		return sinkId;
	}
	*/
	/*
	public int getFieldId() {
		return fieldId;
	}
	*/
	
	public PointerVariable getSink() {
		return sink;
	}
	
	public PointerKey getField() {
		return field;
	}
	
	public IField getFieldRef() {
		return fieldRef;
	}
	/*
	public String getFieldName() {
		return fieldName;		
	}
	*/

	
	public boolean containsStringConst() {
		return sink.toString().equals("<Primordial,Ljava/lang/String>");
	}
	
	/*
	// used only for TOPLAS paper!
	public String toFormattedPointsToConstraint() {
		Util.Assert(false, "UNIMP!");
		//if (fieldName == null) {
		//return sink.toFormattedPointsToConstraint() + " <- " + source.toFormattedPointsToConstraint();
		//return source.toFormattedPointsToConstraint() + " -> " + sink.toFormattedPointsToConstraint();
		//} else {
			//return source.toFormattedPointsToConstraint() + " ->_" + fieldName + "<" + fieldId + "> " + sink.toFormattedPointsToConstraint();
		//}
		return "";
	}
	*/
	
	/*
	public void setSource(String srcName) {
		
		int oldsrcId = sourceId;
		source.setName(srcName);
		source.setSymbolic(false);
		this.sourceId = source.getId();
		this.sinkId = sink.getId();
		this.uniqueId = "_" + sourceId + "_" + fieldName + "_" + sinkId;
		
		//source = new PointerVariable(srcName);
		//source.changeName(srcName);
		source = source.withChangedName(srcName);
		this.uniqueId = "_" + source.getId() + "_" + fieldName + "_" + sink.getId();
	}
	
	public void setSink(String sinkName) {
		
		Util.Assert(rhsSymbolic, "RHS SHOULD BE SYMBOLIC FOR THIS TO BE CALLED");
		sink.setName(sinkName);
		sink.setSymbolic(false);
		this.sourceId = source.getId();
		this.sinkId = sink.getId();
		this.uniqueId = "_" + sourceId + "_" + fieldName + "_" + sinkId;
		
		//sink.changeName(sinkName);
		sink = sink.withChangedName(sinkName);
		//sink = new PointerVariable(sinkName);
		this.uniqueId = "_" + source.getId() + "_" + fieldName + "_" + sink.getId();
	}
	*/
	
}

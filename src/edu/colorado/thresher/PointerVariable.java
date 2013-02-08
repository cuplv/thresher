package edu.colorado.thresher;

import java.util.Set;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;


public interface PointerVariable extends Comparable {
	
	public PointerVariable deepCopy();
	
	//public String parseToHumanReadable(String str);
	
	@Override
	public String toString();
	
	//public String toFormattedPointsToConstraint();
	
	@Override
	public boolean equals(Object other);
	
	@Override
	public int hashCode();
	
	//public String getName();
	
	//public int getId();
	
	public boolean isSymbolic();
	
	//public int getTypeId();
	
	public boolean isLocalVar();
	
	public boolean isHeapVar();
	
	// get WALA instance key associated with this pointer variable
	// returns instance key or static field key
	public Object getInstanceKey();
	
	// returns instance num of variable
	//public int getInstanceNum();
	
	//public MethodReference getMethod();

	// are these variables possibly equal?
	public boolean symbEq(PointerVariable other);
	
	// does this possibly contain other?
	public boolean symbContains(PointerVariable other);
	
	public CGNode getNode();
	
	public Set<InstanceKey> getPossibleValues();
	
	// unconstrained instance num
	public static final int ANY_INSTANCE_NUM = -1;
	//@Override
	//public int compareTo(Object other);
	
	//public String makeNewSymbolicVariable();
	
	//public int getSymbCounter();
	
	//public void setSymbolic(boolean symbolic);
	
}

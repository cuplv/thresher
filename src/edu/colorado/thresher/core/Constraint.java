package edu.colorado.thresher.core;

import java.util.Set;

import com.ibm.wala.types.FieldReference;

public interface Constraint {

  /**
   * @return - unique identifying id that persists across substitution of
   *         constraints
   */
  // public int getId();
  public Set<FieldReference> getFields();
  
  public boolean isArrayIndexConstraint();
  
  public boolean isComparisonToConstant();
  
  public boolean isMultiDimArrayConstraint();
  
  public boolean isClinitConstraint();
  
  public Set<PointerVariable> getVars();

}

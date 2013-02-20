package edu.colorado.thresher;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;

public class PointerStatement implements Comparable {
  public static final String ARRAY = "0__ARRAY";

  public static enum EdgeType {
    Assign, GetField, PutField
  };

  private final SSAInstruction instr;
  private final PointerVariable lhs, rhs;
  private final EdgeType type;
  private final String fieldName;

  private final String methodName;

  // globally unique identifier for this statement
  private final int lineId;
  // line number of statement within WALA IR
  private final int lineNum;

  public PointerStatement(SSAInstruction instr, PointerVariable lhs, PointerVariable rhs, EdgeType type, String fieldName,
      int lineId, int lineNum) {
    this.instr = instr;
    this.methodName = null;
    this.lhs = lhs;
    this.rhs = rhs;
    this.type = type;
    this.fieldName = fieldName;
    this.lineId = lineId;
    this.lineNum = lineNum;
  }

  public static PointerStatement DUMMY = new PointerStatement(null, null, null, null, null, -1, -1);

  @Override
  public int hashCode() {
    return this.toString().hashCode();
  }

  public String toString() {
    if (lineId == -1)
      return "DUMMY";
    String result = null;
    switch (type) {
      case Assign:
        result = lhs.toString() + " := " + rhs.toString();
        break;
      case GetField:
        if (fieldName.equals(ARRAY)) {
          result = lhs.toString() + " := " + rhs.toString() + "[arr]";
        } else {
          result = lhs.toString() + " := " + rhs.toString() + "." + fieldName;
        }
        break;
      case PutField:
        if (fieldName.equals(ARRAY)) {
          result = lhs.toString() + "[arr] := " + rhs.toString();
        } else {
          result = lhs.toString() + "." + fieldName + " := " + rhs.toString();
        }
        break;
    }
    return "l(" + lineId + "," + lineNum + ") : " + result;
  }

  public SSAInstruction getInstr() {
    return instr;
  }

  public boolean isNewInstr() {
    return instr instanceof SSANewInstruction;
  }

  public String getFieldName() {
    return fieldName;
  }

  public int getLineNum() {
    return lineNum;
  }

  public int getLineId() {
    return lineId;
  }

  @Override
  public int compareTo(Object other) {
    PointerStatement otherStmt = (PointerStatement) other;
    if (this.getLineNum() < otherStmt.getLineNum())
      return -1;
    else if (this.getLineNum() > otherStmt.getLineNum())
      return 1;

    if (this.getLineId() < otherStmt.getLineId())
      return -1;
    else if (this.getLineId() > otherStmt.getLineId())
      return 1;

    return 0;
  }
}

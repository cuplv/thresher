package edu.colorado.thresher;

import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ssa.SSAInstruction;

public class WitnessInstruction {

  private final IMethod method;
  private final SSAInstruction instruction;
  private final int srcIndex;
  private final int bytecodeIndex;

  public WitnessInstruction(IMethod method, SSAInstruction instruction, int srcIndex, int bytecodeIndex) {
    this.method = method;
    this.instruction = instruction;
    this.srcIndex = srcIndex;
    this.bytecodeIndex = bytecodeIndex;
  }

  public String toString() {
    return method + "," + instruction + "," + srcIndex + "," + bytecodeIndex;
  }
}

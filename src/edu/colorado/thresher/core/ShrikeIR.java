package edu.colorado.thresher.core;

import com.ibm.wala.cfg.ShrikeCFG;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSABuilder;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.ssa.SSAPiNodePolicy;
import com.ibm.wala.ssa.ShrikeIndirectionData;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.ssa.analysis.DeadAssignmentElimination;

// extracted version of the anonymous IR class created in ShrikeIRFactory
public class ShrikeIR extends IR {
  private final SSA2LocalMap localMap;  

  private final ShrikeIndirectionData indirectionData;
  
  private final IBytecodeMethod method;

  private static final boolean buildLocalMap = true;
  
  // all of this global state is a horrendous hack to allow us to pass the correct variables to super()
  // WALA gets around this by using an anonymous class that captures these variables, but that solution
  // isn't acceptable for us because we want to be able to extend the ShrikeIR class
  private static SymbolTable _symbolTable;
  private static SSACFG _cfg;
  private static SSABuilder _builder;
  
  static void clearGlobals() {
    _symbolTable = null;
    _cfg = null;
    _builder = null;
  }
  
  private static SSAInstruction[] makeNewInstructions(IBytecodeMethod method, SSAOptions options) {
    _symbolTable = new SymbolTable(method.getNumberOfParameters());
    ShrikeCFG shrikeCFG = (ShrikeCFG) ShrikeCFG.make(method);
    com.ibm.wala.shrikeBT.IInstruction[] shrikeInstructions = null;
    try {
      shrikeInstructions = method.getInstructions();
    } catch (InvalidClassFileException e) {
      System.out.println("Bad bytecodes " + e);
      System.exit(1);
    }
    final SSAInstruction[] newInstrs = new SSAInstruction[shrikeInstructions.length];
    _cfg = new SSACFG(method, shrikeCFG, newInstrs);
    _builder = SSABuilder.make(method, _cfg, shrikeCFG, newInstrs, _symbolTable, buildLocalMap, options
        .getPiNodePolicy());
    _builder.build();
    return newInstrs;
  }  
    
  public ShrikeIR(IBytecodeMethod method, SSAOptions options) {    
    super(method, makeNewInstructions(method, options), _symbolTable, _cfg, options);
    this.method = method;
   
    if (buildLocalMap)
      localMap = _builder.getLocalMap();
    else
      localMap = null;

    indirectionData = _builder.getIndirectionData();
    
    eliminateDeadPhis();
    setupLocationMap();  
    clearGlobals();
  }    
  
  /**
   * Remove any phis that are dead assignments.
   * 
   * TODO: move this elsewhere?
   */
  private void eliminateDeadPhis() {
    DeadAssignmentElimination.perform(this);
  }

  @Override
  protected String instructionPosition(int instructionIndex) {
    try {
      int bcIndex = method.getBytecodeIndex(instructionIndex);
      int lineNumber = method.getLineNumber(bcIndex);

      if (lineNumber == -1) {
        return "";
      } else {
        return "(line " + lineNumber + ")";
      }
    } catch (InvalidClassFileException e) {
      return "";
    }
  }

  @Override
  public SSA2LocalMap getLocalMap() {
    return localMap;
  }    

  @SuppressWarnings("unchecked")
  @Override
  protected ShrikeIndirectionData getIndirectionData() {
     return indirectionData;
  }

}

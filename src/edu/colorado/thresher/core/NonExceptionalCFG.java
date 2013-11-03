package edu.colorado.thresher.core;

import java.util.Iterator;

import com.ibm.wala.cfg.AbstractCFG;
import com.ibm.wala.cfg.IBasicBlock;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.shrikeBT.IInstruction;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.debug.UnimplementedError;
import com.ibm.wala.util.intset.IntSet;

public class NonExceptionalCFG extends SSACFG {

 public NonExceptionalCFG(SSACFG cfg) {
   super(cfg.getMethod(), cfg.delegate, cfg.getInstructions());
 }

 @Override
 public Iterator<ISSABasicBlock> getSuccNodes(ISSABasicBlock b) throws IllegalArgumentException {
   if (b == null) {
     throw new IllegalArgumentException("b == null");
   }
   IBasicBlock<IInstruction> n = delegate.getNode(b.getNumber());
   final Iterator i = delegate.getNormalSuccessors(n).iterator();
   return new Iterator<ISSABasicBlock>() {
     @Override
     public boolean hasNext() {
       return i.hasNext();
     }

     @Override
     public ISSABasicBlock next() {
       IBasicBlock n = (IBasicBlock) i.next();
       int number = n.getNumber();
       return NonExceptionalCFG.this.getNode(number);
     }

     @Override
     public void remove() {
       Assertions.UNREACHABLE();
     }
   };
 }
 
 @Override
 public int getSuccNodeCount(ISSABasicBlock b) throws IllegalArgumentException {
   if (b == null) {
     throw new IllegalArgumentException("b == null");
   }
   IBasicBlock<IInstruction> n = delegate.getNode(b.getNumber());
   return delegate.getNormalSuccessors(n).size();
 }

 @Override
 public Iterator<ISSABasicBlock> getPredNodes(ISSABasicBlock b) throws IllegalArgumentException {
   if (b == null) {
     throw new IllegalArgumentException("b == null");
   }
   IBasicBlock<IInstruction> n = delegate.getNode(b.getNumber());
   final Iterator i = delegate.getNormalPredecessors(n).iterator();
   return new Iterator<ISSABasicBlock>() {
     @Override
     public boolean hasNext() {
       return i.hasNext();
     }

     @Override
     public BasicBlock next() {
       IBasicBlock n = (IBasicBlock) i.next();
       int number = n.getNumber();
       return NonExceptionalCFG.this.getNode(number);
     }

     @Override
     public void remove() {
       Assertions.UNREACHABLE();
     }
   };
 }
 
 @Override
 public int getPredNodeCount(ISSABasicBlock b) throws IllegalArgumentException {
   if (b == null) {
     throw new IllegalArgumentException("b == null");
   }
   IBasicBlock<IInstruction> n = delegate.getNode(b.getNumber());
   return delegate.getNormalPredecessors(n).size();
 }
 
 // TODO: implement these? not used for now
 @Override
 public boolean hasEdge(ISSABasicBlock src, ISSABasicBlock dst) throws UnimplementedError {
   Assertions.UNREACHABLE();
   return false;
 }

 @Override
 public IntSet getSuccNodeNumbers(ISSABasicBlock b) throws IllegalArgumentException {
   Assertions.UNREACHABLE();
   return null;
 }

 @Override
 public IntSet getPredNodeNumbers(ISSABasicBlock node) throws UnimplementedError {
   Assertions.UNREACHABLE();
   return null;
 }
  
}

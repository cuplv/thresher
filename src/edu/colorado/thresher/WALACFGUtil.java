package edu.colorado.thresher;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.graph.Acyclic;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;
import com.ibm.wala.util.intset.IBinaryNaturalRelation;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntPair;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.MutableSparseIntSet;

/**
 * utility class for asking various common questions about WALA CFG's 
 * @author sam
 *
 */
public class WALACFGUtil {

	// optimization: map from IR to loop headers for that IR to save us from recomputing loop heads 
	private static final Map<IR,MutableIntSet> loopHeadersCache = new HashMap<IR, MutableIntSet>();
	// optimization: map from IR to dominators for that IR to save us from recomputing dominators
	private static final Map<IR,Dominators<ISSABasicBlock>> dominatorsCache = new HashMap<IR, Dominators<ISSABasicBlock>>();
	// optimization: map from (IR, loop head) to blocks contained in that loop head 
	private static final Map<Pair<IR,SSACFG.BasicBlock>,Set<ISSABasicBlock>> loopBodyCache = new HashMap<Pair<IR,SSACFG.BasicBlock>,Set<ISSABasicBlock>>();

	// CGNode for class initializers
	private static CGNode fakeWorldClinit = null;
	
	/**
	 * empty the loop header and dominators cache - should do before analyzing a new program 
	 */
	public static void clearCaches() {
		loopHeadersCache.clear();
		dominatorsCache.clear();
		fakeWorldClinit = null;
	}
	
	/**
	 * @param instr - suspected constructor
	 * @return true if instr is a constructor, false otherwise
	 */
	public static boolean isConstructor(SSAInvokeInstruction instr) { return instr.isSpecial() && instr.toString().contains("<init>"); }
	
	
	public static boolean isClassInit(SSAInvokeInstruction instr) { return instr.isStatic() && instr.toString().contains("<clinit>"); }

	
	/**
	 * @param suspected loop head
	 * @param IR for block containing suspected loop head
	 * @return true if suspsectedHead is a loop head, false otherwise
	 */
	public static boolean isLoopHead(SSACFG.BasicBlock suspectedHead, IR ir) {
		MutableIntSet loopHeaders = getLoopHeaders(ir);
		SSACFG cfg = ir.getControlFlowGraph();
		if (loopHeaders.contains(cfg.getNumber(suspectedHead))) return true;
		return false;
	}

	/**
	 * get loop headers from cache or create them 
	 */
	static MutableIntSet getLoopHeaders(IR ir) {
		MutableIntSet loopHeaders = loopHeadersCache.get(ir); 
		final SSACFG cfg = ir.getControlFlowGraph();
		if (loopHeaders == null) {
			loopHeaders = MutableSparseIntSet.makeEmpty();
			final IBinaryNaturalRelation backEdges = Acyclic.computeBackEdges(cfg, cfg.entry());
			final Dominators<ISSABasicBlock> domInfo = getDominators(ir);
					
			for (IntPair p : backEdges) {
				final ISSABasicBlock src = cfg.getNode(p.getX());
				final ISSABasicBlock dst = cfg.getNode(p.getY());
				if (domInfo.isDominatedBy(src, dst)) {
					//Util.Debug("loop header " + dst);
					loopHeaders.add(p.getY());
					
					// also add blocks that loop header transitions to directly (i.e. no splits)
					// this is to handle loop structures where the loop leader consists of multiple blocks (i.e. one with phi nodes and arithmetic, and another
					// with the actual conditional branch instr)
					Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(dst);
					while (succs.size() == 1) {
						ISSABasicBlock succ = succs.iterator().next();
						if (succ.equals(src)) break; // avoid (explicitly) infinite loops
						loopHeaders.add(cfg.getNumber(succ));
						succs = cfg.getNormalSuccessors(succ);
					}
				}
			}
			loopHeadersCache.put(ir, loopHeaders);
		}
		return loopHeaders;
	}
	
	static boolean isDominatedBy(SSACFG.BasicBlock dominated, SSACFG.BasicBlock master, IR ir) {
		Dominators<ISSABasicBlock> domInfo = getDominators(ir);
		//return domInfo.isDominatedBy(dominated, master);
		boolean result = domInfo.isDominatedBy(dominated, master);
		//Util.Debug(dominated + " dominated by " + master + "? " + result);
		return result;
	}
	
	/**
	 * get dominators from cache or create them 
	 */
	static Dominators<ISSABasicBlock> getDominators(IR ir) {
		Dominators<ISSABasicBlock> domInfo = dominatorsCache.get(ir);
		if (domInfo == null) {
			final SSACFG cfg = ir.getControlFlowGraph();
			domInfo = Dominators.make(cfg, cfg.entry());
			dominatorsCache.put(ir, domInfo);
		}
		return domInfo;
	}
	
	/**
	 * is suspectedEscapeBlock inside of the loop, or BEFORE it? 
	 * THIS SHOULD NOT BE USED TO ASK IF A BLOCK IS AFTER THE LOOP
	 * @param loopHead - head of loop whose escape block we are looking for
	 * @return - true if escape block, false otherwise
	 */
	public static boolean isLoopEscapeBlock(SSACFG.BasicBlock suspectedEscapeBlock, SSACFG.BasicBlock loopHead, IR ir) {
		//Util.Debug("is " + suspectedEscapeBlock + " an escape block for loop head " + loopHead);
		Dominators<ISSABasicBlock> domInfo = getDominators(ir);
		if (!isInLoopBody(suspectedEscapeBlock, loopHead, ir) && // we have an escape block if it's not in the loop...
				domInfo.isDominatedBy(loopHead, suspectedEscapeBlock)) { // ... and it dominates the loop head
			return true;
		}
		return false;
	}

	/**
	 * @return - true if suspectedLoopBodyBlock is in the body of *any* loop, false otherwise
	 */
	public static boolean isInLoopBody(SSACFG.BasicBlock suspectedLoopBodyBlock, IR ir) {
		return getLoopHeadForBlock(suspectedLoopBodyBlock, ir) != null;
	}
	
	/**
	 * @return - head of loop containing suspectedLoopBodyBlock if there is one, null otherwise
	 */
	public static SSACFG.BasicBlock getLoopHeadForBlock(SSACFG.BasicBlock suspectedLoopBodyBlock, IR ir) {
		//Util.Debug("is " + suspectedLoopBodyBlock + " in loop body?");
		final Dominators<ISSABasicBlock> domInfo = getDominators(ir);
		final MutableIntSet loopHeaders = getLoopHeaders(ir);
		final SSACFG cfg = ir.getControlFlowGraph();
		final IntIterator iter = loopHeaders.intIterator();
		while (iter.hasNext()) {
			SSACFG.BasicBlock loopHeadBlock = cfg.getBasicBlock(iter.next());
			if (domInfo.isDominatedBy(suspectedLoopBodyBlock, loopHeadBlock) &&   // a block B is in a loop body if it is dominated by the loop head...
					isReachableFrom(suspectedLoopBodyBlock, loopHeadBlock, ir)) { // ...and the loop head is reachable from B
				return loopHeadBlock;
			}
		}
		return null;
	}
	
	/**
	 * get the block that precedes a loop
	 * @param loopHead
	 * @param ir
	 * @return
	 */
	public static SSACFG.BasicBlock getEscapeBlockForLoop(SSACFG.BasicBlock loopHead, IR ir) {
		Util.Pre(isLoopHead(loopHead, ir), "must be loop head!");
		Set<ISSABasicBlock> body = getLoopBodyBlocks(loopHead, ir);
		SSACFG cfg = ir.getControlFlowGraph();
		for (ISSABasicBlock blk : body) {
			Iterator<ISSABasicBlock> preds = cfg.getPredNodes(blk);
			while (preds.hasNext()) {
				ISSABasicBlock next = preds.next();
				if (!body.contains(next)) return (SSACFG.BasicBlock) next;
			}
		}
		Util.Unimp("couldn't find escape block for loopHead " + loopHead);
		return null;
	}
		
	public static boolean isExplicitlyInfiniteLoop(SSACFG.BasicBlock loopHead, IR ir) {
		Util.Pre(isLoopHead(loopHead, ir), "must be loop head!");
		Set<ISSABasicBlock> body = getLoopBodyBlocks(loopHead, ir);
		SSACFG cfg = ir.getControlFlowGraph();
		for (ISSABasicBlock blk : body) {
			Iterator<ISSABasicBlock> succs = cfg.getSuccNodes(blk);
			while (succs.hasNext()) {
				//if (body.contains(succs.next())) return true;
				if (!body.contains(succs.next())) return false;
			}
		}
		//return false;
		return true;
	}
	
	private static Set<ISSABasicBlock> getLoopBodyBlocks(SSACFG.BasicBlock loopHead, IR ir) {
		/*
		Pair<IR,SSACFG.BasicBlock> key = Pair.make(ir, loopHead);
		Set<ISSABasicBlock> loopBody = loopBodyCache.get(key);
		if (loopBody == null) { // not found in cache; get loop body
			loopBody = new HashSet<ISSABasicBlock>();
			List<ISSABasicBlock> headList = Collections.singletonList((ISSABasicBlock) loopHead);
			SCCIterator<ISSABasicBlock> sccIter = new SCCIterator<ISSABasicBlock>(ir.getControlFlowGraph(), headList.iterator());
			boolean multipleSccs = false;
			while (sccIter.hasNext()) {
				Set<ISSABasicBlock> scc = sccIter.next();
				for (ISSABasicBlock blk : scc) Util.Debug("scc blk " + blk);
				loopBody.addAll(scc);
				Util.Debug("done with scc");
				Util.Assert(!multipleSccs, "more than one scc for loop head " + loopHead + " ir\n" + ir);
				multipleSccs = true;
			}
			loopBodyCache.put(key, loopBody);
		}
		*/
		
		Pair<IR,SSACFG.BasicBlock> key = Pair.make(ir, loopHead);
		Set<ISSABasicBlock> loopBody = loopBodyCache.get(key);
		if (loopBody == null) {
			//Util.Debug("getting loop body blocks for ir " + ir);
			loopBody = new HashSet<ISSABasicBlock>();
			loopBody.add(loopHead);
			// find the forward escape block of the loopHead
			SSACFG cfg = ir.getControlFlowGraph();
			Set<ISSABasicBlock> seen = new HashSet<ISSABasicBlock>();
			Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors((ISSABasicBlock) loopHead);
			while (succs.size() < 2) { // we're in a loop setup block. keep executing until we hit the conditional split for the loop or we wrap around
				ISSABasicBlock next = succs.iterator().next();
				loopHead = (SSACFG.BasicBlock) next;
				if (!seen.add(next)) {
					// this is an expliclity infinite loop, and we've wrapped back around to the beginning. return seen set
					return seen;
				}
				succs = cfg.getNormalSuccessors(next);
			}
			// now we should have > 1 succ
			Util.Assert(succs.size() > 1, "need to be looking a loop escape block! instead have succs of " + loopHead);
			Set<ISSABasicBlock> toExplore = new HashSet<ISSABasicBlock>();
			boolean escapeBlock = true;
			for (ISSABasicBlock succ : succs) {
				//if (succ.getLastInstructionIndex() >= 0 && succ.getLastInstruction() instanceof SSAGotoInstruction) toExplore.add(succ); 				
				if (escapeBlock) escapeBlock = false; // throw away escape block... we only want to explore blocks in the loop
				else toExplore.add(succ);
			}
			
			//Set<ISSABasicBlock> seen = new HashSet<ISSABasicBlock>(); // protection against explicitly infinite loops
			while (!toExplore.isEmpty()) {
				ISSABasicBlock blk = toExplore.iterator().next();
				toExplore.remove(blk);
				SSAInstruction lastInstr = blk.getLastInstruction();
				// if this block ends in a return, don't execute its successors
				if (lastInstr instanceof SSAReturnInstruction) continue;
				succs = cfg.getNormalSuccessors(blk);
				// check for break statements; don't want to execute successors if this block ends in a break
				if (lastInstr instanceof SSAGotoInstruction) { // breaks are goto's that send us outside of the loop
					if (succs.size() == 1 && !isReachableFrom((SSACFG.BasicBlock) blk, loopHead, ir)) { // if we can't get to the loop head from this goto, it's a break 
						continue;
					}
				}
				for (ISSABasicBlock succ : succs) {
					if (loopBody.add(blk)) toExplore.add(succ);
				}
			}
			
			Util.Debug("loop body blocks for " + loopHead);
			for (ISSABasicBlock blk : loopBody) Util.Debug(blk.toString());
			loopBodyCache.put(key, loopBody);
		}
		return loopBody;
	}
	
	/**
	 * @return - true if suspectedLoopBodyBlock is in the body of loop dominated by loopHead, false otherwise
	 */
	public static boolean isInLoopBody(SSACFG.BasicBlock suspectedLoopBodyBlock, SSACFG.BasicBlock loopHead, IR ir) {
		Set<ISSABasicBlock> loopBodyBlocks = getLoopBodyBlocks(loopHead, ir);
		//return loopBodyBlocks.contains(suspectedLoopBodyBlock);
		boolean result = loopBodyBlocks.contains(suspectedLoopBodyBlock);
		//Util.Debug(suspectedLoopBodyBlock + " in loop body headed by " + loopHead + "? " + result);
		return result;
		/*
		final Dominators<ISSABasicBlock> domInfo = getDominators(ir);
		// WRONG. this doesn't get blocks with loop break or returns...
		if (domInfo.isDominatedBy(suspectedLoopBodyBlock, loopHead) &&   // a block B is in a loop body if it is dominated by the loop head...
				(isReachableFrom(suspectedLoopBodyBlock, loopHead, ir) || // ...and the loop head is reachable from be, as a normal loop block is
				 //!isReachableFrom(escapeBlock, suspectedLoopBodyBlock, ir) || // ...or the block ends in a return statement...
				 ) { 
			return true;
		}
		return false;
		*/
	}
	
	/**
	 * @param loopHead - the head of the loop whose instructions we want
	 * @param ir - IR for the method containing the loop
	 * @return - set of all instructions contained in the loop
	 */
	public static Set<SSAInstruction> getInstructionsInLoop(SSACFG.BasicBlock loopHead, IR ir) {
		Set<SSAInstruction> instrs = new HashSet<SSAInstruction>();

		Set<ISSABasicBlock> loopBodyBlocks = getLoopBodyBlocks(loopHead, ir);
		for (ISSABasicBlock blk : loopBodyBlocks) {
			instrs.addAll(((SSACFG.BasicBlock) blk).getAllInstructions());
		}
		/*
		Set<SSAInstruction> instrs = new HashSet<SSAInstruction>();
		instrs.addAll(loopHead.getAllInstructions());
		SSACFG cfg = ir.getControlFlowGraph();
		final LinkedList<ISSABasicBlock> toExplore = new LinkedList<ISSABasicBlock>();
		
		for (ISSABasicBlock pred : cfg.getNormalPredecessors(loopHead)) {
			if (!isLoopEscapeBlock((SSACFG.BasicBlock) pred, loopHead, ir)) {
				toExplore.add(pred);
			}
		}
		
		final Set<SSACFG.BasicBlock> loopHeadsSeen = new HashSet<SSACFG.BasicBlock>();
		loopHeadsSeen.add(loopHead);
		
		while (!toExplore.isEmpty()) {
			SSACFG.BasicBlock blk = (SSACFG.BasicBlock) toExplore.remove();
			if (!isLoopHead(blk, ir) || loopHeadsSeen.add(blk)) { // avoid infinite loops
				instrs.addAll(blk.getAllInstructions());
				toExplore.addAll(cfg.getNormalPredecessors(blk));
			}
		}
		*/
		return instrs;
	}
	
	public static Set<CGNode> getCallTargetsInLoop(SSACFG.BasicBlock loopHead, CGNode loopNode, CallGraph cg) {
		IR ir = loopNode.getIR();
		Set<SSAInstruction> loopInstrs = getInstructionsInLoop(loopHead, ir);
		Set<CGNode> possibleTargets = new HashSet<CGNode>();
		for (SSAInstruction instr : loopInstrs) { // drop all vars that can be written to in the loop body
			if (instr instanceof SSAInvokeInstruction) {
				SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
				//Util.Debug("adding call " + call);
				possibleTargets.addAll(cg.getPossibleTargets(loopNode, call.getCallSite()));
			}
		}
		return possibleTargets;
	}
	
	/**
	 * @param srcBlk - block to search forward from
	 * @param dstBlk - block we are looking for
	 * @param ir - IR of method containing blocks
	 * @return - true if dstBlk is reachable from srcBlk, false otherwise
	 */
	public static boolean isReachableFrom(SSACFG.BasicBlock srcBlk, SSACFG.BasicBlock dstBlk, IR ir) {
		final SSACFG cfg = ir.getControlFlowGraph();
		// TODO: make more efficient; LinkedList allows duplicate blocks to be added
		final LinkedList<ISSABasicBlock> toExplore = new LinkedList<ISSABasicBlock>();
		toExplore.addAll(cfg.getNormalSuccessors(srcBlk));
		final Set<SSACFG.BasicBlock> loopHeadsSeen = new HashSet<SSACFG.BasicBlock>();
		while (!toExplore.isEmpty()) {
			SSACFG.BasicBlock blk = (SSACFG.BasicBlock) toExplore.remove();
			if (blk.equals(dstBlk)) return true;
			else if (!isLoopHead(blk, ir) || loopHeadsSeen.add(blk)) { // avoid infinite loops
				toExplore.addAll(cfg.getNormalSuccessors(blk));
			}
		}		
		return false;
	}
	
	public static CGNode getClassInitializerFor(IClass clazz, CallGraph callGraph) {
		Set<CGNode> classInits = callGraph.getNodes(clazz.getClassInitializer().getReference());
		Util.Assert(classInits.size() == 1, "should be exactly one class init!");
		return classInits.iterator().next();
	}
	
	/**
	 * find and return fakeWorldClinitNode. this seems unnecessarily hard to do. 
	 * @param cg
	 * @return
	 */
	public static CGNode getFakeWorldClinitNode(CallGraph cg) {
		// find fakeWorldClinit node (class initializers)
		if (fakeWorldClinit == null) {
			Iterator<CGNode> iter = cg.iterator();
			while (iter.hasNext()) {
				CGNode node = iter.next();
				if (node.getMethod().toString().equals("synthetic < Primordial, Lcom/ibm/wala/FakeRootClass, fakeWorldClinit()V >")) {
					fakeWorldClinit = node;
				}
				/*// note: this didn't work...
				CallSiteReference ref = iter.next();
				System.err.println(ref.getDeclaredTarget().toString());
				if (ref.getDeclaredTarget().toString().equals("< Primordial, Lcom/ibm/wala/FakeRootClass, fakeWorldClinit()V >")) {
					fakeWorldClinit = cg.getNodes(ref.getDeclaredTarget()).iterator().next();
				}
				*/
			}
			Util.Assert(fakeWorldClinit != null, "Couldn't find fakeWorldClinit!");
		}
		return fakeWorldClinit;
	}
	
	public static boolean isFakeWorldClinit(CGNode node, CallGraph cg) {
		return isFakeWorldClinit(node.getMethod().getReference(), cg);
	}
	
	public static boolean isFakeWorldClinit(MethodReference method, CallGraph cg) {
		CGNode clinit = getFakeWorldClinitNode(cg);
		return method.toString().equals(clinit.getMethod().getReference().toString());
	}
	
	/**
	 * @return index into blk corresponding to instr
	 */
	public static int findInstrIndexInBlock(SSAInstruction instr, SSACFG.BasicBlock blk) {
		int index = 0;
		for (SSAInstruction blkInstr : blk.getAllInstructions()) {
			// we have to do a string comparison here because if the instr's belong to IR's from different contexts they won't compare equal
			if (blkInstr.toString().equals(instr.toString())) return index;
			//if (blkInstr.equals(instr)) return index; 
			index++;
		}
		Util.Assert(false, "couldn't find instr " + instr + " in block " + blk);
		return -1;
	}
	
	/**
	 * @param blk - block to begin execution from
	 * @return - true if straight-line execution forward from blk definitely ends in a thrown exception; false otherwise
	 */
	public static boolean endsInThrownException(SSACFG.BasicBlock blk, SSACFG cfg) {
		for (;;) {
			if (!blk.getAllInstructions().isEmpty() && blk.getLastInstruction() instanceof SSAThrowInstruction) return true;
			Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(blk);
			if (succs.isEmpty() || succs.size() > 1) return false; // either we hit the end of the proc without throwing, or the path splits
			blk = (SSACFG.BasicBlock) succs.iterator().next();
		} 
	}
	
	/**
	 * are two methods the same except for the Primordial / Application classloader scope?
	 */
	public static boolean equalExceptScope(MethodReference method1, MethodReference method2) {
		String methodName1 = method1.getName().toString(), methodName2 = method2.getName().toString();
		if (methodName1.equals(methodName2)) {
			return method1.getDeclaringClass().getName().toString().equals(method2.getDeclaringClass().getName().toString());
		}
		return false;
	}
	
	
	public int distanceToEntrypoint(CallGraph cg, CGNode node) {
		BFSPathFinder<CGNode> finder = new BFSPathFinder<CGNode>(cg, cg.getEntrypointNodes().iterator(), node);
		List<CGNode> lst = finder.find();
		if (lst != null) return lst.size();
		return -1;
	}
	
	public static SSAInvokeInstruction getCallInstructionFor(CGNode callee, CGNode caller) {
		MethodReference calleeMethod = callee.getMethod().getReference();
		Iterator<SSAInstruction> instrs = caller.getIR().iterateAllInstructions();
		while (instrs.hasNext()) {
			SSAInstruction instr = instrs.next();
			if (instr instanceof SSAInvokeInstruction) {
				SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
				//if (call.getDeclaredTarget().equals(calleeMethod)) {
				if (equalExceptScope(call.getDeclaredTarget(), calleeMethod)) {
					return call;
				}
			}

		}
		Util.Assert(false, "couldn't find call to " + callee + " in caller " + caller);
		return null;
	}
	
	public static SSAInvokeInstruction getCallInstructionFor(CGNode callee, CGNode caller, CallGraph cg) {
		Set<CallSiteReference> siteRefs = Util.iteratorToSet(cg.getPossibleSites(caller, callee));
				
		MethodReference calleeMethod = callee.getMethod().getReference();
		Iterator<SSAInstruction> instrs = caller.getIR().iterateAllInstructions();
		while (instrs.hasNext()) {
			SSAInstruction instr = instrs.next();
			if (instr instanceof SSAInvokeInstruction) {
				SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
				//if (call.getDeclaredTarget().equals(calleeMethod)) {
				if (siteRefs.contains(call.getCallSite())) return call;
				//if (equalExceptScope(call.getDeclaredTarget(), calleeMethod)) {
					//return call;
				//}
			}

		}
		Util.Assert(false, "couldn't find call to " + callee + " in caller " + caller);
		return null;
	}
	
}

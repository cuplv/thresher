/**
 * Refinement Analysis Tools is Copyright (c) 2007 The Regents of the
 * University of California (Regents). Provided that this notice and
 * the following two paragraphs are included in any distribution of
 * Refinement Analysis Tools or its derivative work, Regents agrees
 * not to assert any of Regents' copyright rights in Refinement
 * Analysis Tools against recipient for recipient's reproduction,
 * preparation of derivative works, public display, public
 * performance, distribution or sublicensing of Refinement Analysis
 * Tools and derivative works, in source code and object code form.
 * This agreement not to assert does not confer, by implication,
 * estoppel, or otherwise any license or rights in any intellectual
 * property of Regents, including, but not limited to, any patents
 * of Regents or Regents' employees.
 * 
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT,
 * INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES,
 * INCLUDING LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE
 * AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *   
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE AND FURTHER DISCLAIMS ANY STATUTORY
 * WARRANTY OF NON-INFRINGEMENT. THE SOFTWARE AND ACCOMPANYING
 * DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS PROVIDED "AS
 * IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 */
package edu.colorado.thresher.core;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.demandpa.alg.ContextSensitiveStateMachine;
import com.ibm.wala.demandpa.alg.DemandRefinementPointsTo;
import com.ibm.wala.demandpa.alg.DemandRefinementPointsTo.PointsToResult;
import com.ibm.wala.demandpa.alg.refinepolicy.AbstractRefinementPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.AlwaysRefineCGPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.FieldRefinePolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.ManualFieldPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.ManualRefinementPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.RefinementPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.RefinementPolicyFactory;
import com.ibm.wala.demandpa.alg.refinepolicy.TunedFieldRefinementPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.TunedRefinementPolicy;
import com.ibm.wala.demandpa.alg.statemachine.StateMachineFactory;
import com.ibm.wala.demandpa.flowgraph.IFlowLabel;
import com.ibm.wala.demandpa.util.MemoryAccessMap;
import com.ibm.wala.demandpa.util.PABasedMemoryAccessMap;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.Predicate;
import com.ibm.wala.util.ProgressMaster;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.intset.OrdinalSet;

/**
 * Uses a demand-driven points-to analysis to check the safety of downcasts.
 * 
 * @author Manu Sridharan
 * 
 */
public class DemandCastChecker {

  // maximum number of casts to check
  private static final int MAX_CASTS = Integer.MAX_VALUE;

  /**
   * @param args
   * @throws CancelException
   * @throws IllegalArgumentException
   * @throws IOException
   */
  /*
  public static void main(String[] args) throws IllegalArgumentException, CancelException, IOException {
    try {
      Properties p = new Properties();
      p.putAll(WalaProperties.loadProperties());
    } catch (WalaException e) {
      e.printStackTrace();
      Assertions.UNREACHABLE();
    }

    runTestCase(TestConstants.JLEX_MAIN, TestConstants.JLEX, "JLex");
    // runTestCase(TestConstants.HELLO_MAIN, TestConstants.HELLO, "Hello");

  }

  public static void runTestCase(String mainClass, String scopeFile, String benchName) throws IllegalArgumentException,
      CancelException, IOException {
    System.err.println("=====BENCHMARK " + benchName + "=====");
    System.err.println("analyzing " + benchName);
    try {
      Pair<DemandRefinementPointsTo, PointerAnalysis> p = makeDemandPointerAnalysis(scopeFile, mainClass, benchName);
      DemandRefinementPointsTo dmp = p.fst;
      findFailingCasts(dmp.getBaseCallGraph(), p.snd, dmp);
    } catch (ClassHierarchyException e) {
      e.printStackTrace();
    }
    System.err.println("=*=*=*=*=*=*=*=*=*=*=*=*=*=*");
    System.err.println("");
    System.err.println("");
  }

  public static Pair<DemandRefinementPointsTo,PointerAnalysis> makeDemandPointerAnalysis(String scopeFile, String mainClass, String benchName)
      throws ClassHierarchyException, IllegalArgumentException, CancelException, IOException {
    AnalysisScope scope = CallGraphTestUtil.makeJ2SEAnalysisScope(scopeFile, getExclusions(benchName));
    // build a type hierarchy
    ClassHierarchy cha = ClassHierarchy.make(scope);

    // set up call graph construction options; mainly what should be considered
    // entrypoints?
    Iterable<Entrypoint> entrypoints = com.ibm.wala.ipa.callgraph.impl.Util.makeMainEntrypoints(scope, cha, mainClass);
    return makeDemandPointerAnalysis(scope, cha, entrypoints);
  }
  */
  
  public static Pair<DemandRefinementPointsTo,PointerAnalysis> makeDemandPointerAnalysis(AnalysisScope scope, ClassHierarchy cha, 
                                                     Iterable<Entrypoint> entrypoints, AnalysisOptions options, String exclusions)
        throws ClassHierarchyException, IllegalArgumentException, CancelException, IOException {
    exclusionsStr = exclusions;

    System.err.print("constructing call graph...");
    final Pair<CallGraph, PointerAnalysis> cgAndPA = buildCallGraph(scope, cha, options);
    CallGraph cg = cgAndPA.fst;    
    System.err.println("done");
    System.err.println(CallGraphStats.getStats(cg));
//    MemoryAccessMap fam = new SimpleMemoryAccessMap(cg, cgAndPA.snd.getHeapModel(), false);
    MemoryAccessMap fam = new PABasedMemoryAccessMap(cg, cgAndPA.snd);
    DemandRefinementPointsTo fullDemandPointsTo = DemandRefinementPointsTo.makeWithDefaultFlowGraph(cg, heapModel, fam, cha, options, makeStateMachineFactory());
    fullDemandPointsTo.setRefinementPolicyFactory(chooseRefinePolicyFactory(cha));
    return Pair.make(fullDemandPointsTo,cgAndPA.snd);
  }

  private static String exclusionsStr;
  private static String getExclusions(String benchName) {
    return exclusionsStr; //CallGraphTestUtil.REGRESSION_EXCLUSIONS;
  }

  // if true, construct up-front call graph cheaply (0-CFA)
  private static final boolean CHEAP_CG = false;

  private static HeapModel heapModel;

  /**
   * builds a call graph, and sets the corresponding heap model for analysis
   * 
   * @param scope
   * @param cha
   * @param options
   * @return
   * @throws CancelException
   * @throws IllegalArgumentException
   */
  private static Pair<CallGraph, PointerAnalysis> buildCallGraph(AnalysisScope scope, ClassHierarchy cha, AnalysisOptions options)
      throws IllegalArgumentException, CancelException {
    CallGraph retCG = null;
    PointerAnalysis retPA = null;
    final AnalysisCache cache = new AnalysisCache();
    CallGraphBuilder builder;
    if (CHEAP_CG) {
      builder = Util.makeZeroCFABuilder(options, cache, cha, scope);
      // we want vanilla 0-1 CFA, which has one abstract loc per allocation
      heapModel = Util.makeVanillaZeroOneCFABuilder(options, cache, cha, scope);
    } else {
      builder = Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);
      heapModel = (HeapModel) builder;
    }
    ProgressMaster master = ProgressMaster.make(new NullProgressMonitor(), 360000, false);
    //master.setMillisPerWorkItem(360000);
    master.beginTask("runSolver", 1);
    try {
      retCG = builder.makeCallGraph(options, master);
      retPA = builder.getPointerAnalysis();
    } catch (CallGraphBuilderCancelException e) {
      System.err.println("TIMED OUT!!");
      retCG = e.getPartialCallGraph();
      retPA = e.getPartialPointerAnalysis();
    }
    return Pair.make(retCG, retPA);
  }

  private static RefinementPolicyFactory chooseRefinePolicyFactory(ClassHierarchy cha) {
    if (true) {
      return new TunedRefinementPolicy.Factory(cha);
      //return new MyRefinementPolicy.Factory(cha);
    } else {
      return new ManualRefinementPolicy.Factory(cha);
    }
  }

  static class MyRefinementPolicy extends AbstractRefinementPolicy {
    
    private static final int DEFAULT_NUM_PASSES = 8;
    private static final int SHORTER_PASS_BUDGET = 2000;
    protected static final int LONGER_PASS_BUDGET = 24000;

    static int[] makeBudgetArr() {
      int[] tmp = new int[DEFAULT_NUM_PASSES];
      tmp[0] = SHORTER_PASS_BUDGET;
      Arrays.fill(tmp, 1, DEFAULT_NUM_PASSES, LONGER_PASS_BUDGET);
      return tmp;
    }
    
    public MyRefinementPolicy(IClassHierarchy cha) {
      super(new TunedFieldRefinementPolicy(cha), new AlwaysRefineCGPolicy(), DEFAULT_NUM_PASSES, makeBudgetArr());
    }
    
    public static class Factory implements RefinementPolicyFactory {

      private final IClassHierarchy cha;

      public Factory(IClassHierarchy cha) {
        this.cha = cha;
      }

      @Override
      public RefinementPolicy make() {
        return new MyRefinementPolicy(cha);
      }

    }
    
  }
  
  private static StateMachineFactory<IFlowLabel> makeStateMachineFactory() {
    return new ContextSensitiveStateMachine.Factory();
  }

  public static Map<MethodReference, Set<Integer>> findFailingCasts(CallGraph cg, PointerAnalysis pa, DemandRefinementPointsTo dmp) {
  //public static Set<Integer> findFailingCasts(CallGraph cg, PointerAnalysis pa, DemandRefinementPointsTo dmp) {
    final IClassHierarchy cha = dmp.getClassHierarchy();
    //List<Pair<CGNode, SSACheckCastInstruction>> failing = new ArrayList<Pair<CGNode, SSACheckCastInstruction>>();
    Map<MethodReference, Set<Integer>> failing = HashMapFactory.make();
    Set<Integer> failingSet = HashSetFactory.make();
    Set<Integer> noMoreRefinement = HashSetFactory.make();
    
    int numSafe = 0, numMightFail = 0, safeViaPointsTo = 0, count = 0;
    outer: for (Iterator<? extends CGNode> nodeIter = cg.iterator(); nodeIter.hasNext();) {
      CGNode node = nodeIter.next();
      MethodReference method = node.getMethod().getReference();
      TypeReference declaringClass = node.getMethod().getReference().getDeclaringClass();
      // skip library classes
      if (declaringClass.getClassLoader().equals(ClassLoaderReference.Primordial)) {
        continue;
      }
      IR ir = node.getIR();
      if (ir == null)
        continue;
      SSAInstruction[] instrs = ir.getInstructions();
      for (int i = 0; i < instrs.length; i++) {
        if (numSafe + numMightFail > MAX_CASTS)
          break outer;
        SSAInstruction instruction = instrs[i];
        if (instruction instanceof SSACheckCastInstruction) {
          SSACheckCastInstruction castInstr = (SSACheckCastInstruction) instruction;
          final TypeReference[] declaredResultTypes = castInstr.getDeclaredResultTypes();
     
          boolean primOnly = true;
          for (TypeReference t : declaredResultTypes) {
            if (! t.isPrimitiveType()) {
              primOnly = false;
            }
          }
          if (primOnly) {
            continue;
          }
          
          System.err.println("Checking cast #" + ++count + " " + castInstr + " in " + node.getMethod() + 
              ", line " + edu.colorado.thresher.core.Util.getSourceLineNumber(ir, i));
          //System.err.println("CHECKING " + castInstr +  " #" + ++count + " in " + node.getMethod());
          PointerKey castedPk = heapModel.getPointerKeyForLocal(node, castInstr.getUse(0));
          OrdinalSet<InstanceKey> pointsToSet = (OrdinalSet<InstanceKey>) pa.getPointsToSet(castedPk);
          
          Predicate<InstanceKey> castPred = new Predicate<InstanceKey>() {

            @Override
            public boolean test(InstanceKey ik) {
              TypeReference ikTypeRef = ik.getConcreteType().getReference();
              for (TypeReference t : declaredResultTypes) {
                IClass class1 = cha.lookupClass(t), class2 = cha.lookupClass(ikTypeRef);
                if (class1 == null || class2 == null) return true; // (unsoundly) punt
                //if (cha.isAssignableFrom(cha.lookupClass(t), cha.lookupClass(ikTypeRef))) {
                if (cha.isAssignableFrom(class1, class2)) {
                  return true;
                }
              }
              return false;
            }

          };
          //System.err.println("PTO SET: " + pointsToSet);
          Collection<InstanceKey> collection = OrdinalSet.toCollection(pointsToSet);
          if (com.ibm.wala.util.collections.Util.forAll(collection, castPred)) {
            System.err.println("SAFE VIA POINTER ANALYSIS: " + castInstr + " in " + node.getMethod());
            numSafe++;
            safeViaPointsTo++;
            continue;
          }
//          InstanceKey bogus = com.ibm.wala.util.collections.Util.find(collection, castPred.not());
//          Set<PointerStatement> statementsForPToEdge = edu.colorado.thresher.Util.getStatementsForPToEdge(castedPk, bogus, cg, pa, new AnalysisCache());
//          System.out.println(statementsForPToEdge);
          long startTime = System.currentTimeMillis();
          Pair<PointsToResult, Collection<InstanceKey>> queryResult = dmp.getPointsTo(castedPk, castPred);
          long runningTime = System.currentTimeMillis() - startTime;
          System.err.println("running time: " + runningTime + "ms");
          final FieldRefinePolicy fieldRefinePolicy = dmp.getRefinementPolicy().getFieldRefinePolicy();
          switch (queryResult.fst) {
            case SUCCESS:
              System.err.println("SAFE: " + castInstr + " in " + node.getMethod());
              if (fieldRefinePolicy instanceof ManualFieldPolicy) {
                ManualFieldPolicy hackedFieldPolicy = (ManualFieldPolicy) fieldRefinePolicy;
                System.err.println(hackedFieldPolicy.getHistory());
              }
              System.err.println("TRAVERSED " + dmp.getNumNodesTraversed() + " nodes");
              numSafe++;
              break;
            case NOMOREREFINE:
              if (queryResult.snd != null) {
                System.err.println("MIGHT FAIL: no more refinement possible for " + castInstr + " in " + node.getMethod());
                noMoreRefinement.add(count);
              } else {
                System.err.println("MIGHT FAILs: exceeded budget for " + castInstr + " in " + node.getMethod());
                System.err.println("skipping.");
              }
              addToFails(method, i, failing);
              failingSet.add(count);            
              numMightFail++;
              break;
            case BUDGETEXCEEDED:
              System.err.println("MIGHT FAIL: exceeded budget for " + castInstr + " in " + node.getMethod());
              System.err.println("skipping.");
              addToFails(method, i, failing);
              //failing.add(Pair.make(node.getMethod().getReference(), castInstr));
              failingSet.add(count); 
              numMightFail++;
              break;
            default:
              Assertions.UNREACHABLE();
            }
        }
      }
      // break outer;
    }
    System.err.println("TOTAL SAFE: " + numSafe);
    System.err.println("TOTAL SAFE VIA POINTS-TO: " + safeViaPointsTo);    
    System.err.println("TOTAL MIGHT FAIL: " + numMightFail);
    //System.err.println("TOTAL NO MORE REFINEMENT: " + failingSet.size());
    System.err.println("TOTAL NO MORE REFINEMENT: " + noMoreRefinement.size());
    //return failingSet;
    return failing;
  }
  
  private static void addToFails(MethodReference method, Integer cast, Map<MethodReference, Set<Integer>> failing) {
    Set<Integer> fails = failing.get(method);
    if (fails == null) {
      fails = HashSetFactory.make();
      failing.put(method, fails);
    }
    fails.add(cast);
  }
  
}

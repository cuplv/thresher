package edu.colorado.thresher;

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.Collection;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import z3.java.Z3AST;
import z3.java.Z3Context;
import z3.java.Z3Sort;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.propagation.AllocationSite;
import com.ibm.wala.ipa.callgraph.propagation.AllocationSiteInNode;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.ConcreteTypeKey;
import com.ibm.wala.ipa.callgraph.propagation.ConstantKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.NormalAllocationInNode;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.ReturnValueKey;
import com.ibm.wala.ipa.callgraph.propagation.SmushedAllocationSiteInNode;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ExceptionReturnValueKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ipa.modref.ArrayLengthKey;
import com.ibm.wala.shrikeBT.BinaryOpInstruction;
import com.ibm.wala.shrikeBT.ConditionalBranchInstruction;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.intset.BitVectorIntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.viz.DotUtil;
import com.ibm.wala.viz.PDFViewUtil;

public class Util {

  public static boolean LOG = Options.LOG;
  public static boolean DEBUG = Options.DEBUG;
  public static boolean PRINT = Options.PRINT;

  public static TypeReference EXCEPTION_TYPE = TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/lang/Exception");
  
  public static Map<String, Integer> varIds = HashMapFactory.make();
  private static int varIdCounter = 0;
  public static Map<String, Integer> fieldIds = HashMapFactory.make();
  private static int fieldIdCounter = 0;
  public static Map<String, Integer> typeIds = HashMapFactory.make();
  private static int typeIdCounter = 0;

  private static int tmpCounter = 0;

  private static int pathCounter = 0;

  public static void Log(String s) {
    if (LOG)
      System.err.println(s);
  }

  public static void Debug(Object s) {
    if (Options.DEBUG)
      System.out.println(s);
  }

  public static void Print(Object s) {
    // if (PRINT) System.out.println(s);
    System.out.println(s);
  }
  
  /*
  public static void Print(String s) {
    // if (PRINT) System.out.println(s);
    System.out.println(s);
  }
  */

  public static void clear() {
    varIds.clear();
    fieldIds.clear();
    typeIds.clear();
    varIdCounter = 0;
    fieldIdCounter = 0;
    typeIdCounter = 0;
  }

  public static String newTmpVar() {
    return (tmpCounter++) + "_tmp";
  }

  /*
   * public static void clearAssumptions() { assumptions.clear();
   * assumptionVars.clear(); }
   */

  public static int newPathNum() {
    return pathCounter++;
  }

  public static int getIdForVar(String varName) {
    // MEGA HACK - but easier than refactoring whole program
    varName = varName.replace("synthetic ", "");
    varName = varName.replace("Primordial", "");
    varName = varName.replace("Application", "");

    Util.Assert(!varName.contains("synthetic"), "evil synthetic var " + varName);
    Integer id = varIds.get(varName);
    if (id == null) {
      varIds.put(varName, ++varIdCounter);
      // System.err.println("ADDING " + varName + "; id " + varIdCounter);
      return varIdCounter;
    }
    return id;
  }

  public static int getIdForField(String fieldName) {
    Util.Assert(!fieldName.contains("synthetic"), "evil synthetic var " + fieldName);
    Integer id = fieldIds.get(fieldName);
    if (id == null) {
      fieldIds.put(fieldName, ++fieldIdCounter);
      return fieldIdCounter;
    }
    return id;
  }

  public static int getIdForType(String typeName) {
    if (typeName.contains("synthetic")) {
      typeName = typeName.replace("synthetic ", "");
    }
    Util.Assert(!typeName.contains("synthetic"), "evil synthetic var " + typeName);
    Integer id = typeIds.get(typeName);
    if (id == null) {
      // System.err.println("NOT FOUND!");
      typeIds.put(typeName, ++typeIdCounter);
      return typeIdCounter;
    }
    // System.err.println("found");
    return id;
  }

  public static DependencyRule makeUnconditionalDependencyRule(SSAInstruction instr, Object lhs, Object rhs,
      PointerStatement.EdgeType type, int lineId, int lineNum, CGNode node) {
    PointerVariable lhsPointer = makePointerVariable(lhs);
    PointerVariable rhsPointer = makePointerVariable(rhs);
    if (lhsPointer != null & rhsPointer != null) {
      PointerStatement stmt = makePointerStatement(instr, lhsPointer, rhsPointer, type, null, lineId, lineNum);
      PointsToEdge edge = new PointsToEdge(lhsPointer, rhsPointer);
      return new DependencyRule(edge, stmt, new TreeSet<PointsToEdge>(), node, (SSACFG.BasicBlock) node.getIR()
          .getBasicBlockForInstruction(instr));
    }
    return null;
  }

  public static PointerStatement makePointerStatement(SSAInstruction instr, PointerVariable lhs, PointerVariable rhs,
      PointerStatement.EdgeType type, String fieldString, int lineId, int lineNum) {
    // assign edges should never be given a field name, since there is none
    assert type != PointerStatement.EdgeType.Assign || fieldString == null;
    return new PointerStatement(instr, lhs, rhs, type, fieldString, lineId, lineNum);
  }

  public static PointerVariable makeSymbolicPointerVariable(Object key) {
    Util.Unimp("symbolic pointer variables");
    return makePointerVariableImpl(key);
  }

  /**
   * insta
   * 
   * @param key
   * @param nodeNum
   * @return
   */
  public static PointerVariable makePointerVariable(Object key) {
    return makePointerVariableImpl(key);
  }

  /**
   * gives all dependency rules generated both directly by a call and
   * transitively by its callees
   * 
   * @param call
   *          - the base call from which to generate rules
   * @return - set of dependency rules that give all rules generated by call and
   *         its callees
   */
  public static Set<DependencyRule> getRulesProducableByCall(CGNode call, CallGraph cg,
      AbstractDependencyRuleGenerator depRuleGenerator) {
    Util.Unimp("don't call this");
    return depRuleGenerator.getRulesForNodeAndCallees(call);
    /*
     * Set<CGNode> toExplore = new HashSet<CGNode>(), explored = new
     * HashSet<CGNode>(); Set<DependencyRule> rules = new
     * TreeSet<DependencyRule>(); toExplore.add(call); while
     * (!toExplore.isEmpty()) { call = toExplore.iterator().next();
     * explored.add(call); toExplore.remove(call);
     * depRuleGenerator.generateRulesForNode(call); Set<DependencyRule>
     * rulesForCall = depRuleGenerator.getRulesForNode(call); if (rulesForCall
     * != null) rules.addAll(rulesForCall); else Util.Debug("no rules for node "
     * + call); Iterator<CallSiteReference> sites = call.iterateCallSites();
     * while (sites.hasNext()) { CallSiteReference site = sites.next();
     * Set<CGNode> targets = cg.getPossibleTargets(call, site); for (CGNode
     * target : targets) { if (!explored.contains(target))
     * toExplore.add(target); } } } return rules;
     */
  }

  /**
   * does an instruction in ir write key locally (not via a callee)?
   * 
   * @param ir
   * @return
   */
  public static boolean writesKeyLocally(CGNode node, PointerKey key, HeapModel hm, HeapGraph hg, ClassHierarchy cha) {
    if (key instanceof InstanceFieldKey) return writesKeyLocally(node, ((InstanceFieldKey) key).getField(), hm, cha);
    else if (key instanceof StaticFieldKey) return writesKeyLocally(node, ((StaticFieldKey) key).getField(), hm, cha);
    else if (key instanceof ArrayContentsKey) return writesKeyLocally(node, ((ArrayContentsKey) key), hm, hg, cha);
    // TODO: do we need to do something smarter for array length?
    else if (key instanceof ArrayLengthKey) return false; // nothing modifies an array length other than the array constructor
    Util.Assert(false, "bad pointer key type " + key.getClass() + " " + key);
    return false;
  }

  private static boolean writesKeyLocally(CGNode node, IField fld, HeapModel hm, ClassHierarchy cha) {
    Util.Pre(fld != null);
    SSAInstruction[] instrs = node.getIR().getInstructions();
    for (int i = 0; i < instrs.length; i++) {
      SSAInstruction instr = instrs[i];
      if (instr instanceof SSAPutInstruction) {
        SSAPutInstruction put = (SSAPutInstruction) instr;
        FieldReference f = put.getDeclaredField();
        IField field = cha.resolveField(f);
        if (field != null && field.equals(fld)) return true;
      }
    }
    return false;
  }

  public static <T> Set<T> iteratorToSet(Iterator<T> iter) {
    Set<T> set = HashSetFactory.make();
    while (iter.hasNext()) {
      set.add(iter.next());
    }
    return set;
  }

  public static <T> Collection<T> iteratorToCollection(Iterator<T> iter) {
    List<T> list = new LinkedList<T>();
    while (iter.hasNext())
      list.add(iter.next());
    return list;
  }

  private static boolean writesKeyLocally(CGNode node, ArrayContentsKey key, HeapModel hm, HeapGraph hg, ClassHierarchy cha) {
    Util.Debug("getting predecessor heap nodes for " + key);
    Set<Object> preds = iteratorToSet(hg.getPredNodes(key)); // get array
                                                             // references that
                                                             // point at this
                                                             // ArrayContentsKey
    IR ir = node.getIR();
    SSAInstruction[] instrs = ir.getInstructions();
    for (int i = 0; i < instrs.length; i++) {
      SSAInstruction instr = instrs[i];
      if (instr instanceof SSAArrayStoreInstruction) {
        SSAArrayStoreInstruction store = (SSAArrayStoreInstruction) instr;
        PointerKey lpk = hm.getPointerKeyForLocal(node, store.getArrayRef());
        // get array references pointed to by this local
        Iterator<Object> succs = hg.getSuccNodes(lpk);
        while (succs.hasNext()) {
          // if the ArrayContentsKey and refs pointed to by the local match, we
          // have a possible write
          if (preds.contains(succs.next()))
            return true;
        }
        // IntSet succs = hg.getSuccNodeNumbers(lpk);
        // if (!succs.intersection(preds).isEmpty()) return true;
        return true;
      }
    }
    return false;
  }

  public static Set<DependencyRule> getProducersForEdge(PointsToEdge edge, AbstractDependencyRuleGenerator depRuleGenerator) {
    HeapGraph hg = depRuleGenerator.getHeapGraph();
    final int ANY_LINE_ID = 0;
    Set<DependencyRule> rules = new TreeSet<DependencyRule>();
    Util.Debug("getting rules relevant to " + edge);
    Object src = edge.getSource().getInstanceKey();
    Object snk = edge.getSink().getInstanceKey();
    Util.Debug("finding methods where " + src + "\n->" + edge.getField()+ "\n" + snk + " can be produced");
    Util.Assert(src != null, "expected instance key for " + edge.getSource());
    // snk can be symbolic
    //Util.Assert(snk != null, "expected instance key for " + edge.getSink());
    /*
     * if (snk == null) { // TODO: support this // trying to witness something
     * pointing to a constant... return empty rule set for now return rules;
     * //Util.Assert(snk instanceof ConstantKey, "should be a constant!"); }
     */
    boolean array = false;
    FieldReference edgeField = null;
    if (edge.getField() instanceof InstanceFieldKey) {
      InstanceFieldKey ifk = (InstanceFieldKey) edge.getField();
      edgeField = ifk.getField().getReference();
    } else if (edge.getField() instanceof ArrayContentsKey)
      array = true;
    else
      Util.Assert(edge.getField() == null || edge.getField() instanceof StaticFieldKey, "odd field " + edge.getField());
    boolean staticField = edgeField == null && !array;

    if (src instanceof LocalPointerKey) { // this edge has a local LHS
      LocalPointerKey lpk = (LocalPointerKey) src;
      CGNode node = lpk.getNode();
      IR ir = node.getIR();
      SSAInstruction[] instrs = ir.getInstructions();
      int i = 0;
      for (i = 0; i < instrs.length; i++) {
        SSAInstruction instr = instrs[i];
        if (instr != null && instr.hasDef() && instr.getDef() == lpk.getValueNumber()) {
          // this is the statement that produces our edge
          Set<DependencyRule> instrRules = depRuleGenerator.visit(instr, node, ANY_LINE_ID, i, ir);
          for (DependencyRule rule : instrRules) {
            if (rule.getShown().equals(edge))
              rules.add(rule); // this rule produces our edge
          }
          // because of SSA, this must be the only statement that
          // produces our edge
          return rules;
        }
      }
      if (rules.isEmpty()) { // it's possible that the edge is produced by a
                             // phi, which aren't in the regular instruction
                             // array
        Iterator<? extends SSAInstruction> phiIter = ir.iteratePhis();
        while (phiIter.hasNext()) {
          SSAPhiInstruction phi = (SSAPhiInstruction) phiIter.next();
          if (phi.getDef() == lpk.getValueNumber()) {
            // this is the statement that produces our edge
            Set<DependencyRule> instrRules = depRuleGenerator.visit(phi, node, ANY_LINE_ID, i, ir);
            for (DependencyRule rule : instrRules) {
              if (rule.getShown().equals(edge))
                rules.add(rule); // this rule produces our edge
            }
            break; // because of SSA, this must be the only statement that produces our edge
          }
        }
      }
    } else { // this edge has a heap LHS
      Set<CGNode> srcMethods = HashSetFactory.make(), snkMethods = HashSetFactory.make();
      // sets to keep track of value nums of local pointers. these are
      // overapproximate because they don't contain any information about
      // methods they belong to, but it doesn't seem worth it to save that
      // information
      MutableIntSet srcNums = new BitVectorIntSet(), snkNums = new BitVectorIntSet();
      boolean staticSrc = src instanceof StaticFieldKey;
      if (!staticSrc) {
        Iterator<Object> iter0 = hg.getPredNodes(src);
        while (iter0.hasNext()) { // find locals that point at the src, since we
                                  // must write to it through some local ptr
          Object next = iter0.next();
          // Util.Debug("next is " + next);
          if (next instanceof LocalPointerKey) {
            LocalPointerKey lpk = (LocalPointerKey) next;
            srcMethods.add(lpk.getNode());
            srcNums.add(lpk.getValueNumber());
          }
        }
      }

      if (snk != null) { // snk is an ordinary, concrete variable
        Iterator<Object> iter1 = hg.getPredNodes(snk);
        while (iter1.hasNext()) { 
          // find locals that point at the snk, since we need a local ptr to write it to snk 
          Object next = iter1.next();
          if (next instanceof LocalPointerKey) {
            LocalPointerKey lpk = (LocalPointerKey) next;
            snkMethods.add(lpk.getNode());
            snkNums.add(lpk.getValueNumber());
          }
        }
      } else { // snk is a symbolic variable
        Util.Assert(edge.getSink() instanceof SymbolicPointerVariable);
        SymbolicPointerVariable sink = (SymbolicPointerVariable) edge.getSink();
        for (InstanceKey key : sink.getPossibleValues()) {
          Iterator<Object> iter1 = hg.getPredNodes(key);
          while (iter1.hasNext()) { // find locals that point at the snk, since we
                                    // need a local ptr to write it to snk
            Object next = iter1.next();
            if (next instanceof LocalPointerKey) {
              LocalPointerKey lpk = (LocalPointerKey) next;
              snkMethods.add(lpk.getNode());
              snkNums.add(lpk.getValueNumber());
            }
          }
        }
      }
      if (!srcMethods.isEmpty()) snkMethods.retainAll(srcMethods);
      srcMethods = null;
      // now, snkMethods contains all methods which could possibly produce our edge

      if (staticField) {
        // we're looking for a write to a static field
        Util.Assert(staticSrc, "all non-static heap pointers must have field names! " + edge + " is bad.");
        StaticFieldKey key = (StaticFieldKey) src;
        for (CGNode node : snkMethods) {
          IR ir = node.getIR();
          if (ir == null)
            continue;
          SSAInstruction[] instrs = ir.getInstructions();
          int i = 0;
          for (i = 0; i < instrs.length; i++) {
            SSAInstruction instr = instrs[i];
            if (instr instanceof SSAPutInstruction) {
              SSAPutInstruction put = (SSAPutInstruction) instr;
              if (put.isStatic() && snkNums.contains(put.getUse(0)) && put.getDeclaredField().equals(key.getField().getReference())) {
                // src/snk nums and fields match; may produce our edge
                Set<DependencyRule> instrRules = depRuleGenerator.visit(put, node, ANY_LINE_ID, i, ir);
                for (DependencyRule rule : instrRules) {
                  if (rule.getShown().equals(edge))
                    rules.add(rule); // this rule produces our edge
                }
              }
            }
          }
        }
      } else if (array) {
        // we're looking for an array write
        for (CGNode node : snkMethods) {
          IR ir = node.getIR();
          if (ir == null) continue;
          SSAInstruction[] instrs = ir.getInstructions();
          int i = 0;
          for (i = 0; i < instrs.length; i++) {
            SSAInstruction instr = instrs[i];
            if (instr instanceof SSAArrayStoreInstruction) {
              SSAArrayStoreInstruction arr = (SSAArrayStoreInstruction) instr;
              if (srcNums.contains(arr.getUse(0)) && snkNums.contains(arr.getUse(2))) {
                // src/snk nums match; may produce our edge
                Set<DependencyRule> instrRules = depRuleGenerator.visit(arr, node, ANY_LINE_ID, i, ir);
                for (DependencyRule rule : instrRules) {
                  if (rule.getShown().equals(edge))
                    rules.add(rule); // this rule produces our edge
                }
              }
            }
          }
        }
      } else {
        // we're looking for an ordinary field write
        for (CGNode node : snkMethods) {
          IR ir = node.getIR();
          if (ir == null) continue;
          SSAInstruction[] instrs = ir.getInstructions();
          int i = 0;
          for (i = 0; i < instrs.length; i++) {
            SSAInstruction instr = instrs[i];
            if (instr instanceof SSAPutInstruction) {
              SSAPutInstruction put = (SSAPutInstruction) instr;
              if (srcNums.contains(put.getUse(0)) && snkNums.contains(put.getUse(1))
                  && edgeField.getName().equals(put.getDeclaredField().getName())) {

                // src/snk nums and fields match; may produce our edge
                Set<DependencyRule> instrRules = depRuleGenerator.visit(put, node, ANY_LINE_ID, i, ir);
                for (DependencyRule rule : instrRules) {
                  //if (rule.getShown().equals(edge))
                  if (rule.getShown().symbEq(edge))
                    rules.add(rule); // this rule possibly produces our edge
                }
              }
            }
          }
        }
      }
    }
    // Util.Assert(!rules.isEmpty(), "could not find rule producing " + edge);
    return rules;
  }

  public static Set<CGNode> getPotentialProducersForEdgeAndGenerateRules(PointsToEdge edge, HeapGraph hg,
      AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("don't call this");
    Util.Debug("getting rules relevant to " + edge);
    Set<CGNode> srcMethods = HashSetFactory.make();
    Object src = edge.getSource().getInstanceKey();
    Object snk = edge.getSink().getInstanceKey();

    Set<CGNode> snkMethods = HashSetFactory.make();
    if (edge.getSource().toString().contains("fakeRootMethod"))
      srcMethods.add(cg.getFakeRootNode());
    if (edge.getSink().toString().contains("fakeRootMethod"))
      snkMethods.add(cg.getFakeRootNode());
    // Util.Unimp("not sure what's going on here...should probably just return a trivial witness");

    // Util.Debug("finding methods where " + src + "\n->\n" + snk +
    // " can be produced");
    Util.Assert(src != null, "expected instance key for " + edge.getSource());
    Util.Assert(snk != null, "expected instance key for " + edge.getSink());

    if (src instanceof LocalPointerKey) {
      LocalPointerKey lpk = (LocalPointerKey) src;
      srcMethods.add(lpk.getNode());
      if (lpk.isParameter()) {
        // add the callers of this node as well
        Iterator<CGNode> callers = cg.getPredNodes(lpk.getNode());
        while (callers.hasNext())
          srcMethods.add(callers.next());
      }
    } else {
      Iterator<Object> iter0 = hg.getPredNodes(src);
      while (iter0.hasNext()) {
        Object next = iter0.next();
        if (next instanceof LocalPointerKey) {
          LocalPointerKey lpk = (LocalPointerKey) next;
          // add method containing this local variable
          srcMethods.add(lpk.getNode());
        }
      }
    }
    // we don't have to worry about snk being a local pointer key
    Iterator<Object> iter1 = hg.getPredNodes(snk);
    while (iter1.hasNext()) {
      Object next = iter1.next();
      if (next instanceof LocalPointerKey) {
        LocalPointerKey lpk = (LocalPointerKey) next;
        // find method containing this local variable
        snkMethods.add(lpk.getNode());
      }
    }
    // compute intersection of methods containing src and methods containing snk
    // Util.Debug("there are " + snkMethods.size() + " sink methods");
    // Util.Assert(!srcMethods.isEmpty(), "can't find any methods for " + src);
    if (!srcMethods.isEmpty())
      snkMethods.retainAll(srcMethods);
    // snkMethods.retainAll(srcMethods);
    Util.Debug("combined, there are " + snkMethods.size() + " methods");
    Util.Assert(snkMethods.size() != 0, "Can't have size 0 here!");

    int nodeCounter = 0;
    // generate dependency rules for each of these methods
    for (CGNode node : snkMethods) {
      depRuleGenerator.generateRulesForNode(node);
      Util.Debug("finished with " + (++nodeCounter) + " of " + snkMethods.size());
      // if (DEBUG) System.err.println("generated rules for node " + count +
      // " of " + snkMethods.size() + "; have " + aDepRuleGenerator.numRules() +
      // " rules");
    }
    return snkMethods;
  }

  public static List<CGNode> getMethodsProducingEdge(PointsToEdge edge, HeapGraph hg,
      AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Set<CGNode> sharedMethods = getPotentialProducersForEdgeAndGenerateRules(edge, hg, depRuleGenerator, cg);
    List<CGNode> producers = new LinkedList<CGNode>();

    for (CGNode node : sharedMethods) {
      Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(node);
      if (rules != null) {
        for (DependencyRule rule : rules) {
          if (rule.getShown().equals(edge)) {
            producers.add(node);
          }
        }
      }
    }
    return producers;
  }

  /**
   * @param edge
   *          - edge to be produced
   * @return all dependency rules that could possibly produce that edge
   */
  public static Set<DependencyRule> getRulesProducingEdge(PointsToEdge edge,
      AbstractDependencyRuleGenerator depRuleGenerator) {
    Util.Unimp("don't call this");
    HeapGraph hg = depRuleGenerator.getHeapGraph();
    CallGraph cg = depRuleGenerator.getCallGraph();
    Set<CGNode> sharedMethods = getPotentialProducersForEdgeAndGenerateRules(edge, hg, depRuleGenerator, cg);
    Set<DependencyRule> producers = new TreeSet<DependencyRule>();

    for (CGNode node : sharedMethods) {
      // Util.Debug("checking rules for node " + node);
      Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(node);
      if (rules != null) {
        for (DependencyRule rule : rules) {
          // Util.Debug("RULE: " + rule);
          if (rule.getShown().equals(edge)) {
            producers.add(rule);
          }
        }
      }
    }
    return producers;
  }

  /**
   * 
   * @param edge
   *          - the edge to be checked for produceability in loop
   * @param loopHead
   *          - head of the loop we are looking at
   * @param node
   *          - CGNode containing the loop we are currently in
   * @return set of dependency rules in loop that can produce edge. these
   *         dependency rules are modified so *only* their non-loop
   *         preconditions are retained
   */
  public static List<DependencyRule> getLoopProducersForEdge(PointsToEdge edge, SSACFG.BasicBlock loopHead, CGNode node,
      HeapGraph hg, AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("don't call this");
    Set<DependencyRule> loopRules = getRulesForLoop(loopHead, node, depRuleGenerator, cg);

    List<DependencyRule> rulesProducingEdge = new LinkedList<DependencyRule>();
    for (DependencyRule rule : loopRules) {
      if (!rule.getShown().equals(edge))
        continue; // this rule does not produce our edge
      SSACFG.BasicBlock ruleBlk = rule.getBlock();
      Util.Assert(ruleBlk != null, "no basic block for rule " + rule);
      if (WALACFGUtil.isInLoopBody(ruleBlk, loopHead, rule.getNode().getIR())) {
        TreeSet<PointsToEdge> toAdd = new TreeSet<PointsToEdge>();
        // boolean noRule = false;
        // TODO: need to do mini fixed-point computation here; keep adding
        // preconditions as long as at least one cannot be produced in the loop

        // see if preconditions are also produceable in the loop body. if they
        // are not, do not add them to our constraints
        for (PointsToEdge pre : rule.getToShow()) {
          if (!isEdgeProduceableByLoop(pre, loopHead, node, hg, depRuleGenerator, cg))
            toAdd.add(pre);
          else {
            Util.Debug("dropped node is " + pre.getSource().getNode());
            Util.Debug("current node is " + node);
            Util.Assert(pre.getSource().getNode().equals(node), "nodes " + pre.getSource().getNode() + " and " + node
                + " don't match");
            // noRule = true;
            // break;
            Util.Debug("dropping edge " + pre);
          }
        }
        // if (noRule) continue;
        Util.Debug("adding rule to produce " + rule.getShown());
        // make dummy rule that replaces edge with non-loop-produceable
        // preconditions
        DependencyRule dummy = new DependencyRule(rule.getShown(), rule.getStmt(), toAdd, rule.getNode(), rule.getBlock());
        boolean contained = false;
        List<DependencyRule> toRemove = new LinkedList<DependencyRule>();
        for (DependencyRule producer : rulesProducingEdge) {
          if (producer.equalExceptForStatement(dummy)) {// are dummy and this
                                                        // rule equivalent (same
                                                        // produced edge, same
                                                        // preconditions)?
            contained = true;
            break;
            // we also need to consider that the rules may shown the same fact,
            // but with different precondition sets
          } else if (producer.getShown().equals(dummy.getShown())) {
            // choose the less constrained precondition set
            if (producer.getToShow().size() < dummy.getToShow().size()) {
              contained = true;
              break;
            } else if (producer.getToShow().size() > dummy.getToShow().size()) {
              toRemove.add(producer);// Util.Unimp("removing producer!");
            }
          }
        }
        for (DependencyRule removeMe : toRemove)
          rulesProducingEdge.remove(removeMe);
        if (!contained)
          rulesProducingEdge.add(dummy);
      }
    }
    return rulesProducingEdge;
  }

  public static Set<DependencyRule> getRulesForLoop(SSACFG.BasicBlock loopHead, CGNode node,
      AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("don't call this");
    Set<DependencyRule> loopRules = new TreeSet<DependencyRule>();

    Set<DependencyRule> rules = depRuleGenerator.getRulesForNode(node); // add
                                                                        // normal
                                                                        // loop
                                                                        // rules
    for (DependencyRule rule : rules) {
      Util.Assert(rule.getBlock() != null, "no basic block for rule " + rule);
      if (WALACFGUtil.isInLoopBody(rule.getBlock(), loopHead, node.getIR())) {
        loopRules.add(rule);
      }
    }

    // get rules for calls in loop body
    Set<SSAInstruction> loopInstrs = WALACFGUtil.getInstructionsInLoop(loopHead, node.getIR());
    for (SSAInstruction instr : loopInstrs) {
      if (instr instanceof SSAInvokeInstruction) {
        Util.Unimp("found call " + instr + " in loop");
        SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
        Set<CGNode> callees = cg.getPossibleTargets(node, call.getCallSite());
        for (CGNode callNode : callees) {
          loopRules.addAll(Util.getRulesProducableByCall(callNode, cg, depRuleGenerator));
        }
      }
    }
    return loopRules;
  }

  /**
   * @param edge
   *          - the edge to be checked for produceability in loop
   * @return true if there are any rules in *any* loop in node that can produce
   *         edge; false otherwise
   */
  public static boolean isEdgeProduceableByLoop(PointsToEdge edge, CGNode node, HeapGraph hg,
      AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("needs to account for calls in loops");
    Set<DependencyRule> nodeRules = depRuleGenerator.getRulesForNode(node);
    for (DependencyRule rule : nodeRules) {
      if (!rule.getShown().equals(edge))
        continue; // this rule does not produce our edge
      SSACFG.BasicBlock ruleBlk = rule.getBlock();
      Util.Assert(ruleBlk != null, "no basic block for rule " + rule);
      if (WALACFGUtil.isInLoopBody(ruleBlk, rule.getNode().getIR()))
        return true;
    }
    return false;
  }

  /**
   * @param edge
   *          - the edge to be checked for produceability in loop
   * @param loopHead
   *          - head of the loop we are looking at
   * @return true if there are any rules in the loop headed by loopHead that can
   *         produce edge; false otherwise
   */
  public static boolean isEdgeProduceableByLoop(PointsToEdge edge, SSACFG.BasicBlock loopHead, CGNode node, HeapGraph hg,
      AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("don't call this");
    Set<DependencyRule> nodeRules = getRulesForLoop(loopHead, node, depRuleGenerator, cg);

    for (DependencyRule rule : nodeRules) {
      if (!rule.getShown().equals(edge))
        continue; // this rule does not produce our edge
      return true;
    }
    return false;
  }

  // wrapper
  public static List<TreeSet<PointsToEdge>> getNonLoopPreconditionsForEdge(PointsToEdge edge, SSACFG.BasicBlock loopHead,
      CGNode node, HeapGraph hg, AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("don't call this");
    Util.Debug("getting non-loop preconditions for " + edge);
    List<TreeSet<PointsToEdge>> pre = getNonLoopPreconditionsForEdge(edge, new TreeSet<PointsToEdge>(), loopHead, node, hg,
        depRuleGenerator, cg);
    Util.Debug("Done getting preconditions; have " + pre.size());
    Util.Post(!pre.isEmpty(), "this should never be empty...should at least contain an empty list");
    return pre;
    // return
  }

  /**
   * @param edge
   *          - the edge to be checked for produceability in loop
   * @param loopHead
   *          - head of the loop we are looking at
   * @return the set of preconditions for producing this edge that are *not*
   *         contained in the loop
   */
  public static List<TreeSet<PointsToEdge>> getNonLoopPreconditionsForEdge(PointsToEdge edge, Set<PointsToEdge> seen,
      SSACFG.BasicBlock loopHead, CGNode node, HeapGraph hg, AbstractDependencyRuleGenerator depRuleGenerator, CallGraph cg) {
    Util.Unimp("need to account for calls in the loop");
    Util.Debug("getting non-loop producers for " + edge);

    // TODO: DEBUG
    if (edge.getSource().isLocalVar())
      Util.Assert(edge.getSource().getNode().equals(node), "mismatch: Nodes " + node + " and " + edge.getSource().getNode());

    Set<DependencyRule> nodeRules = depRuleGenerator.getRulesForNode(node);
    List<TreeSet<PointsToEdge>> preconditionChoices = new LinkedList<TreeSet<PointsToEdge>>();
    List<DependencyRule> loopProducers = new LinkedList<DependencyRule>();

    for (DependencyRule rule : nodeRules) {
      SSACFG.BasicBlock ruleBlk = rule.getBlock();
      Util.Assert(ruleBlk != null, "no basic block for rule " + rule);
      if (rule.getShown().equals(edge) && WALACFGUtil.isInLoopBody(ruleBlk, loopHead, rule.getNode().getIR())) {
        // keep only rules that produce our edge and are in the loop
        loopProducers.add(rule);
      }
    }

    if (loopProducers.isEmpty()) {
      TreeSet<PointsToEdge> preconditions = new TreeSet<PointsToEdge>();
      preconditions.add(edge);
      preconditionChoices.add(preconditions);
      Util.Debug("no loop producers for " + edge);
      return preconditionChoices;
    }
    // preconditions.remove(edge);
    for (DependencyRule rule : loopProducers) {
      Util.Debug("PRODUCER " + rule);
    }
    Util.Debug(loopProducers.size() + " loop producers");
    // Util.Assert(loopProducers.size() < 2, "too many loop producers " +
    // loopProducers.size());

    for (DependencyRule producer : loopProducers) {
      List<TreeSet<PointsToEdge>> caseSplits = new LinkedList<TreeSet<PointsToEdge>>();
      caseSplits.add(new TreeSet<PointsToEdge>()); // start off with no case
                                                   // splits
      for (PointsToEdge showMe : producer.getToShow()) {
        if (seen.add(showMe)) { // prevent infinite looping
          List<TreeSet<PointsToEdge>> choices = getNonLoopPreconditionsForEdge(showMe, seen, loopHead, node, hg, depRuleGenerator,
              cg);
          for (TreeSet<PointsToEdge> choice : choices) {
            for (TreeSet<PointsToEdge> split : caseSplits) {
              split.addAll(Util.deepCopyTreeSet(choice));
            }
          }
        }
      }
      preconditionChoices.addAll(caseSplits);
    }
    Util.Debug("printing lists");
    boolean emptyList = false;
    for (TreeSet<PointsToEdge> list : preconditionChoices) {
      if (list.isEmpty())
        emptyList = true;
      Util.Debug("LIST: ");
      for (PointsToEdge lEdge : list)
        Util.Debug("edge: " + lEdge);
    }
    Util.Debug("done printing lists");
    if (emptyList) {
      Util.Debug("found empty precondition set for " + edge);
      // an empty list means that the edge can be produced entirely in the loop
      // (i.e no non-loop preconditions;
      // if we can produce an edge with no preconditions, there's no sense in
      // considering ways to produce it which require preconditions
      List<TreeSet<PointsToEdge>> empty = new LinkedList<TreeSet<PointsToEdge>>();
      empty.add(new TreeSet<PointsToEdge>());
      return empty;
    }
    // Util.Unimp("this");

    return preconditionChoices;
  }

  private static PointerVariable makePointerVariableImpl(Object key) {
    Util.Pre(key != null, "can't make pointer variable from null key!");
    CGNode node = null;
    String pointerString = null;
    // StringBuilder pointerString = new StringBuilder();

    if (key instanceof PointerKey) {
      if (key instanceof LocalPointerKey) {
        LocalPointerKey lpk = (LocalPointerKey) key;
        node = lpk.getNode();
        int valueNum = lpk.getValueNumber();
        return new ConcretePointerVariable(key, node, valueNum);
      } else if (key instanceof ReturnValueKey && !(key instanceof ExceptionReturnValueKey)) {
        ReturnValueKey rvk = (ReturnValueKey) key;
        // String methodName = rvk.getNode().getMethod().getName().toString();
        node = rvk.getNode();
        String methodName = rvk.getNode().getMethod().toString();
        pointerString = methodName + " Retval";
        // typeId = getIdForType(pointerString);
        // if (symbolic) return new SymbolicPointerVariable(typeId);
        // else
        return new ConcretePointerVariable(rvk, node, -2);
      } else if (key instanceof ExceptionReturnValueKey) {
        /*
        ExceptionReturnValueKey erv = (ExceptionReturnValueKey) key;
        node = erv.getNode();
        return new ConcretePointerVariable(erv, node, -1);
        */
        return null; // purposely do not handle this case
      } else if (key instanceof StaticFieldKey) {
        StaticFieldKey sfk = (StaticFieldKey) key;
        IMethod classInit = sfk.getField().getDeclaringClass().getClassInitializer();
        // Util.Assert(classInit != null, "coudn)
        String fieldName = sfk.getField().getName().toString();
        String className = sfk.getField().getDeclaringClass().toString();
        pointerString = className + "." + fieldName;
        // typeId =
        // getIdForType(sfk.getField().getFieldTypeReference().toString());

        // if (symbolic) return new SymbolicPointerVariable(typeId);
        // else return new ConcretePointerVariable(key, method, -1,
        // pointerString, typeId);
        return new ConcretePointerVariable(sfk, classInit, pointerString);
        // else return new ConcretePointerVariable(pointerString, typeId);
        // return makeStaticFieldVar(sfk.getField().getReference());
      } else if (key instanceof ArrayContentsKey) {
        ArrayContentsKey ack = (ArrayContentsKey) key;
        return makePointerVariableImpl(ack.getInstanceKey());
      } else {
        Util.Assert(false, "UNIMPLEMENTED POINTER KEY " + key.getClass());
        pointerString = key.toString();
        return null;
      }
    } else if (key instanceof InstanceKey) {
      if (key instanceof AllocationSiteInNode) {
        AllocationSiteInNode as = (AllocationSiteInNode) key;
        node = as.getNode();
        return new ConcretePointerVariable((InstanceKey) key, node, -1);
      } else if (key instanceof NormalAllocationInNode) {
        NormalAllocationInNode nan = (NormalAllocationInNode) key;
        node = nan.getNode();
        return new ConcretePointerVariable((InstanceKey) key, node, -1);
      } else if (key instanceof AllocationSite) {
        AllocationSite site = (AllocationSite) key;
        pointerString = site.getMethod() + "-" + site.getSite().getDeclaredType().getName().toString() + "@"
            + site.getSite().getProgramCounter();
        return new ConcretePointerVariable(site, site.getMethod(), pointerString);
      } else if (key instanceof ConcreteTypeKey) {
        ConcreteTypeKey ctk = (ConcreteTypeKey) key;
        // purposely don't track exception literals
        if (ctk.getConcreteType().getReference() == EXCEPTION_TYPE) return null;
        pointerString = ctk.getType().toString();
        return new ConcretePointerVariable(key, pointerString);// typeId);
      } else if (key instanceof ConstantKey) {
        // TODO: need to implement LoadMetaDataInstruction to get this to work
        ConstantKey ck = (ConstantKey) key;
        IClass clazz = ck.getConcreteType();
        return new ConcretePointerVariable(ck, clazz + "_CONST");
      } else if (key instanceof SmushedAllocationSiteInNode) {
        SmushedAllocationSiteInNode smushed = (SmushedAllocationSiteInNode) key;
        return new ConcretePointerVariable(key, smushed.getNode(), smushed.getNode().getMethod() + "_SMUSHED ");// typeId);
      } else {
        Util.Assert(false, "UNIMPLEMENTED INSTANCE KEY! " + key);
        pointerString = "Unimplemented Instance Key";
        return null;
      }
    } else {
      Util.Assert(false, "Bad argument for makePointerVariable " + key + " ; expected PointerKey or InstanceKey. Exiting.");
      return null;
    }
    // else return new PointerVariable(pointerString, typeId);
  }
  
  public static boolean isExceptionType(InstanceKey key, IClassHierarchy cha) {
    if (key instanceof ConcreteTypeKey){
      ConcreteTypeKey ctk = (ConcreteTypeKey) key;
      // purposely don't track exception literals
      return ctk.getConcreteType().getReference() == Util.EXCEPTION_TYPE ||
          cha.computeSubClasses(EXCEPTION_TYPE).contains(key.getConcreteType());
    }
    return false;
  }

  public static CGNode getNodeForInstanceKey(InstanceKey key) {
    if (key instanceof AllocationSiteInNode)
      return ((AllocationSiteInNode) key).getNode();
    else if (key instanceof NormalAllocationInNode)
      return ((NormalAllocationInNode) key).getNode();
    else if (key instanceof SmushedAllocationSiteInNode)
      return ((SmushedAllocationSiteInNode) key).getNode();
    else {
      Util.Assert(false, "UNIMPLEMENTED INSTANCE KEY! " + key);
      return null;
    }
  }

  public static int getSourceLineNumber(IR ir, int instrNum) {
    int lineNum = -1;
    try {
      IBytecodeMethod method = (IBytecodeMethod) ir.getMethod();
      int bytecodeIndex = method.getBytecodeIndex(instrNum);
      lineNum = method.getLineNumber(bytecodeIndex);
    } catch (Exception e) {
      System.err.println("Error mapping bytecode line num to source line num");
    }
    return lineNum;
  }

  public static void Pre(boolean assertion) {
    Pre(assertion, "failed precondition");
  }

  public static void Pre(boolean assertion, String msg) {
    if (!assertion) {
      Util.Print("FAILED PRECONDITION: " + msg);
      Util.Debug("FAILED PRECONDITION: " + msg);
      // Thread.dumpStack();
      throw new NullPointerException();
      // System.exit(1);
    }
  }

  public static void Post(boolean assertion) {
    Post(assertion, "");
  }

  public static void Post(boolean assertion, String msg) {
    if (!assertion) {
      Util.Print("FAILED POSTCONDITION: " + msg);
      Util.Debug("FAILED POSTCONDITION: " + msg);
      // Thread.dumpStack();
      // System.exit(1);
      throw new NullPointerException();
    }
  }

  public static void Assert(boolean assertion) {
    Assert(assertion, "failed assertion");
  }

  public static void Assert(boolean assertion, String msg) {
    if (!assertion) {
      Util.Print("FAILED ASSERTION: " + msg);
      //Util.Debug("FAILED ASSERTION: " + msg);
      // Thread.dumpStack();
      // System.exit(1);
      throw new NullPointerException();
    }
  }

  public static void Unimp(String msg) {
    Util.Assert(false, "UNIMPLEMENTED: " + msg);
  }

  public static String constraintSetToString(Set<PointsToEdge> constraints) {
    String edgeSet = "";
    boolean firstPass = true;
    for (PointsToEdge edge : constraints) {
      if (firstPass) {
        edgeSet += edge.toString();
        firstPass = false;
      } else
        edgeSet += " *\n" + edge.toString();
    }
    return "{" + edgeSet + "}";
  }

  private static Z3AST makeUnboundAssumptionForVar(String varName, Z3Context ctx) {
    String boundVar = varName + "_unbound";
    // System.err.println("adding assumption ~" + boundVar);
    // return makeNegatedPropositionalVar(boundVar, ctx);
    return makePropositionalVar(boundVar, ctx);
  }

  public static Z3AST makeSymbolicRule(Z3Context ctx, int lhs0, String lhs1, int fieldName0, String fieldName1, String rhs0,
      String rhs1, int rhsType0, String rhsType1, String concreteName, String constraintId) {
    Z3Sort intSort = ctx.mkIntSort();

    // System.err.println("setting " + rhsType1 + " == " + rhsType0);
    // System.err.println("LHS IS " + lhs1);
    // System.err.println("RHS IS " + lhs1);

    // String boundVar = rhs0 + "_bound";
    // create a propositional variable to represent whether or not variable is
    // bound (starts unbound)
    Z3AST unbound = makeUnboundAssumptionForVar(rhs0, ctx);
    // makeNegatedPropositionalVar(boundVar, ctx);
    // ctx.mkConst(ctx.mkStringSymbol(boundVar), ctx.mkBoolSort());
    // System.err.println("ADDING ASSUMPION ~" + rhs0);
    // assumptions.put(constraintIndex, rhs0);
    // assumptionVars.put(constraintIndex, concreteName);
    // symbolicRules.add(constraintIndex);

    Z3AST symbTypesEq = ctx.mkEq(ctx.mkInt(rhsType0, intSort), ctx.mkConst(ctx.mkStringSymbol(rhsType1), intSort));
    // Z3AST symbPartEq = ctx.mkOr(ctx.mkNot(bound),
    // unbound => symbPartEq
    Z3AST symbPartEq = ctx.mkOr(unbound,
        ctx.mkEq(ctx.mkConst(ctx.mkStringSymbol(rhs0), intSort), ctx.mkConst(ctx.mkStringSymbol(rhs1), intSort)));
    // Z3AST symbPartEq =
    // ctx.mkEq(ctx.mkConst(ctx.mkStringSymbol(rhs0), intSort),
    // ctx.mkConst(ctx.mkStringSymbol(rhs1), intSort));

    Z3AST fieldNameEq = ctx.mkEq(ctx.mkInt(fieldName0, intSort), ctx.mkConst(ctx.mkStringSymbol(fieldName1), intSort));
    Z3AST nonSymbPartEq = ctx.mkEq(ctx.mkInt(lhs0, intSort), ctx.mkConst(ctx.mkStringSymbol(lhs1), intSort));

    return ctx.mkNot(ctx.mkAnd(symbTypesEq, symbPartEq, fieldNameEq, ctx.mkNot(nonSymbPartEq)));
  }

  // TODO: some redundancy here now that we check for LHS matches; clean up
  public static Z3AST makeStrongUpdateRule(Z3Context ctx, int lhs0, String lhs1, int fieldName0, String fieldName1, int rhs0,
      String rhs1) {
    Z3Sort intSort = ctx.mkIntSort();

    // System.err.println("Setting " + lhs1 + " == " + lhs0);
    // System.err.println("Setting " + fieldName1 + " == " + fieldName0);
    // System.err.println("Setting " + rhs1 + " == " + rhs0);

    // NOT (lhs's equal AND field names equal AND NOT rhs's equal)
    return ctx.mkNot(ctx.mkAnd(ctx.mkEq(ctx.mkInt(lhs0, intSort), ctx.mkConst(ctx.mkStringSymbol(lhs1), intSort)),
        ctx.mkEq(ctx.mkInt(fieldName0, intSort), ctx.mkConst(ctx.mkStringSymbol(fieldName1), intSort)),
        ctx.mkNot(ctx.mkEq(ctx.mkInt(rhs0, intSort), ctx.mkConst(ctx.mkStringSymbol(rhs1), intSort)))));

  }

  /*
   * public static String valueFromPointsToConstraints(String rhs, String
   * fieldName, Set<PointsToEdge> constraints) { for (PointsToEdge edge :
   * constraints) { if (edge.getSource().getName().equals(rhs)) { return
   * edge.getSink().getName(); } } return null; }
   * 
   * public static boolean constraintsContainLHS(String lhs, Set<PointsToEdge>
   * constraints) { for (PointsToEdge edge : constraints) { if
   * (edge.getSource().getName().equals(lhs)) return true; } return false; }
   */

  public static Set<String> deepCopyStringSet(Set<String> pathConstraints) {
    Set<String> newConstraints = HashSetFactory.make();
    for (String str : pathConstraints) {
      newConstraints.add(new String(str));
    }
    return newConstraints;
  }

  public static TreeSet<PointerVariable> deepCopyPointerVariableSet(Set<PointerVariable> toCopy) {
    TreeSet<PointerVariable> copy = new TreeSet<PointerVariable>();
    for (PointerVariable var : toCopy) {
      // pointer variables are immutable, so we don't need to deep copy them
      copy.add(var);
    }
    return copy;
  }

  // public static TreeSet<PointsToEdge>
  // deepCopyPointsToEdgeSet(TreeSet<PointsToEdge> edges) {
  public static Set<PointsToEdge> deepCopyPointsToEdgeSet(Set<PointsToEdge> edges) {
    Set<PointsToEdge> newEdges = HashSetFactory.make();
    for (PointsToEdge edge : edges) {
      // this is ok since the contents of the set are immutable
      newEdges.add(edge);
    }
    return newEdges;
  }

  public static <K, V> Map<K, V> copyMap(Map<K, V> map) {
    Map<K, V> newMap = HashMapFactory.make();
    for (K key : map.keySet()) {
      newMap.put(key, map.get(key));
    }
    return newMap;
  }

  public static <T> TreeSet<T> deepCopyTreeSet(TreeSet<T> set) {
    TreeSet<T> copy = new TreeSet<T>();
    Iterator<T> iter = set.iterator();
    while (iter.hasNext()) {
      copy.add(iter.next()); // this is ok since the contents of the set are
                             // immutable
    }
    return copy;
  }

  public static <T> Set<T> deepCopySet(Set<T> set) {
    Set<T> copy = HashSetFactory.make();
    Iterator<T> iter = set.iterator();
    while (iter.hasNext()) {
      copy.add(iter.next());
    }
    Util.Assert(set.size() == copy.size(), "we picked the wrong kind of set!");
    return copy;
  }

  public static <T> List<T> deepCopyList(List<T> list) {
    if (list == null) return null;
    List<T> copy = new LinkedList<T>();
    for (int i = 0; i < list.size(); i++) {
      copy.add(list.get(i));
    }
    return copy;
  }

  public static <T> LinkedList<T> deepCopyStackList(LinkedList<T> stackList) {
    LinkedList<T> newList = new LinkedList<T>();
    for (T type : stackList) {
      newList.addLast(type);
    }
    return newList;
  }

  public static String fieldNameFromPointerKey(PointerKey key) {
    if (key instanceof StaticFieldKey) {
      StaticFieldKey sfk = (StaticFieldKey) key;
      return sfk.getField().getName().toString();
    } else if (key instanceof InstanceFieldKey) {
      InstanceFieldKey ifk = (InstanceFieldKey) key;
      return ifk.getField().getName().toString();
    } else if (key instanceof ArrayContentsKey) {
      return "__ARRAY";
    } else {
      Util.Assert(false, "UNHANDLED POINTER KEY TYPE " + key);
      return null;
    }
  }

  public static Z3AST makeIntConst(int i, Z3Context ctx) {
    return ctx.mkInt(i, ctx.mkIntSort());
  }

  public static Z3AST makeIntVar(String name, Z3Context ctx) {
    return ctx.mkConst(ctx.mkStringSymbol(name), ctx.mkIntSort());
  }

  public static Z3AST makePropositionalVar(String name, Z3Context ctx) {
    return ctx.mkConst(ctx.mkStringSymbol(name), ctx.mkBoolSort());
  }

  /*
   * private static Z3AST makeNegatedPropositionalVar(String name, Z3Context
   * ctx) { return ctx.mkNot(makePropositionalVar(name, ctx)); }
   */

  public static Z3AST makeFreshPropositionalVar(Z3Context ctx) {
    return makePropositionalVar(newTmpVar(), ctx);
  }

  // public static String makeLocalVarName(MethodReference method, int localNum)
  // {
  public static String makeLocalVarName(CGNode node, int localNum) {
    String varName = node.toString();
    // MEGA HACK!
    if (varName.contains("synthetic")) {
      varName = varName.replace("synthetic ", "");
    }

    Util.Assert(!varName.contains("synthetic"), "evil synthetic var name " + varName);
    return varName + "-v" + localNum;
    // return method.toString() + "-v" + localNum;
  }

  public static boolean isBinOpCommutative(BinaryOpInstruction.Operator binOp) {
    boolean commutative = false;
    switch (binOp) {
      case ADD:
        commutative = true;
        break;
      case SUB:
        break;
      case MUL:
        commutative = true;
        break;
      case DIV:
        break;
      case AND:
        commutative = true;
        break;
      case OR:
        commutative = true;
        break;
      case XOR:
        commutative = true;
        break;
      case REM:
        break;
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return commutative;
  }

  public static BinaryOpInstruction.Operator reverseBinOperator(BinaryOpInstruction.Operator binOp) {
    switch (binOp) {
      case ADD:
        return BinaryOpInstruction.Operator.SUB;
      case SUB:
        return BinaryOpInstruction.Operator.ADD;
      case MUL:
        return BinaryOpInstruction.Operator.DIV;
      case DIV:
        return BinaryOpInstruction.Operator.MUL;
      case AND:
        Util.Assert(false, "Not sure how to handle AND!");
      case OR:
        Util.Assert(false, "Not sure how to handle OR!");
      case XOR:
        Util.Assert(false, "Not sure how to handle XOR!");
      case REM:
        Util.Assert(false, "Not sure how to handle REM!");
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return binOp;
  }

  /**
   * syntactically reverse orientation of operator
   */
  public static ConditionalBranchInstruction.Operator flipOperator(ConditionalBranchInstruction.Operator op) {
    switch (op) {
      case LT:
        return ConditionalBranchInstruction.Operator.GT;
      case LE:
        return ConditionalBranchInstruction.Operator.GE;
      case GT:
        return ConditionalBranchInstruction.Operator.LT;
      case GE:
        return ConditionalBranchInstruction.Operator.LE;
      case EQ:
        return ConditionalBranchInstruction.Operator.EQ;
      case NE:
        return ConditionalBranchInstruction.Operator.NE;
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return op;
  }

  /**
   * logically negate operator
   */
  public static ConditionalBranchInstruction.Operator negateOperator(ConditionalBranchInstruction.Operator op) {
    switch (op) {
      case LT:
        return ConditionalBranchInstruction.Operator.GE;
      case LE:
        return ConditionalBranchInstruction.Operator.GT;
      case GT:
        return ConditionalBranchInstruction.Operator.LE;
      case GE:
        return ConditionalBranchInstruction.Operator.LT;
      case EQ:
        return ConditionalBranchInstruction.Operator.NE;
      case NE:
        return ConditionalBranchInstruction.Operator.EQ;
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return op;
  }

  public static String opToString(ConditionalBranchInstruction.Operator op) {
    String str = null;
    switch (op) {
      case LT:
        str = "<";
        break;
      case LE:
        str = "<=";
        break;
      case GT:
        str = ">";
        break;
      case GE:
        str = ">=";
        break;
      case EQ:
        str = "==";
        break;
      case NE:
        str = "!=";
        break;
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return str;
  }

  public static String binOpToString(BinaryOpInstruction.Operator binOp) {
    String str = null;
    switch (binOp) {
      case ADD:
        str = "+";
        break;
      case SUB:
        str = "-";
        break;
      case MUL:
        str = "*";
        break;
      case DIV:
        str = "/";
        break;
      case AND:
        str = "&&";
        break;
      case OR:
        str = "||";
        break;
      case XOR:
        str = "^";
        break;
      case REM:
        str = "%";
        break;
      default:
        Util.Assert(false, "Unsupported op!");
    }
    return str;
  }

  public static PointerVariable makeReturnValuePointer(CGNode callee, HeapModel hm) {
    return makePointerVariableImpl(hm.getPointerKeyForReturnValue(callee));
    // return new ConcretePointerVariable(method, makeReturnValueName(method),
    // 0);
  }

  /*
   * public static String makeReturnValueName(CGNode method) { String name =
   * method.toString(); Util.Assert(!name.contains("synthetic"),
   * "evil synthetic var name " + name); return name.toString() + " Retval"; }
   */

  public static boolean isCommutative(ConditionalBranchInstruction.Operator op) {
    switch (op) {
      case EQ:
        return true;
      case NE:
        return true;
      case LE:
        return false;
      case LT:
        return false;
      case GT:
        return false;
      case GE:
        return false;
      default:
        Util.Unimp("unhandled op " + op);
        return false;
    }

  }

  public static <T> void visualizeCG(Graph<T> g) {
    String pdfFile = "/home/sam/Desktop/WALA/test.pdf";

    String dotExe = "/usr/bin/dot";
    try {
      DotUtil.dotify(g, null, "temp.dt", pdfFile, dotExe);
    } catch (WalaException e) {
      Util.Debug("Exception " + e);
    }
  }

  public static void visualizeIR(IClassHierarchy cha, IR ir, String name) {
    System.err.println("DOIN IT!");
    String psFile = name + ".ps";
    String dotFile = name + ".dot";
    String dotExe = "/usr/bin/dot";
    String gvExe = "/usr/bin/gv";
    try {
      PDFViewUtil.ghostviewIR(cha, ir, psFile, dotFile, dotExe, gvExe);
    } catch (WalaException e) {
      System.err.println("error getting pdf " + e);
      System.exit(1);
    }
    System.err.println("DONE!");
  }

  public static <T> String printArray(T[] arr) {
    String s = "";
    for (int i = 0; i < arr.length; i++) {
      s += arr[i].toString() + "\n";
    }
    return s;
  }

  public static <T> String printCollection(Collection<T> c) {
    Iterator<T> iter = c.iterator();
    StringBuffer s = new StringBuffer();
    while (iter.hasNext()) {
      s.append(iter.next());
      s.append("\n");
    }
    return s.toString();
  }

  public static boolean generateFlowInsensitiveWitness(PointsToEdge edge, Set<PointsToEdge> refuted,
      AbstractDependencyRuleGenerator depRuleGenerator, HeapGraph hg, CallGraph cg) {
    Set<PointsToEdge> edges = new TreeSet<PointsToEdge>();
    edges.add(edge);
    return generateFlowInsensitiveWitness(edges, refuted, depRuleGenerator, hg, cg);
  }

  public static boolean generateFlowInsensitiveWitness(Set<PointsToEdge> toProduce, Set<PointsToEdge> refuted,
      AbstractDependencyRuleGenerator depRuleGenerator, HeapGraph hg, CallGraph cg) {
    Util.Debug("generating flow-insens witness");
    final int TIMEOUT = 10000;
    int count = 0;

    Set<PointsToEdge> produced = new TreeSet<PointsToEdge>();

    while (!toProduce.isEmpty()) {
      if (count++ > TIMEOUT) {
        Util.Unimp("TIMEOUT while generating flow-insensitive witness!");
        System.err.println("TIMEOUT while generating flow-insensitive witness");
        return true;
      }

      PointsToEdge nextEdge = toProduce.iterator().next();
      /*
       * if (refuted.contains(nextEdge)) { Util.Debug("edge " + nextEdge +
       * " already refuted!"); Util.Unimp("refuting on flow-insens witness");
       * return false; }
       */
      Set<DependencyRule> rules = Util.getRulesProducingEdge(nextEdge, depRuleGenerator);
      Util.Assert(!rules.isEmpty(), "no rule can produce " + nextEdge);

      boolean applicable = true;
      List<DependencyRule> applicableRules = new LinkedList<DependencyRule>();
      for (DependencyRule rule : rules) {
        applicable = true;
        Util.Assert(nextEdge.equals(rule.getShown()), "rule " + rule + " does not produce " + nextEdge);
        /*
         * for (PointsToEdge toShow : rule.getToShow()) {
         * 
         * if (refuted.contains(toShow)) { applicable = false; break; } }
         */
        if (applicable)
          applicableRules.add(rule);
      }
      if (!applicableRules.isEmpty()) {
        // else, applying this rule is OK.
        // Util.Assert(applicableRules.size() == 1, "more than one choice!");
        for (DependencyRule rule : applicableRules) {
          for (PointsToEdge toShow : rule.getToShow()) {
            if (!produced.contains(toShow))
              toProduce.add(toShow);
          }
          boolean removed = toProduce.remove(nextEdge);
          Util.Assert(removed, "couldn't remove edge " + nextEdge);
          produced.add(nextEdge);
          Util.Debug("produced " + nextEdge);
          break;
        }
      } else {
        Util.Debug("couldn't generate flow-insensitive witness! unshown " + nextEdge);
        Util.Unimp("refuting on flow-insens witness");
        return false;
      }
    }
    Util.Debug("flow-insensitive witness found!");
    return true;
  }

  public static <T> boolean intersectionNonEmpty(Collection<T> a, Set<T> b) {
    for (T elem : a) {
      if (b.contains(elem))
        return true;
    }
    return false;
  }

  public static <T> boolean equal(T a, T b) {
    return (a == null) ? (b == null) : a.equals(b);
  }

  public static <T> int treeSetCompare(TreeSet<? extends Comparable<T>> a, TreeSet<? extends Comparable<T>> b) {
    if (a.size() > b.size())
      return 1;
    else if (a.size() < b.size())
      return -1;
    // sets are the same size
    Iterator<? extends Comparable<T>> iter1 = a.descendingIterator(), iter2 = b.descendingIterator();
    while (iter1.hasNext()) {
      Comparable<T> c0 = iter1.next();
      Comparable<T> c1 = iter2.next();
      int comparison = c0.compareTo((T) c1);
      if (comparison != 0)
        return comparison;
    }
    return 0;
  }

  public static <T> Set<T> flatten(Collection<Set<T>> sets) {
    Set<T> flatSet = HashSetFactory.make();
    for (Set<T> set : sets)
      flatSet.addAll(set);
    return flatSet;
  }

  public static boolean compareFiles(String file1, String file2) {
    try {
      BufferedReader expected = new BufferedReader(new FileReader(file1));
      BufferedReader actual = new BufferedReader(new FileReader(file2));
      String expectedLine;
      String actualLine;
      while ((expectedLine = expected.readLine()) != null) {
        actualLine = actual.readLine();
        if (!expectedLine.equals(actualLine)) {
          return false;
        }
      }
      return true;
    } catch (Exception e) {
      return false;
    }
  }

  public static Set<String> getAllLinesFromFile(String filename) {
    Set<String> lines = HashSetFactory.make();
    try {
      BufferedReader reader = new BufferedReader(new FileReader(filename));
      String line;
      while ((line = reader.readLine()) != null) {
        lines.add(line);
      }
    } catch (Exception e) {
    }
    return lines;
  }
  
  public static boolean isOnlyCalledBy(CGNode caller, CGNode callee, CallGraph callGraph) {
    Collection<CGNode> preds = Util.iteratorToCollection(callGraph.getPredNodes(callee));
    while (preds.size() == 1) {
      CGNode next = preds.iterator().next();
      if (next.equals(caller)) return true;
      preds = Util.iteratorToCollection(callGraph.getPredNodes(next));
    }
    return false;
  }
}

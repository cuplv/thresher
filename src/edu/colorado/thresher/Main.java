package edu.colorado.thresher;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.JarFile;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.BinaryDirectoryTreeModule;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.dataflow.IFDS.ICFGSupergraph;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisOptions.ReflectionOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.propagation.AllocationSiteInNode;
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey;
import com.ibm.wala.ipa.callgraph.propagation.ConcreteTypeKey;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ipa.modref.ModRef;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.CollectionFilter;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.config.FileOfClasses;
import com.ibm.wala.util.graph.traverse.BFSIterator;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;
import com.ibm.wala.util.intset.IBinaryNaturalRelation;
import com.ibm.wala.util.intset.OrdinalSet;


public class Main {
	public static final boolean DEBUG = Options.DEBUG; // print debug information (LOTS of printing)

	public static IClassHierarchy DEBUG_cha;
	
	private static IClass WEAK_REFERENCE;

    private static boolean REGRESSIONS = false; // don't set manually; automatically on when regression tests run and off otherwise
	
    public static String REGRESSION = "__regression";
    
	// field errors we see in almost every app and do not want to repeatedly re-refute
	static final String[] blacklist = new String[] { "EMPTY_SPANNED", "sThreadLocal", "sExecutor", "sWorkQueue", "sHandler", "CACHED_CHARSETS" };
	
	static final Set<String> EMPTY_SET = Collections.EMPTY_SET;

    public static void main(String[] args) throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
						  CallGraphBuilderCancelException {
    	String target = Options.parseArgs(args);
    	if (target == null) {
			System.out.println("No analysis targets given...exiting.");
			System.exit(1);
		} else if (target.equals(REGRESSION)) runRegressionTests();
		else runAnalysisAllStaticFields(target);
		//else runAnalysisActivityFieldsOnly(target, true, true);
    }
    
    public static void runRegressionTests() throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
	  CallGraphBuilderCancelException {
		  Util.DEBUG = true;
		  Util.LOG = true;
		  Util.PRINT = true;
		  REGRESSIONS = true;
		  final String[] fakeMapTests = new String[] { "IntraproceduralStrongUpdate", "SimpleNoRefute", "FunctionCallRefute", "FunctionCallNoRefute",
				  						  "BranchRefute", "BranchNoRefute", "HeapRefute", "HeapNoRefute", "InterproceduralRefute", 
				 						  "PathValueUpdateRefute", "PathValueUpdateNoRefute", "SharedStaticMapNoRefute", "ManuNoRefute2", "MultiWayBranchNoRefute", 
				 						  "MultiWayBranchRefute", "SubBranchRefute", "MultiBranchUpdateRefute", "IrrelevantLoopRefute", "IrrelevantLoopNoRefute",
				 						  "MultiBranchAndThrowNoRefute", 
				 						  		  "SimpleDynamicDispatchRefute", 
				 								  "SimpleDynamicDispatchNoRefute", "ReturnValueNoRefute", 
				 						  "ReturnValueRefute", "BranchInLoopNoRefute", "BranchInLoopRefute", "DoubleLoopNoRefute", "DoubleLoopRefute", 
				 						  "DoubleLoopNoRefute", "LoopInBranchRefute", "LoopInBranchNoRefute", "HeapReturnRefute", "HeapReturnNoRefute",
				 						  "NullRefute", 
				 						  "NullNoRefute", "IrrelevantBranchNoRefute", "UninitVarRefute", "UninitVarNoRefute", 
				 						  "ArrayLengthRefute", "ArrayLengthNoRefute", "DoubleLoopAndBranchNoRefute", 
				 						  "SimpleDisjunctiveRefute",
				 						  "SimpleDisjunctiveNoRefute", 
				 						  "SimpleConjunctiveRefute", 
				 						  "SimpleConjunctiveNoRefute", 
				 						  "MultiLevelParamPassRefute", 
				 						  "MultiLevelParamPassNoRefute", "StartInLoopNoRefute", "CallInLoopHeadRefute", "CallInLoopHeadNoRefute", "LoopProcRefute", 
				 						  "LoopProcNoRefute", "ForEachLoopRefute", "ForEachLoopNoRefute", "InfiniteLoopRefute", "StraightLineCaseSplitNoRefute",
				 						  "ManuLoopNoRefute", "CallPruningNoRefute", "SingletonNoRefute" }; 
		  
		  // tests that we expect to fail under piecewise execution
		  final Set<String> piecewiseExceptions = new HashSet<String>();
		  piecewiseExceptions.add("SimpleDynamicDispatchRefute");
		  piecewiseExceptions.add("NullRefute");
		  piecewiseExceptions.add("SimpleDisjunctiveRefute");
		  piecewiseExceptions.add("SimpleConjunctiveRefute");
		  piecewiseExceptions.add("MultiLevelParamPassRefute");
		  
		  final String[] realHashMapTests = new String[] { "SimpleHashMapRefute", "SimpleHashMapNoRefute", "ContainsKeyRefute", "ContainsKeyNoRefute" };
		  
		  //final String[] fakeMapTests0 = new String[] { };
		  final String[] fakeMapTests0 = new String[] { "FunctionCallRefute" };

		  final String[] realHashMapTests0 = new String[] { }; 
		  //final String[] realHashMapTests0 = new String[] { "SimpleHashMapRefute" }; 
		  
		  String regressionDir = "apps/tests/regression/";
		  boolean result;
		  int testNum = 0;
		  int successes = 0;
		  int failures = 0;
		  long start = System.currentTimeMillis();
		  
		  for (String test : fakeMapTests) {
			  Util.Print("Running test " + testNum + ": " + test);
			  long testStart = System.currentTimeMillis();
			  try {
				  result = runAnalysisActivityFieldsOnly(regressionDir + test, true, true);
			  } catch (Exception e) {
				  Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
				  throw e;
			  }
			  Util.clear();
		
			  boolean expectedResult = false;
			  if (test.contains("NoRefute")) expectedResult = true; // HACK: tests that we aren't meant to refute have NoRefute in name
			  // some tests are expected not to pass with piecewise execution
			  if (Options.PIECEWISE_EXECUTION && piecewiseExceptions.contains(test)) result = !result;
			  
			  if (result == expectedResult) {
				  Util.Print("Test " + test + " (# " + (testNum++) + ") passed!");
				  successes++;
			  } else {
				  Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
				  failures++;
				  if (Options.EXIT_ON_FAIL) System.exit(1);	
			  }
			  long testEnd = System.currentTimeMillis();
			  Util.Print("Test took " + ((testEnd - testStart) / 1000) + " seconds.");
			  WALACFGUtil.clearCaches();
		  }

		  testNum = 0;
		
		  for (String test : realHashMapTests) {
			  Util.Print("Running test " + testNum + ": " + test);
			  long testStart = System.currentTimeMillis();
			  try {
				  result = runAnalysisActivityFieldsOnly(regressionDir + test, true, false);
			  } catch (Exception e) {
				  System.err.println("Test " + test + " (#" + (testNum++) + ") failed :(");
				  throw e;
			  }
			  Util.clear();
			  boolean expectedResult = false;
			  if (test.contains("NoRefute")) expectedResult = true; // HACK: tests that we aren't meant to refute have NoRefute in name
			  if (result == expectedResult) {
				  Util.Print("Test " + test + " (# " + (testNum++) + ") passed!");
				  successes++;
			  } else {
				  Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
				  failures++;
				  if (Options.EXIT_ON_FAIL) System.exit(1);
			  }
			  long testEnd = System.currentTimeMillis();
			  Util.Print("Test took " + ((testEnd - testStart) / 1000) + " seconds");
			  WALACFGUtil.clearCaches();
		  }
		 
		  long end = System.currentTimeMillis();
		  Util.Print("All tests complete in " + ((end - start) / 1000) + " seconds");
		  Util.Print(successes + " tests passed, " + failures + " tests failed.");
	  }
	
	private static boolean isInteresting(IField f) {
		return true;
	}
	
	public static void computeSubclassesAndStaticFields(List<IClass> baseClasses, AnalysisScope scope, IClassHierarchy cha, 
			Collection<Entrypoint> entryPoints, Collection<IClass> subclasses, Set<IField> staticFields, Set<MethodReference> saveMethods) {
		for (IClass baseClass : baseClasses) {
			subclasses.add(baseClass);
		    // find all subclasses of the base class	
		    for (IClass subclass : cha.computeSubClasses(baseClass.getReference())) {
		      //if (scope.isApplicationLoader(subclass.getClassLoader())) {
		        subclasses.add(subclass);
		        if (DEBUG) Util.Debug("Found subclass class " + subclass);
		      //} 
		    }
		    
		    for (IClass c : subclasses) { // for each subclass
		    	/*
		    	for (IMethod m : c.getDeclaredMethods()) { // for each method in the class
		    		// make all of the class's public and protected methods entrypoints
			    	// the reason for this is to model the arbitrary execution order of event handler methods in Activity/View; 
			    	// user/OS actions can cause the event handlers to be invoked in any order and any number of times
		    		//if (m.isPublic() || m.isProtected()) entryPoints.add(new DefaultEntrypoint(m, cha));
		    		//if ((m.isPublic() || m.isProtected()) && m.getName().toString().startsWith("on")) entryPoints.add(new DefaultEntrypoint(m, cha));
		    		// save references to methods that can keep a reference to Activity data
		    		//if (m.getName().toString().equals("onRetainNonConfigurationInstance")) saveMethods.add(m.getReference());
		    	}
		    	*/

		    	Collection<IField> fields = c.getAllStaticFields();
		    	for (IField f : fields) { // for each static field in the class
		    		if (isInteresting(f)) {
		    			if (DEBUG) Util.Debug("Found static field " + f.toString());
		    			staticFields.add(f);
		    		}
		    	}
		    }
		}
	}
	
	public static boolean runAnalysisAllStaticFields(String appName, Set<String> refutedEdges) // wrapper
		throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
		//String[] snkClasses = new String[] { "Landroid/app/Activity", "Landroid/view/View"};
		String[] snkClasses = new String[] { "Landroid/app/Activity" };
		String[] srcClasses = new String[0]; // with no base
		return runAnalysis(appName, srcClasses, snkClasses, refutedEdges, false);
	}
	
	public static boolean runAnalysisAllStaticFields(String appName) // wrapper
			throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
		return runAnalysisAllStaticFields(appName, EMPTY_SET);
	}
	
	public static boolean runAnalysisActivityAndViewFieldsOnly(String appName) // wrapper
			throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
		String[] srcClasses = new String[] { "Landroid/app/Activity", "Landroid/view/View"};
		String[] snkClasses = new String[] { "Landroid/app/Activity" };
		return runAnalysis(appName, srcClasses, snkClasses, EMPTY_SET, false);
	}
	
	public static boolean runAnalysisActivityFieldsOnly(String appName) // wrapper 
		throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
		return runAnalysisActivityFieldsOnly(appName, false, false);
	}
	
	public static boolean runAnalysisActivityFieldsOnly(String appName, boolean fakeAct, boolean fakeMap) // wrapper 
			throws FileNotFoundException, IOException, ClassHierarchyException, CallGraphBuilderCancelException {
		if (fakeAct) return runAnalysis(appName, "LAct", fakeMap);
		else return runAnalysis(appName, "Landroid/app/Activity", fakeMap);
	}
	
	public static boolean runAnalysis(String appName, String baseClass, boolean fakeMap) // wrapper
			throws FileNotFoundException, IOException, ClassHierarchyException, CallGraphBuilderCancelException {
		String[] singleton = new String[] { baseClass };
		return runAnalysis(appName, singleton, singleton, EMPTY_SET, fakeMap);
	}

	/**
	 * run Thresher on app
	 * @param appName - path to app to run
	 * @param baseClasses - classes whose static fields we should search from, and instances of which should be not reachable from a static field
	 * @param fakeMap - debug parameter; should be false for all real uses
	 * @return - true if no instance of the base classes is reachable from a static field of the base class, false otherwise
	 */
	public static boolean runAnalysis(String appPath, String[] srcStrings, String[] snkStrings, Set<String> refutedEdges, boolean fakeMap) 
			throws FileNotFoundException, IOException, ClassHierarchyException, CallGraphBuilderCancelException {
	    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
	    Set<IField> staticFields = new HashSet<IField>();
	    Set<MethodReference> saveMethods = new HashSet<MethodReference>();
	    Util.Print("Starting on " + appPath);
	    Logger logger = new Logger(appPath);
		long start = System.currentTimeMillis();
		File exclusionsFile = null;
		if (Options.USE_EXCLUSIONS) exclusionsFile = new File("config/exclusions.txt");
		AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
		if (exclusionsFile != null) scope.setExclusions(FileOfClasses.createFileOfClasses(exclusionsFile));
		JarFile file = new JarFile(Options.ANDROID_JAR);
		scope.addToScope(scope.getPrimordialLoader(), file);
		// add application code
		scope.addToScope(scope.getApplicationLoader(), new BinaryDirectoryTreeModule(new File(appPath)));
		
	    System.out.println("making class hierarchy");
	    IClassHierarchy cha = ClassHierarchy.make(scope);
	    
	    List<IClass> snkClasses = new LinkedList<IClass>();
    	Iterator<IClass> classes = cha.iterator();
    	while (classes.hasNext()) {
    		IClass c = classes.next();
    		if (!scope.isApplicationLoader(c.getClassLoader())) continue;
	    	for (IMethod m : c.getDeclaredMethods()) { // for each method in the class
	    		if (REGRESSIONS) {
	    			if (m.isPublic() || m.isProtected()) {
	    				entryPoints.add(new DefaultEntrypoint(m, cha));
	    			}
	    		} else {
	    			if ((m.isPublic() || m.isProtected()) && m.getName().toString().startsWith("on")) { // add "on*" methods; they're the event handlers
	    				entryPoints.add(new DefaultEntrypoint(m, cha));
	    			}
	    		}
	    		
	    		if (m.getName().toString().equals("onRetainNonConfigurationInstance")) saveMethods.add(m.getReference());
	    	}
    		
    		if (srcStrings.length == 0) { // no src classes; just use all static fields
    			for (IField field : c.getAllStaticFields()) {
    				staticFields.add(field);
    			}
    		}
    	}
    	
	    for (String srcString : srcStrings) {
	    	IClass srcClass = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application, srcString));
	    	if (Options.CHECK_ASSERTS) Util.Assert(srcClass != null, "couldn't find base class " + srcString);
	    	staticFields.addAll(srcClass.getAllStaticFields());
	    	// find all subclasses of the src Class	
			for (IClass subclass : cha.computeSubClasses(srcClass.getReference())) {
				staticFields.addAll(subclass.getAllStaticFields());
			}		    	
	    }
		    
	    for (String snkString : snkStrings) {
	    	IClass snkClass = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application, snkString));
	    	if (Options.CHECK_ASSERTS) Util.Assert(snkClass != null, "couldn't find base class " + snkClass);
	    	snkClasses.add(snkClass);
		}
	    
		WEAK_REFERENCE = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application, "Ljava/lang/ref/WeakReference"));
	    
	    Collection<IClass> subclasses = HashSetFactory.make();
	    computeSubclassesAndStaticFields(snkClasses, scope, cha, entryPoints, subclasses, staticFields, saveMethods);

		// gather entrypoints
	    Collection<? extends Entrypoint> e = entryPoints;
	    Util.Print(e.size() + " entrypoints");
 
	    AnalysisOptions options = new AnalysisOptions(scope, e); // build call graph and pointer analysis
	    options.setReflectionOptions(ReflectionOptions.NO_METHOD_INVOKE); // turn off handling of Method.invoke(), which dramatically speeds up points-to analysis
	    AnalysisCache cache = new AnalysisCache();
	    CallGraphBuilder builder;
	    //CallGraphBuilder builder = com.ibm.wala.ipa.callgraph.impl.Util.makeZeroCFABuilder(options, cache, cha, scope);
	    //CallGraphBuilder builder = com.ibm.wala.ipa.callgraph.impl.Util.makeZeroOneCFABuilder(options, cache, cha, scope);
	    if (!fakeMap) builder = com.ibm.wala.ipa.callgraph.impl.Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);
	    else builder = FakeMapContextSelector.makeZeroOneFakeMapCFABuilder(options, cache, cha, scope);
	    DEBUG_cha = cha; // DEBUG ONLY
	    if (DEBUG) Util.Debug("building call graph");
	    CallGraph cg = builder.makeCallGraph(options, null);
	    //if (CALLGRAPH_PRUNING) expandedCallgraph = ExpandedCallgraph.make(cg);
	    Util.Print(CallGraphStats.getStats(cg));
	    PointerAnalysis pointerAnalysis = builder.getPointerAnalysis();
	    HeapGraph hg = pointerAnalysis.getHeapGraph();
	    MySubGraph<Object> graphView = new MySubGraph<Object>(hg);
	    HeapModel hm = pointerAnalysis.getHeapModel();
	    
	    ModRef modref = ModRef.make();
	    Map<CGNode, OrdinalSet<PointerKey>> modRefMap = modref.computeMod(cg, pointerAnalysis);
	      
	    Set<Pair<Object,Object>> fieldErrorList = new HashSet<Pair<Object,Object>>();
	    Map<String,Set<IClass>> leakedActivities = new HashMap<String, Set<IClass>>(); // map from fields -> Acts that leak via that field
	    
	    for (IField f : staticFields) {
	    	boolean skipThis = false;
			for (String skip : blacklist) {
				if (f.toString().contains(skip)) {
					Util.Print("skipping " + f + " due to blacklist");
					skipThis = true;
					break;
				}
			}
			if (skipThis) continue;
	    	
	    	PointerKey field = hm.getPointerKeyForStaticField(f);
			BFSIterator<Object> iter = new BFSIterator<Object>(hg, field);
			// see if an Activity is reachable from this static field
			while (iter.hasNext()) {
				Object node = iter.next();
				IClass type = null;
				if (node instanceof ConcreteTypeKey) {
					type = ((ConcreteTypeKey)node).getConcreteType();
				} else if (node instanceof AllocationSiteInNode) {
					type = ((AllocationSiteInNode)node).getConcreteType();
				}
				if (type != null && subclasses.contains(type)) { // allow arbitrary number of errors per field
					Collection<Object> found = new HashSet<Object>();
					found.add(node);
					
					// is there a path from the static field to the Activity that does not contain weak references?
					if (removeWeakReferences(graphView, field, found, hg, cha)) {
						Set<IClass> leaked = leakedActivities.get(field.toString());
						if (leaked == null) {
							leaked = new HashSet<IClass>();
							leakedActivities.put(field.toString(), leaked);
							Util.Print("found field error " + field);
							logger.logErrorField();
						}
						InstanceKey activityInstance = (InstanceKey) node;
						if (leaked.add(activityInstance.getConcreteType())) { // see if we already know that this Activity can leak via this field
							Pair<Object,Object> errPair = Pair.make((Object) field, node);
							fieldErrorList.add(errPair);
						}
					}
				}
			}
	    }
	    
	    Util.Print("found " + leakedActivities.keySet().size() + " potentially problematic fields");
	    Util.Print("found " + fieldErrorList.size() + " (field, error) pairs");
	    logger.logNumStaticFields(staticFields.size());
	    logger.logTotalErrors(fieldErrorList.size());
	    long refuteStart = System.currentTimeMillis();
	    boolean result = false;
	    if (!Options.FLOW_INSENSITIVE_ONLY) {
	    	result = refuteFieldErrors(fieldErrorList, graphView, cache, hg, cg, hm, cha, modRefMap, refutedEdges, logger);
	    }
	    long refuteEnd = System.currentTimeMillis();
	    Util.Print("Symbolic execution completed in " + ((refuteEnd - refuteStart) / 1000.0) + " seconds");
	    Util.Print("Total time was " + ((refuteEnd - start) / 1000.0) + " seconds");
	    Util.Print("Done with " + appPath);
	    return result;
	}
	
	public static boolean refuteFieldErrors(Set<Pair<Object,Object>> fieldErrors,  MySubGraph<Object> graphView, AnalysisCache cache, HeapGraph hg, CallGraph cg, 
											HeapModel hm, IClassHierarchy cha, Map<CGNode, OrdinalSet<PointerKey>> modRef, Set<String> refutedEdgeStrings, 
											Logger logger) {
		List<Pair<Object,Object>> trueErrors = new LinkedList<Pair<Object,Object>>(), falseErrors = new LinkedList<Pair<Object,Object>>();
		TreeSet<PointsToEdge> producedEdges = new TreeSet<PointsToEdge>(), refutedEdges = new TreeSet<PointsToEdge>();
		AbstractDependencyRuleGenerator aDepRuleGenerator = new AbstractDependencyRuleGenerator(cg, hg, hm, cache, refutedEdges, modRef, DEBUG);

		int count = 1;
		Collection<Object> snkCollection = new LinkedList<Object>();
		
		IBinaryNaturalRelation relation = null;
		// for each error
		for (Pair<Object,Object> error : fieldErrors) {
			try {
				Util.Print("starting on error " + count++ + " of " + fieldErrors.size() + ": " + error.fst);
				snkCollection.add(error.snd);
				MyBFSPathFinder<Object> finder = new MyBFSPathFinder<Object>(graphView, error.fst, new CollectionFilter<Object>(snkCollection));
				if (relation != null) finder.setIgnoreIfBoth(relation);
				// if we can refute error
				if (refuteFieldErrorForward(error, graphView, producedEdges, aDepRuleGenerator, refutedEdges, refutedEdgeStrings, hg, cg, hm, cha, finder, logger)) {
					Util.Print("successfully refuted error path " + error);
					logger.logRefutedError();
					falseErrors.add(error);
				} else {
					Util.Print("successfully witnessed error path " + error);
					logger.logWitnessedError();
					logger.logWitnessedField(error.fst.toString());
					trueErrors.add(error);
				}
				relation = finder.getIgnoreIfBoth();
			} catch (Exception e) {
				Util.Print("problem while examining " + error + ": " + e + " " + Util.printArray(e.getStackTrace()));
				logger.logFailure();
				Thread.dumpStack();
				if (Options.EXIT_ON_FAIL) System.exit(1);
				// otherwise, soundly (but not precisely) add error to witnessed list
				trueErrors.add(error);
			}
		}
		Util.Print("Refuted " + falseErrors.size() + " errors, witnessed " + trueErrors.size() + " errors");
		Util.Print("STATS:\n" + logger.dumpHumanReadable() + "\n" + logger.dumpCountMap());
		boolean result = falseErrors.size() == 0;
		Util.Print("<Labels>" + logger.dumpColumnLabels() + "</Labels>");
		Util.Print("<CSV>" + logger.dumpCSV() + "</CSV>");
		// returns true if the path is feasible
		return result;
	}
	
	/**
	 * @return - true if the error is a refutation, false otherwise
	 */
	public static boolean refuteFieldErrorForward(Pair<Object,Object> error, MySubGraph<Object> graphView, TreeSet<PointsToEdge> producedEdges, 
			  								 AbstractDependencyRuleGenerator aDepRuleGenerator, TreeSet<PointsToEdge> refutedEdges, Set<String> refutedEdgeStrings,
			  								 HeapGraph hg, CallGraph cg, HeapModel hm, IClassHierarchy cha, MyBFSPathFinder<Object> finder, Logger logger) {
		  Collection<Object> snkCollection = new LinkedList<Object>();
		  snkCollection.add(error.snd);
		  List<Object> errorPath = finder.find();
		  if (errorPath == null) {
			  Util.Print("Edges refuted on previous error preclude us from finding path! this error infeasible");
			  return true;
		  }
		  // reverse list and print
		  LinkedList newPath = new LinkedList<Object>();
		  for (Object edge : errorPath) {
			  newPath.addFirst(edge);
			  Util.Print(edge.toString());
		  }
		  errorPath = newPath;
		  Util.Print("have error path; size is " + errorPath.size());
		  int witnessedCount = 0;
		  	  
		  while (errorPath != null) {
			  boolean refutation = false;
			  int srcIndex = 1;
			  int snkIndex = 0;
			  PointerKey fieldKey = null;
			  while (srcIndex < errorPath.size()) {
				  Object snk = errorPath.get(srcIndex);
				  if (snk instanceof PointerKey && !(snk instanceof StaticFieldKey)) {
					  // src is intermediate point in points-to edge; either field name or array contents
					  if (snk instanceof ArrayContentsKey) {
						  fieldKey = (PointerKey) snk;
					  } else if (snk instanceof InstanceFieldKey) {
						  InstanceFieldKey ifk = (InstanceFieldKey) snk;
						  fieldKey = ifk;
					  } else {
						Util.Assert(false, "UNSUPPORTED POINTER KEY TYPE!" + snk);
					  }
					  srcIndex++;
				  } else {
					  Object src = errorPath.get(snkIndex);
					  Util.Assert(src instanceof InstanceKey || src instanceof StaticFieldKey, "Sink should always be concrete; is " + src.getClass() + ": " + src);
					  if (src instanceof StaticFieldKey) fieldKey = (StaticFieldKey) src;
					  PointerVariable source = Util.makePointerVariable(src);
					  PointerVariable sink = Util.makePointerVariable(snk);
					  PointsToEdge witnessMe = new PointsToEdge(source, sink, fieldKey);

					  if (!producedEdges.contains(witnessMe)) {
						  // for now, we insist on refuting *all* contexts for a given edge the first time we see it
						  // so if we refute an edge and then see it again in the error path, we are seeing it again because the version we refuted
						  // was in a different context. however, since we refute for all contexts at once, we can refute this edge immediately 
						  // because we've already done so in the past)
						  List<Pair<InstanceKey,Object>> srcFieldPairs; 
						  if (refutedEdges.contains(witnessMe) || refutedEdgeStrings.contains(witnessMe.toString())) {
							  if (DEBUG) Util.Debug("already refuted edge " + witnessMe);
							  srcFieldPairs = new LinkedList<Pair<InstanceKey,Object>>(); 
						  } else {
							  if (DEBUG) Util.Debug("ATTEMPTING TO REFUTE EDGE " + witnessMe);
							  Util.Print("%%%%%%%%%%%%%%%%%Starting on edge " + witnessMe + "%%%%%%%%%%%%%%%%%");
							  long start = System.currentTimeMillis();
							  srcFieldPairs = generateWitness(witnessMe, aDepRuleGenerator, cha, hg, cg, refutedEdges, logger);
							  Util.Print("Edge took " + ((System.currentTimeMillis() - start) / 1000.0) + " seconds.");
							  WALACFGUtil.clearCaches();
						  }
						  if (srcFieldPairs == null) {
							  // edge produced, continue generating witnesses on this path
							  Util.Print("Successfully produced " + witnessMe + "; done with " + (++witnessedCount) + " of " + errorPath.size());
							  producedEdges.add(witnessMe);
							  logger.logEdgeWitnessed();
						  } else {
							  // edge refuted
							  witnessedCount = 0;
							  refutedEdges.add(witnessMe);
							  IBinaryNaturalRelation ignoreIfBoth = finder.getIgnoreIfBoth();
							  finder = new MyBFSPathFinder<Object>(graphView, error.fst, new CollectionFilter<Object>(snkCollection));
							  finder.setIgnoreIfBoth(ignoreIfBoth);
							  if (fieldKey == null) {
								  Util.Assert(false, "how can field key be null?");
								  graphView.addIgnoreEdge(src, snk, hg);
							  } else {
								  graphView.addIgnoreEdge(fieldKey, snk, hg);
								  
								  if (fieldKey instanceof ArrayContentsKey) {
									  for (Pair<InstanceKey,Object> pair : srcFieldPairs) {
										  if (pair.snd instanceof ArrayContentsKey) {
											  graphView.addIgnoreEdge(pair.snd, snk, hg);
										  }
									  }
								  } else {
									  IField refutedFieldName = null;
									  if (fieldKey instanceof StaticFieldKey) {
										  refutedFieldName = ((StaticFieldKey) fieldKey).getField();
									  } else if (fieldKey instanceof InstanceFieldKey) {
										  refutedFieldName = ((InstanceFieldKey) fieldKey).getField();
									  } else Util.Assert(false, "expecting instance field key ors static field key; got " + fieldKey);
									  
									  for (Pair<InstanceKey,Object> pair : srcFieldPairs) {
										  if (pair.snd instanceof InstanceFieldKey) {
											  IField otherFieldName = ((InstanceFieldKey) pair.snd).getField();
											  if (otherFieldName.equals(refutedFieldName)) {
												  graphView.addIgnoreEdge(pair.snd, snk, hg);
											  }
										  }
									  }
								  }
								  
							  }
							  Util.Print("Successfully refuted edge " + witnessMe + "; now trying to find error path  without it");
							  logger.logEdgeRefutation();
							  // run another DFS to see if error path can still be created without refuted edge
							  errorPath = finder.find();
							  if (errorPath != null) {
								  if (DEBUG) Util.Debug("refuted edge, but err path still exists; size " + errorPath.size());
								  newPath = new LinkedList<Object>();
								  for (Object edge : errorPath) {
									  newPath.addFirst(edge);
									  Util.Print(edge.toString());
								  }
								  errorPath = newPath;
							  } else Util.Debug("no path found!");
							  refutation = true;
							  break;
						  }
					  } else {
						 if (DEBUG) Util.Debug("already produced " + witnessMe);
					  }
					  fieldKey = null;
					  snkIndex = srcIndex;
					  srcIndex++;
				  } // end of producedEdges.contains(witnessMe) else block
			  }  // end of srcIndex < errorPath.size() witness generation loop
			  if (!refutation) {
				  // ended loop without a refutation; we have witnessed entire error path
				  if (DEBUG) Util.Debug("error is real! we have witnessed entire path");
				  if (Options.DUMP_WITNESSED_ERR_PATHS) {
					  Util.Print("<Err Path>");
					  Util.Print(Util.printCollection(errorPath));
					  Util.Print("</Err Path>");
				  }
				  return false;
			  } 
		  } // end of "while path exists" loop
		  // error path is null; we have a refutation!
		  return true;
	  }
	
	/**
	 * @return - null if feasible, list of (src, field) pairs to remove otherwise
	 */
	private static List<Pair<InstanceKey,Object>> generateWitness(PointsToEdge witnessMe, AbstractDependencyRuleGenerator depRuleGenerator, 
																  IClassHierarchy cha, HeapGraph hg, CallGraph cg, Set<PointsToEdge> refutedEdges,
																  Logger logger) {
		final Set<PointsToEdge> toProduce = new HashSet<PointsToEdge>();
		toProduce.add(witnessMe);

		// find potential last rule(s) applied in witness
		Iterator<PointsToEdge> setIter = toProduce.iterator();
		PointsToEdge produceMe = setIter.next();
		//System.err.println("Producing " + produceMe);
		final Set<DependencyRule> lastApplied;
		if (Options.GEN_DEPENDENCY_RULES_EAGERLY) lastApplied = Util.getRulesProducingEdge(produceMe, hg, depRuleGenerator, cg);
		else lastApplied = Util.getProducersForEdge(produceMe, depRuleGenerator);
		Util.Print(lastApplied.size() + " potential starting points.");
		
		logger.logProducingStatementsForEdge(lastApplied.size());
		int lastRuleCounter = 1;
		for (DependencyRule lastRule : lastApplied) {
			Util.Print("starting on possible rule " + (lastRuleCounter++) + " of " + lastApplied.size() + "\n" + lastRule);
			if (!lastRule.getShown().toString().equals(witnessMe.toString())) {
				if (DEBUG) Util.Debug("rule does not produce edge.. continuing");
				if (DEBUG) Util.Debug("refuted all contexts for possible rule " + lastRuleCounter + " of " + lastApplied.size());
				continue;
				//lastRule.getShown() + " not the same as " + witnessMe);
			}
			PointerStatement snkStmt = lastRule.getStmt();
			int startLine = snkStmt.getLineNum();
			if (DEBUG) Util.Debug("start line is " + startLine);
			final Set<CGNode> potentialNodes = new HashSet<CGNode>();
			potentialNodes.add(lastRule.getNode());
			int numContexts = potentialNodes.size();

			for (CGNode startNode : potentialNodes) {
				Util.Assert(numContexts == potentialNodes.size(), "sizes don't match!");
				Util.Print("starting in method " + startNode);
				final PointsToQuery startQuery = new PointsToQuery(lastRule, depRuleGenerator); 
				final IQuery query = new CombinedPathAndPointsToQuery(startQuery); 
				IR ir = startNode.getIR();
				SSACFG cfg = ir.getControlFlowGraph();
				SSACFG.BasicBlock startBlk = cfg.getBlockForInstruction(startLine);
				int startLineBlkIndex = WALACFGUtil.findInstrIndexInBlock(snkStmt.getInstr(), startBlk);
				Util.Assert(startBlk.getAllInstructions().get(startLineBlkIndex).equals(snkStmt.getInstr()), 
						"instrs dif! expected " + snkStmt.getInstr() + "; found " + startBlk.getAllInstructions().get(startLineBlkIndex));
				
				ISymbolicExecutor exec;
				ICFGSupergraph superGraph = null;
				if (Options.CALLGRAPH_PRUNING) superGraph = ICFGSupergraph.make(cg, depRuleGenerator.getCache());				
				boolean foundWitness;
				if (Options.PIECEWISE_EXECUTION) exec = new PiecewiseSymbolicExecutor(cg, superGraph, logger);
				else if (Options.CALLGRAPH_PRUNING) exec = new PruningSymbolicExecutor(cg, superGraph, logger);
				else exec = new OptimizedPathSensitiveSymbolicExecutor(cg, logger, refutedEdges);
				foundWitness = exec.executeBackward(startNode, startBlk, startLineBlkIndex - 1, query); // start at line BEFORE snkStmt
				
				Util.Print(logger.dumpEdgeStats());
				if (foundWitness) {
					return null;
				} // else, refuted this attempt; try again
			}
		}
		return new LinkedList<Pair<InstanceKey,Object>>(); // refuted all posssible last rules without a witness
	}	  
	
	// returns true if error path still exists after removing weak references, false otherwise
	public static boolean removeWeakReferences(MySubGraph<Object> graphView, Object srcKey, Collection<Object> snkKey, HeapGraph hg, IClassHierarchy cha) {
		  boolean foundWeakRef;
		  for (;;) {
			  foundWeakRef = false;
			  BFSPathFinder<Object> bfs = new BFSPathFinder<Object>(graphView, srcKey, new CollectionFilter<Object>(snkKey));
			  List<Object> path = bfs.find();
			  if (path == null) return false;
			  
			  int srcIndex = 1, snkIndex = 0;
			  Object fieldKey = null;
			  while (srcIndex < path.size()) {
				  Object src = path.get(srcIndex);
				  if (src instanceof PointerKey && !(src instanceof StaticFieldKey)) {
					  // src is intermediate point in points-to edge; either field name or array contents
					  if (src instanceof ArrayContentsKey) {
						  fieldKey = src;
					  } else if (src instanceof InstanceFieldKey) {
						  InstanceFieldKey ifk = (InstanceFieldKey) src;
						  fieldKey = ifk;
						  String instanceFieldName = ifk.getField().getName().toString();
						  String className = ifk.getField().getDeclaringClass().toString();
					  } else {
						Util.Assert(false, "UNSUPPORTED POINTER KEY TYPE!" + src);
					  }
					  srcIndex++;
				  } else {
					  Object snk = path.get(snkIndex);
					  if (isWeakReference(src, snk, cha)) {
						  graphView.addIgnoreEdge(fieldKey, snk, hg);
						  foundWeakRef = true;
						  break;
					  }
					  fieldKey = null;
					  snkIndex = srcIndex;
					  srcIndex++;
				  }
			  }
			  if (!foundWeakRef) {
				  if (DEBUG) {
					  System.out.println("<FIELD PATH Length: " + path.size());
					  for (int i=path.size() - 1; i >= 0; i--) System.out.println(path.get(i) + " (" + path.get(i).getClass() + ")");
					  System.out.println("</FIELD PATH>");
				  }
				  return true;
			  }
		  }
	  }
	  
	  private static boolean isWeakReference(Object src, Object snk, IClassHierarchy cha) {
		  if (!Options.INCLUDE_WEAK_REFERENCES) {
			  // check if any links in the path are WeakReference
			  if (src instanceof InstanceKey) {
				  InstanceKey key = (InstanceKey) src;
				  IClass type = key.getConcreteType();
				  if (type.equals(WEAK_REFERENCE) || cha.isSubclassOf(type, WEAK_REFERENCE)) return true;
			  } 
			  if (snk instanceof InstanceKey) {
				  InstanceKey key = (InstanceKey) snk;
				  IClass type = key.getConcreteType();
				  if (type.equals(WEAK_REFERENCE) || cha.isSubclassOf(type, WEAK_REFERENCE)) return true;
			  }
			  // also do silly syntactic check
			  //return src.toString().contains("WeakReference") || snk.toString().contains("WeakReference");
		  }
		  return false;
	  }	
}

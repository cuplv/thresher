package edu.colorado.thresher;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarFile;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.BinaryDirectoryTreeModule;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
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
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ipa.modref.ModRef;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.CollectionFilter;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.config.FileOfClasses;
import com.ibm.wala.util.graph.traverse.BFSIterator;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;
import com.ibm.wala.util.graph.traverse.DFS;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.OrdinalSet;

public class Main {
  
  // print debug information (LOTS of printing)  
  public static IClassHierarchy DEBUG_cha;

  private static IClass WEAK_REFERENCE;

  // don't set manually; is automatically on when regressions tests run and off otherwise
  private static boolean REGRESSIONS = false; 

  public static String REGRESSION = "__regression";
  
  // absolute path to file containing core JVM components
  private static final String JVM_PATH = "/usr/lib/jvm/java-6-openjdk-amd64/jre/lib/rt.jar";

  // field errors we see in almost every app and do not want to repeatedly re-refute
  static final String[] blacklist = new String[] { "EMPTY_SPANNED", "sThreadLocal", "sExecutor", "sWorkQueue", "sHandler",
      "CACHED_CHARSETS" };

  public static void main(String[] args) throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
      CallGraphBuilderCancelException {
    String target = Options.parseArgs(args);
    if (target == null) {
      System.out.println("No analysis targets given...exiting.");
      System.exit(1);
    } else if (target.equals(REGRESSION))
      runRegressionTests();
    else
      if (Options.IMMUTABILITY) runImmutabilityCheck(target);
      else if (Options.SYNTHESIS) runSynthesizer(target);
      else if (Options.ANDROID_UI) runAndroidBadMethodCheck(target);
      else runAnalysisAllStaticFields(target);
  }

  public static void runRegressionTests() throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
    CallGraphBuilderCancelException {
    Util.DEBUG = true;
    Util.LOG = true;
    Util.PRINT = true;
    REGRESSIONS = true;
    //runImmutabilityRegressionTests();
    runAndroidLeakRegressionTests();
  }
  
  
  public static void runAndroidLeakRegressionTests() throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
    CallGraphBuilderCancelException {
    Options.ANDROID_JAR = "android/android-2.3.jar"; // use non-annotated JAR
    final String[] fakeMapTests = new String[] { "IntraproceduralStrongUpdate", "SimpleNoRefute", "FunctionCallRefute",
        "FunctionCallNoRefute", "BranchRefute", "BranchNoRefute", "HeapRefute", "HeapNoRefute", "InterproceduralRefute",
        "PathValueUpdateRefute", "PathValueUpdateNoRefute", "SharedStaticMapNoRefute", "ManuNoRefute2", "MultiWayBranchNoRefute",
        "MultiWayBranchRefute", "SubBranchRefute", "MultiBranchUpdateRefute", "IrrelevantLoopRefute", "IrrelevantLoopNoRefute",
        "MultiBranchAndThrowNoRefute", "SimpleDynamicDispatchRefute", "SimpleDynamicDispatchNoRefute", "ReturnValueNoRefute",
        "ReturnValueRefute", "BranchInLoopNoRefute", "BranchInLoopRefute", "DoubleLoopNoRefute", "DoubleLoopRefute",
        "DoubleLoopNoRefute", "LoopInBranchRefute", "LoopInBranchNoRefute", "HeapReturnRefute", "HeapReturnNoRefute", "NullRefute",
        "NullNoRefute", "IrrelevantBranchNoRefute", "UninitVarRefute", "UninitVarNoRefute", "ArrayLengthRefute",
        "ArrayLengthNoRefute", "DoubleLoopAndBranchNoRefute", "SimpleDisjunctiveRefute", "SimpleDisjunctiveNoRefute",
        "SimpleConjunctiveRefute", "SimpleConjunctiveNoRefute", "MultiLevelParamPassRefute", "MultiLevelParamPassNoRefute",
        "StartInLoopNoRefute", "CallInLoopHeadRefute", "CallInLoopHeadNoRefute", "LoopProcRefute", "LoopProcNoRefute",
        "ForEachLoopRefute", "ForEachLoopNoRefute", "InfiniteLoopRefute", "StraightLineCaseSplitNoRefute", "ManuLoopNoRefute",
        "CallPruningNoRefute", "SingletonNoRefute", "ForEachLoopArrRefute", "CheckCastNoRefute" };

    // tests that we expect to fail under piecewise execution
    final Set<String> piecewiseExceptions = HashSetFactory.make(); //new HashSet<String>();
    piecewiseExceptions.add("SimpleDynamicDispatchRefute");
    piecewiseExceptions.add("NullRefute");
    piecewiseExceptions.add("SimpleDisjunctiveRefute");
    piecewiseExceptions.add("SimpleConjunctiveRefute");
    piecewiseExceptions.add("MultiLevelParamPassRefute");

    final String[] realHashMapTests = new String[] { "SimpleHashMapRefute", "SimpleHashMapNoRefute", "ContainsKeyRefute",
        "ContainsKeyNoRefute" };
    
    final String[] fakeMapTests0 = new String[] {};
    //final String[] fakeMapTests0 = new String[] { "ManuLoopNoRefute" };

    //final String[] realHashMapTests0 = new String[] { };
    final String[] realHashMapTests0 = new String[] { "SimpleHashMapRefute" };

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
      // HACK: tests that we aren't meant to refute have NoRefute in name 
      if (test.contains("NoRefute")) {
        expectedResult = true; 
      }
       
      // some tests are expected not to pass with piecewise execution
      if (Options.PIECEWISE_EXECUTION && piecewiseExceptions.contains(test)) {
        result = !result;
      }

      if (result == expectedResult) {
        Util.Print("Test " + test + " (# " + (testNum++) + ") passed!");
        successes++;
      } else {
        Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
        failures++;
        if (Options.EXIT_ON_FAIL)
          System.exit(1);
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
      if (test.contains("NoRefute"))
        expectedResult = true; // HACK: tests that we aren't meant to refute
                               // have NoRefute in name
      if (result == expectedResult) {
        Util.Print("Test " + test + " (# " + (testNum++) + ") passed!");
        successes++;
      } else {
        Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
        failures++;
        if (Options.EXIT_ON_FAIL)
          System.exit(1);
      }
      long testEnd = System.currentTimeMillis();
      Util.Print("Test took " + ((testEnd - testStart) / 1000) + " seconds");
      WALACFGUtil.clearCaches();
    }

    long end = System.currentTimeMillis();
    Util.Print("All android tests complete in " + ((end - start) / 1000) + " seconds");
    Util.Print(successes + " tests passed, " + failures + " tests failed.");
  }
  
  public static void runImmutabilityRegressionTests() throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
    CallGraphBuilderCancelException {
    Options.DACAPO = true;

    final String[] immutabilityTests = new String[] { "BasicImmutableRefute", "BasicImmutableNoRefute", "HeapRefute", "HeapNoRefute",
                                                       "ArrayRefute", "ArrayNoRefute", "ArrayLoopRefute", "ArrayLoopNoRefute",
                                                       "MapRefute", "MapNoRefute" }; 
    
    // need call stack depth of at least 3 to refute some of these tests
    if (Options.MAX_CALLSTACK_DEPTH < 3) Options.MAX_CALLSTACK_DEPTH = 3;
    
    String regressionDir = "apps/tests/immutability/";
    boolean result;
    int testNum = 0;
    int successes = 0;
    int failures = 0;
    long start = System.currentTimeMillis();
    
    final String[] tests0 = { "MapNoRefute" };

    for (String test : immutabilityTests) {
    //for (String test : tests) {
      Util.Print("Running test " + testNum + ": " + test);
      long testStart = System.currentTimeMillis();
      try {
        result = runImmutabilityCheck(regressionDir + test);
      } catch (Exception e) {
        Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
        throw e;
      }
      Util.clear();

      boolean expectedResult = false;
      // HACK: tests that we aren't meant to refute have NoRefute in name 
      if (test.contains("NoRefute")) {
        expectedResult = true; 
      }

      if (result == expectedResult) {
        Util.Print("Test " + test + " (# " + (testNum++) + ") passed!");
        successes++;
      } else {
        Util.Print("Test " + test + " (#" + (testNum++) + ") failed :(");
        failures++;
        if (Options.EXIT_ON_FAIL)
          System.exit(1);
      }
      long testEnd = System.currentTimeMillis();
      Util.Print("Test took " + ((testEnd - testStart) / 1000) + " seconds.");
      WALACFGUtil.clearCaches();
    }
    
    long end = System.currentTimeMillis();
    Util.Print("All immutability tests complete in " + ((end - start) / 1000) + " seconds");
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
        // if (scope.isApplicationLoader(subclass.getClassLoader())) {
        subclasses.add(subclass);
        if (Options.DEBUG)
          Util.Debug("Found subclass class " + subclass);
        // }
      }

      for (IClass c : subclasses) { // for each subclass
        Collection<IField> fields = c.getAllStaticFields();
        for (IField f : fields) { // for each static field in the class
          if (isInteresting(f)) {
            if (Options.DEBUG)
              Util.Debug("Found static field " + f.toString());
            staticFields.add(f);
          }
        }
      }
    }
  }

  public static boolean runAnalysisAllStaticFields(String appName) // wrapper
      throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
    // String[] snkClasses = new String[] { "Landroid/app/Activity",
    // "Landroid/view/View"};
    String[] snkClasses = new String[] { "Landroid/app/Activity" };
    String[] srcClasses = new String[0]; // with no base
    return runAnalysis(appName, srcClasses, snkClasses, false);
  }

  public static boolean runAnalysisActivityAndViewFieldsOnly(String appName) // wrapper
      throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
    String[] srcClasses = new String[] { "Landroid/app/Activity", "Landroid/view/View" };
    String[] snkClasses = new String[] { "Landroid/app/Activity" };
    return runAnalysis(appName, srcClasses, snkClasses, false);
  }

  public static boolean runAnalysisActivityFieldsOnly(String appName) // wrapper
      throws IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException {
    return runAnalysisActivityFieldsOnly(appName, false, false);
  }

  public static boolean runAnalysisActivityFieldsOnly(String appName, boolean fakeAct, boolean fakeMap) // wrapper
      throws FileNotFoundException, IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    if (fakeAct)
      return runAnalysis(appName, "LAct", fakeMap);
    else
      return runAnalysis(appName, "Landroid/app/Activity", fakeMap);
  }

  public static boolean runAnalysis(String appName, String baseClass, boolean fakeMap) // wrapper
      throws FileNotFoundException, IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    String[] singleton = new String[] { baseClass };
    return runAnalysis(appName, singleton, singleton, fakeMap);
  }
  
  private static IClassHierarchy setupAndroidScopeAndEntryPoints(AnalysisScope scope, 
                                                                 Collection<Entrypoint> entryPoints, 
                                                                 Map<String,String> buttonNamesMap, 
                                                                 String appPath) 
      throws IOException, ClassHierarchyException {
    scope.addToScope(scope.getPrimordialLoader(), new JarFile(JVM_PATH));
    scope.addToScope(scope.getPrimordialLoader(), new JarFile(Options.ANDROID_JAR));
    scope.addToScope(scope.getApplicationLoader(), new BinaryDirectoryTreeModule(new File(appPath)));
    Util.Print("Building class hierarchy");
    IClassHierarchy cha = ClassHierarchy.make(scope);
    Iterator<IClass> classes = cha.iterator();
    Set<String> handlers = buttonNamesMap.keySet();
    
    while (classes.hasNext()) {
      IClass c = classes.next();
       // only application methods should be entrypoints
      if (!scope.isApplicationLoader(c.getClassLoader())) continue;

      Collection<? extends IClass> implementedInterfaces = c.getDirectInterfaces();
      Set<String> possibleOverrides = HashSetFactory.make();
      for (IClass clazz : implementedInterfaces) {
        // only care about overrides from primordial scope. overrides of these methods
        // may be directly callable by the android system. if this method is an override
        // of a method in the Application scope, we should figure out that it is a 
        // potential event handler in some other way
        if (clazz.getClassLoader().getReference().equals(ClassLoaderReference.Primordial)) {
          for (IMethod m : clazz.getAllMethods()) {
            if (!m.isInit() && !m.isStatic()) {
              possibleOverrides.add(m.getName().toString() + m.getDescriptor().toString());
            }
          }
        }
      }
      
      for (IMethod m : c.getDeclaredMethods()) { // for each method defined in the class
        // if this method has a name that looks like an event handler...
        if (((m.isPublic() || m.isProtected()) && m.getName().toString().startsWith("on")) ||
            handlers.contains(m.getName().toString()) || // ... or this method was declared as a custom handler
            possibleOverrides.contains(m.getName().toString() +
                m.getDescriptor().toString())) { // or this method is an override of an interface method
          //entryPoints.add(new DefaultEntrypoint(m, cha));
          entryPoints.add(new SameReceiverEntrypoint(m, cha));
          //Util.Print("adding entrypoint " + m);
        }
      }
    }
    return cha;
  }
  
  // wrapper
  private static AbstractDependencyRuleGenerator 
  buildCallGraphAndPointsToAnalysis(AnalysisScope scope, IClassHierarchy cha, 
                                    Collection<Entrypoint> entryPoints, String appPath) 
    throws CallGraphBuilderCancelException {
    return buildCallGraphAndPointsToAnalysis(scope, cha, entryPoints, appPath, false);
  }
  
  /**
   * build callgraph, points-to analysis, and mod/ref for given entrypoints
   * @return an abstract dependency rule generator containing this components
   */
  private static AbstractDependencyRuleGenerator 
      buildCallGraphAndPointsToAnalysis(AnalysisScope scope, IClassHierarchy cha, 
                                        Collection<Entrypoint> entryPoints, String appPath, boolean fakeMap) 
      throws CallGraphBuilderCancelException {
    Collection<? extends Entrypoint> e = entryPoints;
    AnalysisOptions options = new AnalysisOptions(scope, e); 
    // turn off handling of Method.invoke(), which dramatically speeds up pts-to analysis
    options.setReflectionOptions(ReflectionOptions.NO_METHOD_INVOKE); 
    AnalysisCache cache = new AnalysisCache();
    // cache, cha, scope);
    CallGraphBuilder builder;
    if (!fakeMap) builder = com.ibm.wala.ipa.callgraph.impl.Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);
    else builder = FakeMapContextSelector.makeZeroOneFakeMapCFABuilder(options, cache, cha, scope);
    if (Options.DEBUG) DEBUG_cha = cha;
    Util.Print("Building call graph");
    CallGraph cg = builder.makeCallGraph(options, null);
    Util.Print(CallGraphStats.getStats(cg));
    Util.Print("Building points-to analysis");
    PointerAnalysis pointerAnalysis = builder.getPointerAnalysis();
    HeapGraph hg = new HeapGraphWrapper(pointerAnalysis, cg);
    HeapModel hm = pointerAnalysis.getHeapModel();
    Util.Print("Building mod/ref");
    ModRef modref = ModRef.make();
    Map<CGNode, OrdinalSet<PointerKey>> modRefMap = modref.computeMod(cg, pointerAnalysis);
    return new AbstractDependencyRuleGenerator(cg, hg, hm, cache, modRefMap);
  }
  
  public static void runAndroidBadMethodCheck(String appPath) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
    Map<String,String> buttonNamesMap = AndroidUtils.parseButtonInfo(appPath + "res/");
    IClassHierarchy cha = setupAndroidScopeAndEntryPoints(scope, entryPoints, buttonNamesMap, appPath);
    
    AbstractDependencyRuleGenerator depRuleGenerator = buildCallGraphAndPointsToAnalysis(scope, cha, entryPoints, appPath);
    CallGraph cg = depRuleGenerator.getCallGraph();
    
    final MethodReference TAKE_PIC0 = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/hardware/Camera"),
        "takePicture", "(Landroid/hardware/Camera$ShutterCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;)V");
    final MethodReference TAKE_PIC1 = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/hardware/Camera"),
        "takePicture", "(Landroid/hardware/Camera$ShutterCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;)V");
    final MethodReference RECORD_AUDIO = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/media/MediaRecorder"),
        "start", "()V");
    final MethodReference[] badMethods = new MethodReference[] { TAKE_PIC0, TAKE_PIC1, RECORD_AUDIO };
    
    Set<String> buttonHandlers = buttonNamesMap.keySet();
    // set of all methods that are triggered when a button is clicked
    Set<IMethod> buttonMethods = HashSetFactory.make();
    for (Entrypoint point : entryPoints) {
      IMethod method = point.getMethod();
      if (buttonHandlers.contains(method.getName().toString())) {
        buttonMethods.add(method);
      }
    }

    Set<String> warnings = HashSetFactory.make();
    
    // try to find a corresponding button action for each invocation of a "bad" method
    for (MethodReference badMethod : badMethods) { // for each bad method
      Set<CGNode> nodes = cg.getNodes(badMethod);
      for (CGNode badNode : nodes) { // for each node a bad method resolves to
        for (IMethod buttonMethod : buttonMethods) {
          Set<CGNode> reachable = DFS.getReachableNodes(cg, cg.getNodes(buttonMethod.getReference()));
          if (reachable.contains(badNode)) {
            String buttonLabel = buttonNamesMap.get(buttonMethod.getName().toString());
            warnings.add("Sensitive method " + badMethod.getDeclaringClass() + "." + badMethod.getName() + 
                         " triggered by button with label \"" + buttonLabel + "\"; is this ok?");
          } else {
            warnings.add("Couldn't find any button that triggers sensitive method " + 
                          badMethod.getDeclaringClass() + "." + badMethod.getName() + "; is this ok?");
          }
        }
      }
    }
    
    for (String warning : warnings) Util.Print("Warning: " + warning);
  }
  
  public static boolean runImmutabilityCheck(String appPath) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    final MethodReference UNMODIFIABLE_COLLECTION = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/util/Collections"), 
                                     "unmodifiableCollection", "(Ljava/util/Collection;)Ljava/util/Collection;");
    
    final MethodReference UNMODIFIABLE_LIST = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/util/Collections"), 
                                     "unmodifiableList", "(Ljava/util/List;)Ljava/util/List;");
    
    final MethodReference UNMODIFIABLE_MAP = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/util/Collections"), 
                                     "unmodifiableMap", "(Ljava/util/Map;)Ljava/util/Map;");
    
    final MethodReference UNMODIFIABLE_SET = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/util/Collections"), 
                                     "unmodifiableSet", "(Ljava/util/Set;)Ljava/util/Set;");
    
    final MethodReference UNMODIFIABLE_SORTED_MAP = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/util/Collections"), 
                                     "unmodifiableSortedMap", "(Ljava/util/SortedMap;)Ljava/util/SortedMap;");
    
    final MethodReference UNMODIFIABLE_SORTED_SET = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/util/Collections"), 
                                     "unmodifiableSortedSet", "(Ljava/util/SortedSet;)Ljava/util/SortedSet;");
    
    MethodReference[] unmodifiableContainers = new MethodReference[] { UNMODIFIABLE_COLLECTION, UNMODIFIABLE_LIST, UNMODIFIABLE_MAP,
                                                                       UNMODIFIABLE_SET, UNMODIFIABLE_SORTED_MAP, 
                                                                       UNMODIFIABLE_SORTED_SET };
    
    // TODO: hack; should get full names. 
    String[] badMethods = new String[] { "add", "addAll", "clear", "remove", "removeAll", "retainAll", "set", "put", "putAll" };
    
    AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
    IClassHierarchy cha;
    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
    
    if (REGRESSIONS) {
      scope.addToScope(scope.getPrimordialLoader(), new JarFile(JVM_PATH));
      scope.addToScope(scope.getApplicationLoader(), new BinaryDirectoryTreeModule(new File(appPath)));
      cha = ClassHierarchy.make(scope);
      
      final MethodReference MAIN =
          MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "LMain"), 
              "main", "([Ljava/lang/String;)V");
      entryPoints.add(new DefaultEntrypoint(MAIN, cha));
    } else if (Options.DACAPO) { // running one of the Dacapo benchmarks
      String appName;
      // removing trailing slash if needed
      if (appPath.endsWith("/")) appName = appPath.substring(0, appPath.length() - 1);
      else appName = appPath;
      // strip of front of path away from app name
      appName = appName.substring(appName.lastIndexOf("/") + 1);
      Util.Print("Running on " + appName);
      JarFile appJar = new JarFile(appPath + "/" + appName + ".jar");
      JarFile appDepsJar = new JarFile(appPath + "/" + appName + "-deps.jar");
      scope.addToScope(scope.getPrimordialLoader(), new JarFile(JVM_PATH));
      scope.addToScope(scope.getPrimordialLoader(), appDepsJar);
      scope.addToScope(scope.getApplicationLoader(), appJar);
      
      final MethodReference DACAPO_MAIN =
          MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Ldacapo/" + appName + "/Main"), 
              "main", "([Ljava/lang/String;)V");
      
      cha = ClassHierarchy.make(scope);
      entryPoints.add(new DefaultEntrypoint(DACAPO_MAIN, cha));
      
    } else { // running an android app
      Map<String,String> buttonNamesMap = AndroidUtils.parseButtonInfo(appPath + "res/");
      cha = setupAndroidScopeAndEntryPoints(scope, entryPoints, buttonNamesMap, appPath);
    }

    int creatorNodes = 0, creatorSites = 0, creatorCalls = 0;
    
    AbstractDependencyRuleGenerator depRuleGenerator = buildCallGraphAndPointsToAnalysis(scope, cha, entryPoints, appPath);
    CallGraph cg = depRuleGenerator.getCallGraph();
    
    Util.Print("Starting immutability check");
    
    boolean errs = false;
    
    // list of instance keys corresponding to unmodifiable containers
    for (int i = 0; i < unmodifiableContainers.length; i++) { // for each type of unmodifiable container
      Set<CGNode> nodes = cg.getNodes(unmodifiableContainers[i]);
      for (CGNode node : nodes) { // for each method that creates an unmodifiable container
        Iterator<CGNode> preds = cg.getPredNodes(node);
        while (preds.hasNext()) { // for each caller of such a method
          creatorNodes++;
          CGNode pred = preds.next();
          IR ir = pred.getIR();
          SSAInstruction[] instrs = ir.getInstructions();
          Iterator<CallSiteReference> sites = cg.getPossibleSites(pred, node);
          while (sites.hasNext()) { // for each call site that creates an unmodifiable container
            creatorSites++;
            CallSiteReference site = sites.next();
            IntSet indices = ir.getCallInstructionIndices(site);
            IntIterator indexIter = indices.intIterator();
            while (indexIter.hasNext()) { // for each invocation of a call site
              creatorCalls++;
              int callIndex = indexIter.next();
              Util.Assert(instrs[callIndex] instanceof SSAInvokeInstruction);
              SSAInvokeInstruction instr = (SSAInvokeInstruction) instrs[callIndex];              
              Util.Assert(instr.getNumberOfParameters() == 1); // should take single container as param
              Util.Assert(instr.hasDef()); // should return ptr to unmodifiable container
              
              errs = checkForBadMethodCalls(pred, instr, depRuleGenerator, badMethods) || errs;
              //checkAllFields(pred, instr, hm, hg, cha, cg, logger, depRuleGenerator);
              
            }         
          }
        }
      }
    }
    return errs;
    //Util.Print(creatorNodes + " creator nodes, " + creatorSites + " creator sites, " + creatorCalls + " creator calls.");
  }
  
  // check the object instance corresponding to the unmodifiable container to see if 
  // any bad methods are called on it. this is an overapproximation of the dynamic check
  public static boolean checkForBadMethodCalls(CGNode node, SSAInstruction instr, AbstractDependencyRuleGenerator depRuleGenerator,
                                             String[] badMethods) {
    Util.Print("Checking for bad method calls");
    HeapModel hm = depRuleGenerator.getHeapModel();
    HeapGraph hg = depRuleGenerator.getHeapGraph();
    CallGraph cg = depRuleGenerator.getCallGraph();
    Logger logger = new Logger();
    
    // get local ptr to the unmodifiable container
    PointerKey unmodifiableLocal = hm.getPointerKeyForLocal(node, instr.getDef());
    Iterator<Object> unmodifiableHeapLocs = hg.getSuccNodes(unmodifiableLocal);
    
    Set<PointsToEdge> toWitness = HashSetFactory.make();
    boolean errs = false;
    while (unmodifiableHeapLocs.hasNext()) { // for each heap loc the local may point to
      Object next = unmodifiableHeapLocs.next();
      Util.Assert(next instanceof InstanceKey);
      Iterator<Object> localPtrs = hg.getPredNodes(next);
      while (localPtrs.hasNext()) { // for each local that may point at the heap local
        Object localPtr = localPtrs.next();
        if (localPtr instanceof LocalPointerKey) {
          Util.Assert(localPtr instanceof LocalPointerKey, "bad ptr " + localPtr);
          LocalPointerKey local = (LocalPointerKey) localPtr;
          IMethod method = local.getNode().getMethod();
          if (method.isStatic()) {
            // static methods have no receivers
            continue; 
          }
          if (local.isParameter() && local.getValueNumber() == 1) {
            // "immutable" local is receiver to a method...make sure this function 
            // is not one of the bad ones
            String methodName = method.toString();
            for (String badMethod : badMethods) { // for each bad method 
              if (methodName.contains(badMethod)) {
                CGNode localNode = local.getNode();
                Iterator<CGNode> preds = cg.getPredNodes(localNode);
                while (preds.hasNext()) { // for each node a bad method resolves to
                  CGNode pred = preds.next();
                  //Util.Print(pred.getIR().toString());
                  SSAInstruction[] instrs = pred.getIR().getInstructions();
                  Iterator<CallSiteReference> siteIter = cg.getPossibleSites(pred, localNode);
                  while (siteIter.hasNext()) { // for each call site of a bad method
                    CallSiteReference site = siteIter.next();
                    IR predIR = pred.getIR();
                    IntSet indices = predIR.getCallInstructionIndices(site);
                    IntIterator indexIter = indices.intIterator();
                    while (indexIter.hasNext()) { // for each index of a bad call site
                      int callLine = indexIter.next();
                      SSAInstruction callInstr = instrs[callLine];
                      Util.Assert(callInstr instanceof SSAInvokeInstruction);
                      //SSAInvokeInstruction invoke = (SSAInvokeInstruction) callInstr;
                      Util.Print("bad call " + callInstr);
                      Util.Print("bad call; unmodifiable reference created in " + node + " may flow to " +
                                 callInstr);
                      // query: can the receiver point to a supposedly "immutable" instance key at the time of
                      // the call to the bad method?
                      PointerVariable receiver = Util.makePointerVariable(
                          hm.getPointerKeyForLocal(pred, callInstr.getUse(0)));
                      PointerVariable immutableInstanceKey = Util.makePointerVariable(next);
                      
                      PointsToEdge witnessMe = new PointsToEdge(receiver, immutableInstanceKey);
                      Util.Print("witnessMe: " + witnessMe);
                      toWitness.add(witnessMe);

                      final IQuery query = new CombinedPathAndPointsToQuery(witnessMe, depRuleGenerator);
                      SSACFG cfg = predIR.getControlFlowGraph();
                      SSACFG.BasicBlock startBlk = cfg.getBlockForInstruction(callLine);
                      int startLineBlkIndex = WALACFGUtil.findInstrIndexInBlock(callInstr, startBlk);
                      Util.Assert(startBlk.getAllInstructions().get(startLineBlkIndex).equals(callInstr), "instrs dif! expected "
                          + callInstr + "; found " + startBlk.getAllInstructions().get(startLineBlkIndex));
                      ISymbolicExecutor exec = new OptimizedPathSensitiveSymbolicExecutor(cg, logger);
                      // start at line BEFORE the call
                      boolean foundWitness = exec.executeBackward(pred, startBlk, startLineBlkIndex - 1, query);
                      Util.Print("witnessed? " + foundWitness);
                      errs = foundWitness || errs;
                    }
                  }
                }
              }
            }
          }
        }
      }
    } 
    return errs;
  }
  
  public static void checkAllFields(CGNode node, SSAInstruction instr, HeapModel hm, HeapGraph hg, IClassHierarchy cha, 
                                    CallGraph cg, Logger logger, AbstractDependencyRuleGenerator depRuleGenerator) {
    // get param that points to unmodifiable container
    PointerKey lpk = hm.getPointerKeyForLocal(node, instr.getUse(0));
    // get the possible heap locations that the param might point to
    Iterator<Object> succs = hg.getSuccNodes(lpk);
    while (succs.hasNext()) { // for each heap loc that might be converted into an unmodifiable container
      Object succ = succs.next();
      PointerVariable lhs = Util.makePointerVariable(succ);
      Util.Assert(succ instanceof InstanceKey);
      // get all the fields of this heap location
      Iterator<Object> fields = hg.getSuccNodes(succ);
      while (fields.hasNext()) { // for each field of the heap loc
        Object fld = fields.next();
        Util.Assert(fld instanceof InstanceFieldKey);
        InstanceFieldKey field = (InstanceFieldKey) fld;
        Util.Print("FIELD is " + field);
        Set<InstanceKey> fieldSuccsSet = HashSetFactory.make();
        Iterator<Object> fieldSuccs = hg.getSuccNodes(field);
        // if field doesn't point to anything, this is trivially provable
        Util.Assert(fieldSuccs.hasNext());
        while (fieldSuccs.hasNext()) { // for each successor of the field
          Object fieldSucc = fieldSuccs.next();
          Util.Print("field succ " + fieldSucc);
          Util.Assert(fieldSucc instanceof InstanceKey);
          fieldSuccsSet.add((InstanceKey) fieldSucc);
        }
        // <immutable loc>.f -> {all things that <immutable loc>.f might point to}
        // for each write that might occur *after* the construction of the immutable
        // container, we must refute this edge
        PointsToEdge toRefute = new PointsToEdge(lhs, SymbolicPointerVariable.makeSymbolicVar(fieldSuccsSet),
                                                 field.getField());
        Util.Print("to refute " + toRefute);
        boolean witnessed = generateWitness(toRefute, depRuleGenerator, logger);
        Util.Print("witnessed? " + witnessed);
      }
    }
  }

  public static void runSynthesizer(String appPath) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
    JarFile androidJar = new JarFile(Options.ANDROID_JAR);
    // add Android code
    scope.addToScope(scope.getPrimordialLoader(), androidJar);
    // add application code
    scope.addToScope(scope.getApplicationLoader(), new BinaryDirectoryTreeModule(new File(appPath)));
    
    IClassHierarchy cha = ClassHierarchy.make(scope);
    Iterator<IClass> classes = cha.iterator();
    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
    while (classes.hasNext()) {
      IClass c = classes.next();
      if (!scope.isApplicationLoader(c.getClassLoader())) continue;
      // TODO: should be getAllMethods()?
      for (IMethod m : c.getDeclaredMethods()) { // for each method in the class
        // consider public methods to be entrypoints
        if (m.isPublic() || m.isProtected()) {
          entryPoints.add(new DefaultEntrypoint(m, cha));
          //entryPoints.add(new SameReceiverEntrypoint(m, cha));
        }
      }
    }    
    // build callgraph and pointer analysis
    Collection<? extends Entrypoint> e = entryPoints;

    AnalysisOptions options = new AnalysisOptions(scope, e); 
    // turn off handling of Method.invoke(), which dramatically speeds up pts-to analysis
    options.setReflectionOptions(ReflectionOptions.NO_METHOD_INVOKE); 
    AnalysisCache cache = new AnalysisCache();
    CallGraphBuilder builder = 
        com.ibm.wala.ipa.callgraph.impl.Util.makeZeroOneCFABuilder(options,cache, cha, scope);
    if (Options.DEBUG) Util.Debug("building call graph");
    CallGraph cg = builder.makeCallGraph(options, null);
    // if (CALLGRAPH_PRUNING) expandedCallgraph = ExpandedCallgraph.make(cg);
    Util.Print(CallGraphStats.getStats(cg));
    PointerAnalysis pointerAnalysis = builder.getPointerAnalysis();
    HeapGraph hg = new HeapGraphWrapper(pointerAnalysis, cg);
    HeapModel hm = pointerAnalysis.getHeapModel();
    ModRef modref = ModRef.make();
    Map<CGNode, OrdinalSet<PointerKey>> modRefMap = modref.computeMod(cg, pointerAnalysis);
    
    final MethodReference ASSERT_PT_NULL = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "LAssertions"), 
                                     "Unmodifiable", "(Ljava/lang/Object;Ljava/lang/String;)V");

    Logger logger = new Logger();
    AbstractDependencyRuleGenerator depRuleGenerator = 
        new AbstractDependencyRuleGenerator(cg, hg, hm, cache, modRefMap);
    
    
    // collect assertions
    CGNode fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(cg);
    Iterator<CGNode> clinits = cg.getSuccNodes(fakeWorldClinit);
    while (clinits.hasNext()) { // for each class initializer
      CGNode clinit = clinits.next();
      IR clinitIr = clinit.getIR();
      SymbolTable tbl = clinitIr.getSymbolTable();
      Iterator<CallSiteReference> calls = clinit.iterateCallSites();
      while (calls.hasNext()) { // for each method called in the clinit
        CallSiteReference call = calls.next();
        if (call.getDeclaredTarget() == ASSERT_PT_NULL) {    
          SSAAbstractInvokeInstruction[] callInstrs = clinitIr.getCalls(call);
          for (int i = 0; i < callInstrs.length; i++) {
            Util.Print(callInstrs[i].toString());
            // local pointer pointing at the base loc
            PointerKey baseLoc = hm.getPointerKeyForLocal(clinit, callInstrs[i].getUse(0));
            Iterator<Object> succs = hg.getSuccNodes(baseLoc);
            Util.Assert(succs.hasNext());
            Object succ = succs.next();
            Util.Assert(!succs.hasNext(), "only expecting on obj to flow here");
            String fieldName = tbl.getStringValue(callInstrs[i].getUse(1));
            Util.Print(succ + "." + fieldName);
            Iterator<Object> fields = hg.getSuccNodes(succ);
            Set<InstanceKey> possibleVals = HashSetFactory.make();
            PointerVariable lhs = Util.makePointerVariable(succ);
            PointsToEdge edge = null;
            while (fields.hasNext()) {
              Object field = fields.next();
              if (field instanceof InstanceFieldKey) {
                InstanceFieldKey fieldKey = (InstanceFieldKey) field;
                if (fieldName.equals(fieldKey.getField().getName().toString())) {
                  Iterator<Object> fieldSuccs = hg.getSuccNodes(field);
                  while (fieldSuccs.hasNext()) {
                    possibleVals.add((InstanceKey) fieldSuccs.next());
                  }
                  PointerVariable rhs = SymbolicPointerVariable.makeSymbolicVar(possibleVals);
                  edge = new PointsToEdge(lhs, rhs, fieldKey.getField());
                  break;
                }
              } else if (field instanceof ArrayContentsKey) {
                if (fieldName.equals("contents")) {
                  Iterator<Object> fieldSuccs = hg.getSuccNodes(field);
                  while (fieldSuccs.hasNext()) {
                    possibleVals.add((InstanceKey) fieldSuccs.next());
                  }
                  PointerVariable rhs = SymbolicPointerVariable.makeSymbolicVar(possibleVals);
                  edge = new PointsToEdge(lhs, rhs, AbstractDependencyRuleGenerator.ARRAY_CONTENTS);
                  Util.Print("edge " + edge);
                  break;
                }
              } else Util.Unimp("bad field!");
            }
            Util.Assert(edge != null);
            
            Set<DependencyRule> producers = Util.getProducersForEdge(edge, depRuleGenerator);
            for (DependencyRule producer : producers) {
              Util.Print("producer " + producer);
              PointerStatement snkStmt = producer.getStmt();
              int startLine = snkStmt.getLineNum();
              //PointsToQuery ptQuery = new PointsToQuery(producer, depRuleGenerator);
              
              //final IQuery query = new CombinedPathAndPointsToQuery(ptQuery);
              final IQuery query = new CombinedPathAndPointsToQuery(producer, depRuleGenerator);
              IR ir = producer.getNode().getIR();
              SSACFG cfg = ir.getControlFlowGraph();
              SSACFG.BasicBlock startBlk = cfg.getBlockForInstruction(startLine);
              int startLineBlkIndex = WALACFGUtil.findInstrIndexInBlock(snkStmt.getInstr(), startBlk);
              Util.Assert(startBlk.getAllInstructions().get(startLineBlkIndex).equals(snkStmt.getInstr()), "instrs dif! expected "
                  + snkStmt.getInstr() + "; found " + startBlk.getAllInstructions().get(startLineBlkIndex));
              
              ISymbolicExecutor exec;
              boolean foundWitness;
              exec = new OptimizedPathSensitiveSymbolicExecutor(cg, logger);
              // start at line BEFORE snkStmt
              foundWitness = exec.executeBackward(producer.getNode(), startBlk, startLineBlkIndex - 1, query);
              Util.Print("witness? " + foundWitness);
            }
          }
        }
      }
    }
  }
  
  /**
   * run Thresher on app
   * 
   * @param appName - path to app to run
   * @param baseClasses - classes whose static fields we should search from and classes whose instances should not be reachable
   * from a static field
   * @param fakeMap - debug parameter; should be false for all real uses
   * @return - true if no instance of the base classes is reachable from a static field of the base class, false otherwise
   */
  public static boolean runAnalysis(String appPath, String[] srcStrings, String[] snkStrings, boolean fakeMap) 
      throws FileNotFoundException, IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
    Set<IField> staticFields = HashSetFactory.make();
    Set<MethodReference> saveMethods = HashSetFactory.make();
    Util.Print("Starting on " + appPath);
    Logger logger = new Logger();
    long start = System.currentTimeMillis();
    AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
    if (Options.USE_EXCLUSIONS) {
      File exclusionsFile = new File("config/exclusions.txt");
      if (exclusionsFile != null) scope.setExclusions(FileOfClasses.createFileOfClasses(exclusionsFile));
    }
    JarFile androidJar = new JarFile(Options.ANDROID_JAR);
    // add Android code
    scope.addToScope(scope.getPrimordialLoader(), androidJar);
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
          // add "on*" methods; they're the event handlers
          if ((m.isPublic() || m.isProtected()) && m.getName().toString().startsWith("on")) {
            // use same receiver for all method calls
            entryPoints.add(new SameReceiverEntrypoint(m, cha));
          }
        }
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
    
    
    AbstractDependencyRuleGenerator depRuleGenerator = buildCallGraphAndPointsToAnalysis(scope, cha, entryPoints, appPath, fakeMap);
    HeapGraphWrapper hg = (HeapGraphWrapper) depRuleGenerator.getHeapGraph();
    HeapModel hm = depRuleGenerator.getHeapModel();
   
    Set<Pair<Object, Object>> fieldErrorList = HashSetFactory.make();
    // map from fields -> Acts that leak via that field
    Map<String, Set<IClass>> leakedActivities = HashMapFactory.make();

    for (IField f : staticFields) {
      boolean skipThis = false;
      for (String skip : blacklist) {
        if (f.toString().contains(skip)) {
          Util.Print("skipping " + f + " due to blacklist");
          skipThis = true;
          break;
        }
      }
      if (skipThis)
        continue;

      PointerKey field = hm.getPointerKeyForStaticField(f);
      BFSIterator<Object> iter = new BFSIterator<Object>(hg, field);
      // see if an Activity is reachable from this static field
      while (iter.hasNext()) {
        Object node = iter.next();
        IClass type = null;
        if (node instanceof ConcreteTypeKey) {
          type = ((ConcreteTypeKey) node).getConcreteType();
        } else if (node instanceof AllocationSiteInNode) {
          type = ((AllocationSiteInNode) node).getConcreteType();
        }
        // allow arbitrary number of errors per field
        if (type != null && subclasses.contains(type)) {
          // is there a path from the static field to the Activity?
          if (findNewErrorPath(hg, field, node, cha) != null) {
            Set<IClass> leaked = leakedActivities.get(field.toString());
            if (leaked == null) {
              leaked = HashSetFactory.make();
              leakedActivities.put(field.toString(), leaked);
              Util.Print("found field error " + field);
              logger.logErrorField();
            }
            InstanceKey activityInstance = (InstanceKey) node;
            // see if we already know that this Activity can leak via this field
            if (leaked.add(activityInstance.getConcreteType())) { 
              Pair<Object, Object> errPair = Pair.make((Object) field, node);
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
      result = refuteFieldErrors(fieldErrorList, depRuleGenerator, logger);
    }
    long refuteEnd = System.currentTimeMillis();
    Util.Print("Symbolic execution completed in " + ((refuteEnd - refuteStart) / 1000.0) + " seconds");
    Util.Print("Total time was " + ((refuteEnd - start) / 1000.0) + " seconds");
    Util.Print("Done with " + appPath);
    return result;
  }

  public static boolean refuteFieldErrors(Set<Pair<Object, Object>> fieldErrors, AbstractDependencyRuleGenerator aDepRuleGenerator, Logger logger) {
    List<Pair<Object, Object>> trueErrors = new LinkedList<Pair<Object, Object>>(), falseErrors = new LinkedList<Pair<Object, Object>>();
    Set<PointsToEdge> producedEdges = HashSetFactory.make(), refutedEdges = HashSetFactory.make();
    //AbstractDependencyRuleGenerator aDepRuleGenerator = new AbstractDependencyRuleGenerator(cg, hg, hm, cache, modRef);

    int count = 1;
    Collection<Object> snkCollection = new LinkedList<Object>();

    // for each error
    for (Pair<Object, Object> error : fieldErrors) {
      try {
        Util.Print("starting on error " + count++ + " of " + fieldErrors.size() + ": " + error.fst);
        snkCollection.add(error.snd);
        // if we can refute error
        if (refuteFieldErrorForward(error, producedEdges, aDepRuleGenerator, 
                                    refutedEdges, logger)) {
          Util.Print("successfully refuted error path " + error);
          logger.logRefutedError();
          falseErrors.add(error);
        } else {
          Util.Print("successfully witnessed error path " + error);
          logger.logWitnessedError();
          logger.logWitnessedField(error.fst.toString());
          trueErrors.add(error);
        }
        //relation = finder.getIgnoreIfBoth();
      } catch (Exception e) {
        Util.Print("problem while examining " + error + ": " + e + " " + Util.printArray(e.getStackTrace()));
        logger.logFailure();
        Thread.dumpStack();
        if (Options.EXIT_ON_FAIL)
          System.exit(1);
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
  public static boolean refuteFieldErrorForward(Pair<Object, Object> error, Set<PointsToEdge> producedEdges, 
                          AbstractDependencyRuleGenerator aDepRuleGenerator, Set<PointsToEdge> refutedEdges,
                          Logger logger) {
    HeapGraphWrapper hg = (HeapGraphWrapper) aDepRuleGenerator.getHeapGraph();
    IClassHierarchy cha = aDepRuleGenerator.getClassHierarchy();
    List<Object> errorPath = findNewErrorPath(hg, error.fst, error.snd, cha); 
    if (errorPath == null) {
      Util.Print("Edges refuted on previous error preclude us from finding path! this error infeasible");
      return true;
    }
    // reverse list and print
    LinkedList<Object> newPath = new LinkedList<Object>();
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
          // src is intermediate point in points-to edge; either field name or
          // array contents
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
          Util.Assert(src instanceof InstanceKey || src instanceof StaticFieldKey,
              "Sink should always be concrete; is " + src.getClass() + ": " + src);
          if (src instanceof StaticFieldKey)
            fieldKey = (StaticFieldKey) src;
          PointerVariable source = Util.makePointerVariable(src);
          PointerVariable sink = Util.makePointerVariable(snk);
          PointsToEdge witnessMe = new PointsToEdge(source, sink, fieldKey);

          if (!producedEdges.contains(witnessMe)) {
            // for now, we insist on refuting *all* contexts for a given edge
            // the first time we see it
            // so if we refute an edge and then see it again in the error path,
            // we are seeing it again because the version we refuted
            // was in a different context. however, since we refute for all
            // contexts at once, we can refute this edge immediately
            // because we've already done so in the past)
            boolean witnessed;
            if (refutedEdges.contains(witnessMe)) {
              if (Options.DEBUG)
                Util.Debug("already refuted edge " + witnessMe);
              //srcFieldPairs = new LinkedList<Pair<InstanceKey, Object>>();
              witnessed = false;
            } else {
              if (Options.DEBUG)
                Util.Debug("ATTEMPTING TO REFUTE EDGE " + witnessMe);
              Util.Print("%%%%%%%%%%%%%%%%%Starting on edge " + witnessMe + "%%%%%%%%%%%%%%%%%");
              long start = System.currentTimeMillis();
              witnessed = generateWitness(witnessMe, aDepRuleGenerator, logger);
              Util.Print("Edge took " + ((System.currentTimeMillis() - start) / 1000.0) + " seconds.");
              WALACFGUtil.clearCaches();
            }
            if (witnessed) {
            //if (srcFieldPairs == null) {
              // edge produced, continue generating witnesses on this path
              Util.Print("Successfully produced " + witnessMe + "; done with " + (++witnessedCount) + " of " + errorPath.size());
              producedEdges.add(witnessMe);
              logger.logEdgeWitnessed();
            } else {
              // edge refuted
              witnessedCount = 0;
              refutedEdges.add(witnessMe);
              //IBinaryNaturalRelation ignoreIfBoth = finder.getIgnoreIfBoth();
              //finder = new BFSPathFinder<Object>(hg, error.fst, new CollectionFilter<Object>(snkCollection));
              //finder.setIgnoreIfBoth(ignoreIfBoth);
              if (fieldKey == null) {
                Util.Assert(false, "how can field key be null?");
                hg.addIgnoreEdge(src, snk);
              } else {
                hg.addIgnoreEdge(fieldKey, snk);
              }
              Util.Print("Successfully refuted edge " + witnessMe + "; now trying to find error path  without it");
              logger.logEdgeRefutation();
              
              errorPath = findNewErrorPath(hg, error.fst, error.snd, cha); 
              
              if (errorPath != null) {
                if (Options.DEBUG) Util.Debug("refuted edge, but err path still exists; size " + errorPath.size());
                newPath = new LinkedList<Object>();
                // reverse path
                for (Object edge : errorPath) {
                  newPath.addFirst(edge);
                  Util.Print(edge.toString());
                }
                errorPath = newPath;
              } else
                Util.Debug("no path found!");
              refutation = true;
              break;
            }
          } else {
            if (Options.DEBUG)
              Util.Debug("already produced " + witnessMe);
          }
          fieldKey = null;
          snkIndex = srcIndex;
          srcIndex++;
        } // end of producedEdges.contains(witnessMe) else block
      } // end of srcIndex < errorPath.size() witness generation loop
      if (!refutation) {
        // ended loop without a refutation; we have witnessed entire error path
        if (Options.DEBUG)
          Util.Debug("error is real! we have witnessed entire path");
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
   * @return - true if witness for edge witnessMe found, false otherwise
   */
  private static boolean generateWitness(PointsToEdge witnessMe,
      AbstractDependencyRuleGenerator depRuleGenerator, Logger logger) {
    CallGraph cg = depRuleGenerator.getCallGraph();
    final Set<PointsToEdge> toProduce = HashSetFactory.make();
    toProduce.add(witnessMe);

    // find potential last rule(s) applied in witness
    Iterator<PointsToEdge> setIter = toProduce.iterator();
    PointsToEdge produceMe = setIter.next();
    final Set<DependencyRule> lastApplied;
    if (Options.GEN_DEPENDENCY_RULES_EAGERLY)
      lastApplied = Util.getRulesProducingEdge(produceMe, depRuleGenerator);
    else
      lastApplied = Util.getProducersForEdge(produceMe, depRuleGenerator);
    Util.Print(lastApplied.size() + " potential starting points.");

    logger.logProducingStatementsForEdge(lastApplied.size());
    int lastRuleCounter = 1;
    for (DependencyRule lastRule : lastApplied) {
      Util.Print("starting on possible rule " + (lastRuleCounter++) + " of " + lastApplied.size() + "\n" + lastRule);
      Util.Assert(lastRule.getShown().symbEq(witnessMe), "rule does not produce edge");
      PointerStatement snkStmt = lastRule.getStmt();
      int startLine = snkStmt.getLineNum();
      if (Options.DEBUG) Util.Debug("start line is " + startLine);
      final Set<CGNode> potentialNodes = HashSetFactory.make();
      potentialNodes.add(lastRule.getNode());
      int numContexts = potentialNodes.size();

      Util.Print(potentialNodes.size() + " potential start nodes");
      
      for (CGNode startNode : potentialNodes) {
        Util.Assert(numContexts == potentialNodes.size(), "sizes don't match!");
        Util.Print("starting in method " + startNode);
        final IQuery query = new CombinedPathAndPointsToQuery(lastRule, depRuleGenerator);
        IR ir = startNode.getIR();
        Util.Debug(ir.toString());
        SSACFG cfg = ir.getControlFlowGraph();
        SSACFG.BasicBlock startBlk = cfg.getBlockForInstruction(startLine);
        int startLineBlkIndex = WALACFGUtil.findInstrIndexInBlock(snkStmt.getInstr(), startBlk);
        Util.Assert(startBlk.getAllInstructions().get(startLineBlkIndex).equals(snkStmt.getInstr()), "instrs dif! expected "
            + snkStmt.getInstr() + "; found " + startBlk.getAllInstructions().get(startLineBlkIndex));

        ISymbolicExecutor exec;
        boolean foundWitness;
        if (Options.PIECEWISE_EXECUTION)
          exec = new PiecewiseSymbolicExecutor(cg, logger);
        else if (Options.CALLGRAPH_PRUNING)
          exec = new PruningSymbolicExecutor(cg, logger);
        else
          exec = new OptimizedPathSensitiveSymbolicExecutor(cg, logger);
        // start at line BEFORE snkStmt
        foundWitness = exec.executeBackward(startNode, startBlk, startLineBlkIndex - 1, query);
        Util.Print(logger.dumpEdgeStats());
        if (foundWitness) return true; 
        // else, refuted this attempt; try again
      }
    }
    // refuted all possible last rules without a witness
    return false; 
  }

  // returns error path without weak refs if one can be found, null otherwise
  public static List<Object> findNewErrorPath(HeapGraphWrapper hg, Object srcKey, Object snkKey, IClassHierarchy cha) {
    boolean foundWeakRef;
    for (;;) {
      foundWeakRef = false;
      BFSPathFinder<Object> bfs = new BFSPathFinder<Object>(hg, srcKey, new CollectionFilter<Object>(Collections.singletonList(snkKey)));
      List<Object> path = bfs.find();
      if (path == null) return null;

      int srcIndex = 1, snkIndex = 0;
      Object fieldKey = null;
      while (srcIndex < path.size()) {
        Object src = path.get(srcIndex);
        if (src instanceof PointerKey && !(src instanceof StaticFieldKey)) {
          // src is intermediate point in points-to edge; either field name or
          // array contents
          if (src instanceof ArrayContentsKey) {
            fieldKey = src;
          } else if (src instanceof InstanceFieldKey) {
            InstanceFieldKey ifk = (InstanceFieldKey) src;
            fieldKey = ifk;
          } else {
            Util.Assert(false, "UNSUPPORTED POINTER KEY TYPE!" + src);
          }
          srcIndex++;
        } else {
          Object snk = path.get(snkIndex);
          if (isWeakReference(src, snk, cha)) {
            hg.addIgnoreEdge(fieldKey, snk);
            foundWeakRef = true;
            break;
          }
          fieldKey = null;
          snkIndex = srcIndex;
          srcIndex++;
        }
      }
      if (!foundWeakRef) {
        if (Options.DEBUG) {
          System.out.println("<FIELD PATH Length: " + path.size());
          for (int i = path.size() - 1; i >= 0; i--)
            System.out.println(path.get(i) + " (" + path.get(i).getClass() + ")");
          System.out.println("</FIELD PATH>");
        }
        return path;
      } // else, try finding another path without weak references
    }
  }

  private static boolean isWeakReference(Object src, Object snk, IClassHierarchy cha) {
    if (!Options.INCLUDE_WEAK_REFERENCES) {
      // check if any links in the path are WeakReference
      if (src instanceof InstanceKey) {
        InstanceKey key = (InstanceKey) src;
        IClass type = key.getConcreteType();
        if (type.equals(WEAK_REFERENCE) || cha.isSubclassOf(type, WEAK_REFERENCE))
          return true;
      }
      if (snk instanceof InstanceKey) {
        InstanceKey key = (InstanceKey) snk;
        IClass type = key.getConcreteType();
        if (type.equals(WEAK_REFERENCE) || cha.isSubclassOf(type, WEAK_REFERENCE))
          return true;
      }
      // also do silly syntactic check
      // return src.toString().contains("WeakReference") ||
      // snk.toString().contains("WeakReference");
    }
    return false;
  }
}

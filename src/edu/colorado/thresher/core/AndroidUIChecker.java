package edu.colorado.thresher.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.ibm.wala.analysis.pointers.HeapGraph;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.Selector;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.graph.traverse.DFS;

import edu.colorado.thresher.core.Main.UIQuery;

public class AndroidUIChecker {
  
  // TODO: for now, checking only Buttons and their onClick event handler. will eventually expand to all View's and event handlers
  // TODO: we assume button id's and labels are not set/re-set dynamically. will eventually need to handle this
  public static void runUICheck(String appPath) 
    throws IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    Options.FULL_WITNESSES = true;    
    Util.Unimp("TODO: remove all uses of cg.getNodes()! behaves badly with subclassing");
    // BEGIN PHASE 1
    // (1) parse buttons from the manifest
    Collection<AndroidUtils.AndroidButton> buttons = AndroidUtils.parseButtonInfo(appPath);
    // (2) build call graph and points-to analysis
    AbstractDependencyRuleGenerator drg = setupCGandPT(appPath, buttons);
    
    //getActivities(drg);
    // TMP
    emitEntrypointSinkPairs(drg);
    System.exit(1);
    // END TMP
    
    // (3) find dynamically created buttons (requires symbolic execution)
    findDynamicallyCreatedButtons(buttons, drg);
    // (4) bind buttons to event handlers pre-declared in the manifest
    bindButtonsToManifestDeclaredEventHandlers(buttons, drg.getCallGraph());
    // (5) bind buttons to event handlers set dynamically using button.setOn*Listener() (requires symbolic execution)
    bindButtonsToDynamicallyDeclaredEventHandlers(buttons, drg);
    // (6) for each call to findViewById(), determine which button will be returned by the call
    //collectButtonLookups(buttons, drg);
    // END PHASE 1
    
    Set<CGNode> reachable = HashSetFactory.make();
    for (AndroidUtils.AndroidButton btn : buttons) {
      // TMP 
      reachable.addAll(getCallsReachableFromButtonFI(btn, drg.getCallGraph()));
    }
    
    for (CGNode node : reachable) {
      Util.Print("reachable: " + node.getMethod());
    }
    Util.Print(reachable.size() + " reachable nodes.");
    
	// BEGIN PHASE 2
    // generate harness that creates each button and calls each of its event handlers
	// END PHASE 2
		
	// BEGIN PHASE 3
	// bind each button to its corresponding pointer variable
	// find methods reachable from each button
	// END PHASE 3
  }  
  
  private static void emitEntrypointSinkPairs(AbstractDependencyRuleGenerator drg) {
    CallGraph cg = drg.getCallGraph();
    List<CGNode> snks = new ArrayList<CGNode>();
    for (Iterator<CGNode> iter = drg.getCallGraph().iterator(); iter.hasNext();) {
      CGNode node = iter.next();
      IClass clazz = node.getMethod().getDeclaringClass();
      if (clazz.getClassLoader().getReference().equals(ClassLoaderReference.Primordial) &&
          isAndroidRelated(clazz)) {
        snks.add(node);
      }
    }
    
    LinkedList<CGNode> worklist = new LinkedList<CGNode>();
    Set<CGNode> seen = HashSetFactory.make();
    Set<CGNode> entrypoints = new HashSet<CGNode>(cg.getEntrypointNodes());
    Set<Pair<IMethod,IMethod>> pairs = HashSetFactory.make();
    //Graph<CGNode> reverseCG = GraphInverter.invert(cg);
    // TODO: this is quite inefficient; potentially lots of redundant work done here
    // go backwards from each sink until we find an entrypoint
    // refuse to go backwards to methods that are also library methods
    for (CGNode snk : snks) {
      worklist.add(snk);
      seen.add(snk);
      while (!worklist.isEmpty()) {
        CGNode cur = worklist.removeFirst();
        IMethod snkMethod = snk.getMethod();
        for (Iterator<CGNode> preds = cg.getPredNodes(cur); preds.hasNext();) {
          CGNode pred = preds.next();
          IClass clazz = pred.getMethod().getDeclaringClass();
          if (entrypoints.contains(pred)) {
            pairs.add(Pair.make(pred.getMethod(), snkMethod));
          } else if (!clazz.getClassLoader().getReference().equals(ClassLoaderReference.Primordial) &&
                     seen.add(pred)) {
            worklist.add(pred);
          }          
        }
      }
      seen.clear();
      worklist.clear();
    }
    
    for (Pair<IMethod,IMethod> srcSnkPair : pairs) {
      Util.Print("PAIR: (" + srcSnkPair.fst + " : " + srcSnkPair.snd + ")");
    }
    Util.Print(pairs.size() + " pairs.");
    /*   
    for (CGNode entrypoint : cg.getEntrypointNodes()) {
      IMethod entryMethod = entrypoint.getMethod();
      //Util.Print("checking for reachable from entrypoint " + entryMethod);
      for (CGNode node : DFS.getReachableNodes(cg, Collections.singleton(entrypoint))) {
        IClass clazz = node.getMethod().getDeclaringClass();
        if (clazz.getClassLoader().getReference().equals(ClassLoaderReference.Primordial) &&
            isAndroidRelated(clazz)) {
          Pair<IMethod,IMethod> srcSnkPair = Pair.make(entryMethod, node.getMethod());    		  
          Util.Print("PAIR: (" + srcSnkPair.fst + ", " + srcSnkPair.snd + ")");
        }
      }      
    }	
    */  
  }
  
  
  private static boolean isAndroidRelated(IClass clazz) {
    String name = clazz.getName().toString();
    //Util.Print("is " + name + " android-related?");
    return name.startsWith("Landroid") || name.startsWith("Ldalvik") || name.startsWith("Lorg/apache/http");
  }
  
  public static void getActivities(AbstractDependencyRuleGenerator drg) {
    for (Iterator<CGNode> iter = drg.getCallGraph().iterator(); iter.hasNext();) {
      CGNode node = iter.next();
      IClass clazz = node.getMethod().getDeclaringClass();
      //if (clazz.getClassLoader().getReference().equals(ClassLoaderReference.Primordial)) continue;
      
      if (node.getMethod().toString().contains("onClick")) {
        Util.Print("method " + node.getMethod());
      }
      
      //if (node.getMethod().get)
    }
    /*
    IClassHierarchy cha = drg.getClassHierarchy();
    final IClass activity = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/app/Activity"));
    Util.Assert(activity != null);
    Collection<IClass> classes = cha.getImmediateSubclasses(activity);
    Util.Assert(!classes.isEmpty(), " found no activities!");
    for (IClass clazz : classes) {
      Util.Print("Activity: " + clazz);
      for (IMethod method : clazz.getAllMethods()) {
        Util.Print("method " + method);
      }
    }
    */
  }

  // flow-insensitive reachability
  public static Set<CGNode> getCallsReachableFromButtonFI(AndroidUtils.AndroidButton btn, CallGraph cg) {
    return DFS.getReachableNodes(cg, btn.eventHandlerNodes);    
  }
	
  // special hack to account for event handler methods shared by multiple buttons
  // path-sensitive up to one callee
  public static void getCallsReachableFromButton1LevelPS(AndroidUtils.AndroidButton btn,
														 CGNode eventHandler,
														 AbstractDependencyRuleGenerator drg) {
	HeapModel hm = drg.getHeapModel();
    // create query that says the button was passed as the first argument to the event handler
	// TODO: assertion about # of params, use getParam()?
	PointerKey paramKey = hm.getPointerKeyForLocal(eventHandler, 2);
	PointerVariable lhs = Util.makePointerVariable(paramKey);
    PointsToEdge edge = new PointsToEdge(lhs, btn.var);
	IQuery query = new CombinedPathAndPointsToQuery(edge, drg);

	// push query backwards through event handler method, logging each method call we see
    SSACFG cfg = eventHandler.getIR().getControlFlowGraph();
    SSACFG.BasicBlock startBlk = cfg.exit();
	int startLine = startBlk.getLastInstructionIndex();
	// execute the query to the method boundary
	  
	// do regular flow-insensitive DFS from each logged method call
  }
	
  static int RECEIVER = 1;
  
  public static void collectButtonLookups(Collection<AndroidUtils.AndroidButton> buttons,  
      AbstractDependencyRuleGenerator drg) {
    CallGraph cg = drg.getCallGraph();
    Collection<Pair<SSAInvokeInstruction,CGNode>> callPairs = new ArrayList<Pair<SSAInvokeInstruction,CGNode>>();
    for (MethodReference findMethod : findMethods) { // collect each call to a button lookup method
      callPairs.addAll(WALACallGraphUtil.getCallInstrsForMethod(findMethod, cg));
    }
    Set<Integer> viewsSeen = HashSetFactory.make();
    for (Pair<SSAInvokeInstruction,CGNode> pair : callPairs) {
      if (WALACallGraphUtil.isLibraryMethod(pair.snd)) continue;
      SSAInvokeInstruction call = pair.fst; CGNode node = pair.snd; IR ir = node.getIR(); SymbolTable tbl = ir.getSymbolTable();
      int viewUse = call.getUse(1);
      // make sure button id being used for lookup is a constant.
      // it's possible for us to handle cases where the id is not a constant, but it is difficult in general
      Util.Assert(tbl.isIntegerConstant(viewUse), "non-constant button id used in call " + call + " node " + node);
      int viewId = tbl.getIntValue(viewUse);
      
      // find the button being looked up
      boolean found = false;
      for (AndroidUtils.AndroidButton button : buttons) {
        if (button.intId == viewId) {
          Util.Print("button " + button + " will be returned by call " + call + " in node " + node);
          viewsSeen.add(viewId);
          found = true;
          break;
        }
      }
      //Util.Assert(found, "we don't know about a button with id " + btnId);
      if (!found) Util.Print("WARNING: we don't know about a view with id " + viewId + " (hex " + Integer.toHexString(viewId) + ")");
    }
    
    int used = 0;
    for (AndroidUtils.AndroidButton button : buttons) {
      if (!viewsSeen.contains(button.intId)) {
        Util.Print("Can't find any dynamic lookups of button " + button);
      } else used++;
    }
    Util.Print("Found " + buttons.size() + " buttons; " + used + " are looked up dynamically.");

  }
  
  public static void bindButtonsToDynamicallyDeclaredEventHandlers(Collection<AndroidUtils.AndroidButton> buttons,  
      AbstractDependencyRuleGenerator drg) {
    CallGraph cg = drg.getCallGraph(); HeapModel hm = drg.getHeapModel(); HeapGraph hg = drg.getHeapGraph();
    Collection<Pair<SSAInvokeInstruction,CGNode>> callPairs = WALACallGraphUtil.getCallInstrsForMethod(SET_ON_CLICK_LISTENER, cg);
    for (Pair<SSAInvokeInstruction,CGNode> pair : callPairs) {
      Util.Print("trying call " + pair.fst + " in " + pair.snd);
      // skip this call if it occurs in the library; we only care about what the app developer is doing
      if (WALACallGraphUtil.isLibraryMethod(pair.snd)) continue;
      SSAInvokeInstruction call = pair.fst; CGNode node = pair.snd; IR ir = node.getIR();
      PointerKey receiver = hm.getPointerKeyForLocal(node, call.getReceiver());
      CGNode listener = null;
      if (call.getUse(1) == RECEIVER) {
        // call is castRetval.setOnClickListener(this). the method to consider is therefore this.onClick()
        IMethod thisOnClick = ir.getMethod().getDeclaringClass().
                                 getMethod(Selector.make("onClick(Landroid/view/View;)V"));
        // get CGNode associated with this.onClick()
        Set<CGNode> listenerNodes = cg.getNodes(thisOnClick.getReference());
        Util.Assert(listenerNodes.size() == 1, "more than one onClick() CGNode");
        listener = listenerNodes.iterator().next(); 
      } else {
        Util.Unimp("anonymous listener function set in " + call + " " + ir);
      }
      
      // set up symbolic execution
      PointerVariable lhs = Util.makePointerVariable(receiver);
      PointerVariable rhs = SymbolicPointerVariable.makeSymbolicVar(receiver, hg);
      Util.Assert(rhs != null);
      PointsToEdge startEdge = new PointsToEdge(lhs, rhs);
      UIQuery.buttonId = -1; // reset static button id so we don't get confused
      UIQuery query = new UIQuery(startEdge, drg, findMethods);
      ISSABasicBlock[] blks = node.getIR().getBasicBlocksForCall(call.getCallSite());
      Util.Assert(blks.length == 1);
      SSACFG.BasicBlock startBlk = (SSACFG.BasicBlock) blks[0];
      int startLineBlkIndex = WALACFGUtil.findInstrIndexInBlock(call, startBlk);
      Util.Assert(startBlk.getAllInstructions().get(startLineBlkIndex).equals(call));
      ISymbolicExecutor exec = new OptimizedPathSensitiveSymbolicExecutor(cg, new Logger());
      // start symbolic execution at line BEFORE call
      exec.executeBackward(node, startBlk, startLineBlkIndex - 1, query);
      // make sure we found the button id
      Util.Assert(UIQuery.buttonId != -1, "couldn't determine which button flows to setOn*Listener!");
      Util.Print("found button id " + UIQuery.buttonId);
      boolean found = false;
      for (AndroidUtils.AndroidButton button : buttons) {
        if (button.intId == UIQuery.buttonId) {
          Util.Print("found button " + button + "; setting event handler to " + listener);
          button.eventHandlerNodes.add(listener);
          found = true;
          break;
        }
      }
      Util.Assert(found, "button with id " + UIQuery.buttonId + " not in button list! must be dynamically created");      
    }
    
    // sanity check; make sure we have found at least one event handler for each button
    for (AndroidUtils.AndroidButton button : buttons) {
      Util.Assert(!button.eventHandlerNodes.isEmpty(), "no event handlers found for button " + button);
      //Util.Print("button " + button + " ok.");
    }
  }
  
  public static void findDynamicallyCreatedButtons(Collection<AndroidUtils.AndroidButton> buttons, 
      AbstractDependencyRuleGenerator drg) {
    // TODO: handle calls to library methods that create buttons and reflective user creation of buttons?
    CallGraph cg = drg.getCallGraph(); IClassHierarchy cha = drg.getClassHierarchy();
    Collection<Pair<SSAInvokeInstruction,CGNode>> buttonConstructors = 
        new ArrayList<Pair<SSAInvokeInstruction,CGNode>>();
    
    Collection<IClass> buttonClasses =  cha.computeSubClasses(BUTTON);
    buttonClasses.add(cha.lookupClass(BUTTON));
    // look for calls to Button.<init>() or {subclass of Button}.<init>(),
    for (IClass buttonClass : buttonClasses) {
      for (IMethod method : buttonClass.getDeclaredMethods()) {
        if (method.isInit()) {
          buttonConstructors.addAll(WALACallGraphUtil.getCallInstrsForMethod(method.getReference(), cg));
        }
      }
    }
    for (Pair<SSAInvokeInstruction,CGNode> pair : buttonConstructors) {
      Util.Print("found dynamic button constructor " + pair.fst + " in " + pair.snd);
    }
    // TODO: add dynamically constructed buttons to button list
    Util.Assert(buttonConstructors.isEmpty(), "found " + buttonConstructors.size() + " dynamically constructed buttons");
  }
  
  public static void bindButtonsToManifestDeclaredEventHandlers(Collection<AndroidUtils.AndroidButton> buttons, CallGraph cg) {
    // now that we have built the callgraph, we can bind each button to the CGNode declared as its event handler in the manifest
    for (Iterator<CGNode> iter = cg.iterator(); iter.hasNext();) {
      CGNode node = iter.next();
      IClass clazz = node.getMethod().getDeclaringClass();
      if (clazz.getClassLoader().getReference().equals(ClassLoaderReference.Primordial)) continue;
      
      MethodReference ref = node.getMethod().getReference();
      // TODO: this is super coarse. what we need to do is see what layout is set for a given Activity/View, then
      // only set the onClick() method of that particular Activity/View for buttons in that layout
      // TODO: should be nicer way to do this -- query for methods with a given name?
      for (AndroidUtils.AndroidButton button : buttons) {     

        if (!button.hasDefaultListener() && button.eventHandlerName.equals(ref.getName().toString())) {
          // method name matches name declared in the manifest; add it
          Util.Print("adding event handler node " + node + " to " + button);
          button.eventHandlerNodes.add(node);
          //break outer;
        //} else if (button.hasDefaultListener() && node.getMethod().equals(ON_CLICK)) {
        } else if (button.hasDefaultListener() && ref.getName().equals(ON_CLICK.getName()) && ref.getDescriptor().equals(ON_CLICK.getDescriptor())) {
          Util.Print("adding event handler node " + node + " to " + button);
          // method name matches default listener name and signature (onClick); add it
          button.eventHandlerNodes.add(node);
        }
      }
    }
      
  }
  
  public static AbstractDependencyRuleGenerator setupCGandPT(String appPath, Collection<AndroidUtils.AndroidButton> buttons) 
    throws IOException, ClassHierarchyException, CallGraphBuilderCancelException {
    AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
    
    // get event handlers that override onClick for each button
    Set<String> handlers = HashSetFactory.make();
    for (AndroidUtils.AndroidButton button : buttons) {
      Util.Print("found manifest-declared button: " + button);
      handlers.add(button.eventHandlerName);
    }
    
    IClassHierarchy cha = Main.setupAndroidScopeAndEntryPoints(scope, entryPoints, handlers, appPath);
    return Main.buildCallGraphAndPointsToAnalysis(scope, cha, entryPoints, appPath);
  }
  
  // hardcoded class declarations
  
    
  
    static final MethodReference TAKE_PIC0 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/hardware/Camera"),
        "takePicture", "(Landroid/hardware/Camera$ShutterCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;)V");
    static final MethodReference TAKE_PIC1 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/hardware/Camera"),
        "takePicture", "(Landroid/hardware/Camera$ShutterCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;)V");
    static final MethodReference RECORD_AUDIO0 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/media/MediaRecorder"),
        "start", "()V");
    static final MethodReference TAKE_PIC2 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/hardware/Camera"),
        "takePicture", "(Landroid/hardware/Camera$ShutterCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;)V");
    static final MethodReference TAKE_PIC3 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/hardware/Camera"),
        "takePicture", "(Landroid/hardware/Camera$ShutterCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;Landroid/hardware/Camera$PictureCallback;)V");
    static final MethodReference RECORD_AUDIO1 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/media/MediaRecorder"),
        "start", "()V");
    static final MethodReference[] badMethods = new MethodReference[] { TAKE_PIC0, TAKE_PIC1, TAKE_PIC2, TAKE_PIC3, RECORD_AUDIO0, RECORD_AUDIO1 };
 
    static final MethodReference FIND_VIEW_BY_ID1 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/view/View"),
         "findViewById", "(I)Landroid/view/View");
    static final MethodReference FIND_VIEW_BY_ID2 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/app/Activity"),
        "findViewById", "(I)Landroid/view/View");
    static final MethodReference FIND_VIEW_BY_ID3 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Landroid/view/Window"),
        "findViewById", "(I)Landroid/view/View");
    static final MethodReference FIND_VIEW_BY_ID4 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/view/View"),
         "findViewById", "(I)Landroid/view/View");
    static final MethodReference FIND_VIEW_BY_ID5 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/app/Activity"),
        "findViewById", "(I)Landroid/view/View");
    static final MethodReference FIND_VIEW_BY_ID6 = 
        MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/view/Window"),
        "findViewById", "(I)Landroid/view/View");
    
    
    static final MethodReference SET_ON_CLICK_LISTENER = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, 
        "Landroid/widget/Button"),
        "setOnClickListener", "(Landroid/view/View$OnClickListener;)V");
    
    static final MethodReference ON_CLICK = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/app/Activity"), 
        "onClick", "(Landroid/view/View;)V");
    
    static final MethodReference INFLATE = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/view/LayoutInflater"), 
        "inflate", "(ILandroid/view/ViewGroup;)Landroid/view/View");
    
    static final TypeReference BUTTON = TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/widget/Button");
    
    static final Collection<MethodReference> findMethods = HashSetFactory.make();
    static {
      findMethods.add(FIND_VIEW_BY_ID1);
      findMethods.add(FIND_VIEW_BY_ID2);
      findMethods.add(FIND_VIEW_BY_ID3);
      findMethods.add(FIND_VIEW_BY_ID4);
      findMethods.add(FIND_VIEW_BY_ID5);
      findMethods.add(FIND_VIEW_BY_ID6);
    }
}

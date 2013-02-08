package edu.colorado.thresher;

import com.ibm.wala.classLoader.*;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.*;
import com.ibm.wala.ipa.callgraph.propagation.*;
import com.ibm.wala.ipa.callgraph.propagation.cfa.*;
import com.ibm.wala.ipa.cha.*;
import com.ibm.wala.types.*;
import com.ibm.wala.util.debug.*;
import com.ibm.wala.util.intset.*;

public class FakeMapContextSelector implements ContextSelector {

  private final static TypeName FakeMapName = TypeName.string2TypeName("LFakeMap");

  public final static TypeReference FakeMap = TypeReference.findOrCreate(ClassLoaderReference.Application, FakeMapName);
  private final IClassHierarchy cha;
  private final ZeroXInstanceKeys delegate;
  
  public FakeMapContextSelector(IClassHierarchy cha, ZeroXInstanceKeys delegate) {
    this.cha = cha;
    this.delegate = delegate;
    if (delegate == null) {
      throw new IllegalArgumentException("null delegate");
    }
  }
  
  public Context getCalleeTarget(CGNode caller, CallSiteReference site, IMethod callee, InstanceKey[] keys) {
    InstanceKey receiver = null;
    if (keys != null && keys.length > 0 && keys[0] != null) {
      receiver = keys[0];
    }
    //if (receiver != null && callee.getReference().equals(FakeMap)) {
      //  return new CallerSiteContext(caller, site);
    //} else {
    if (receiver == null) {
    	return Everywhere.EVERYWHERE;
          //Assertions.UNREACHABLE("null receiver for " + site);
    }
    return new ReceiverInstanceContext(receiver);
    //}
  }
  
  private static final IntSet thisParameter = IntSetUtil.make(new int[]{0});

  public IntSet getRelevantParameters(CGNode caller, CallSiteReference site) {
    if (site.isDispatch() || site.getDeclaredTarget().getNumberOfParameters() > 0) {
      return thisParameter;
    } else {
      return EmptyIntSet.instance;
    }
  }
  
  public static SSAPropagationCallGraphBuilder makeZeroOneFakeMapCFABuilder(AnalysisOptions options, AnalysisCache cache,
      IClassHierarchy cha, AnalysisScope scope) {

    if (options == null) {
      throw new IllegalArgumentException("options is null");
    }
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultSelectors(options, cha);
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultBypassLogic(options, scope, Util.class.getClassLoader(), cha);
    //addDefaultBypassLogic(options, scope, Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;

    ZeroXFakeMapCFABuilder builder = new ZeroXFakeMapCFABuilder(cha, options, cache, appSelector, appInterpreter, ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY | ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS
        | ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    return builder;
  }
  
}

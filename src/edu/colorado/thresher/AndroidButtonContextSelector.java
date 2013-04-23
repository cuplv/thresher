package edu.colorado.thresher;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.callgraph.impl.DelegatingContextSelector;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.SSAPropagationCallGraphBuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ContainerContextSelector;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.IntSetUtil;

public class AndroidButtonContextSelector extends ContainerContextSelector {

  public AndroidButtonContextSelector(IClassHierarchy cha, ZeroXInstanceKeys delegate) {
    super(cha, delegate);
  }
  
  @Override
  public IntSet getRelevantParameters(CGNode caller, CallSiteReference site) {
    final MethodReference FIND_VIEW_BY_ID4 = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Application, "Landroid/view/View"),
        "findViewById", "(I)Landroid/view/View");
    //if (caller.getMethod().getReference().equals(FIND_VIEW_BY_ID4)) {
    //if (site.getDeclaredTarget().equals(FIND_VIEW_BY_ID4)) {
    System.out.println("target is " + site.getDeclaredTarget().toString());
    if (site.getDeclaredTarget().toString().contains("MyInflater, inflate")) {
      if (Options.DEBUG) System.out.println("found findViewById()");
      // method is findViewById(int id); distingish via id
      return IntSetUtil.make(new int[2]);
    }
    return super.getRelevantParameters(caller, site);
  }
  
  public static class ZeroXAndroidButtonCFABuilder extends ZeroXCFABuilder {
    private ZeroXAndroidButtonCFABuilder(IClassHierarchy cha, AnalysisOptions options, AnalysisCache cache,
        ContextSelector appContextSelector, SSAContextInterpreter appContextInterpreter, int instancePolicy) {
      super(cha, options, cache, appContextSelector, appContextInterpreter, instancePolicy);
      ContextSelector CCS = makeAndroidButtonContextSelector(cha, (ZeroXInstanceKeys) getInstanceKeys());
      DelegatingContextSelector DCS = new DelegatingContextSelector(CCS, contextSelector);
      setContextSelector(DCS);
    }
    
    protected ContextSelector makeAndroidButtonContextSelector(IClassHierarchy cha, ZeroXInstanceKeys keys) {
      return new AndroidButtonContextSelector(cha, keys);
    }
  }
  
  public static SSAPropagationCallGraphBuilder makeZeroOneAndroidButtonCFABuilder(AnalysisOptions options, AnalysisCache cache,
      IClassHierarchy cha, AnalysisScope scope) {

    if (options == null) {
      throw new IllegalArgumentException("options is null");
    }
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultSelectors(options, cha);
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultBypassLogic(options, scope, Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;

    ZeroXAndroidButtonCFABuilder builder = new ZeroXAndroidButtonCFABuilder(cha, options, cache, appSelector, appInterpreter,
        ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY | ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS
            | ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    return builder;
  }
  
}

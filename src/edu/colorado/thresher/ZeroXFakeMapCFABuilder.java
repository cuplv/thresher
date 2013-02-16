package edu.colorado.thresher;

import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.*;
import com.ibm.wala.ipa.callgraph.propagation.*;
import com.ibm.wala.ipa.callgraph.propagation.cfa.*;
import com.ibm.wala.ipa.cha.*;

public class ZeroXFakeMapCFABuilder extends ZeroXCFABuilder {
  public ZeroXFakeMapCFABuilder(IClassHierarchy cha, AnalysisOptions options, AnalysisCache cache,
      ContextSelector appContextSelector, SSAContextInterpreter appContextInterpreter, int instancePolicy) {
    super(cha, options, cache, appContextSelector, appContextInterpreter, instancePolicy);
    ContextSelector CCS = makeFakeMapContextSelector(cha, (ZeroXInstanceKeys) getInstanceKeys());
    DelegatingContextSelector DCS = new DelegatingContextSelector(CCS, contextSelector);
    setContextSelector(DCS);
  }

  protected ContextSelector makeFakeMapContextSelector(IClassHierarchy cha, ZeroXInstanceKeys keys) {
    return new FakeMapContextSelector(cha, keys);
  }
}

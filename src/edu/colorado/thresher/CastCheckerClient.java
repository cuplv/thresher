package edu.colorado.thresher;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;

import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;

public class CastCheckerClient implements IClient {
  
  public CastCheckerClient() { }
  
  /**
   * do whatever pre-analysis is required for the client (e.g., a points-to a analysis)
   * @param path path to the .class files of the client
   */
  public void setupClient(String appPath) throws ClassHierarchyException, CallGraphBuilderCancelException {
    Options.FULL_WITNESSES = true;
    String appName;
    // removing trailing slash if needed
    if (appPath.endsWith("/")) appName = appPath.substring(0, appPath.length() - 1);
    else appName = appPath;
    // strip of front of path away from app name
    appName = appName.substring(appName.lastIndexOf("/") + 1);
    Util.Print("Starting on " + appName);
    
    AnalysisScope scope = AnalysisScope.createJavaAnalysisScope();
    Collection<Entrypoint> entryPoints = new LinkedList<Entrypoint>();
    /*
    IClassHierarchy cha = setupScopeAndEntrypoints(appPath, entryPoints, scope);
    
    AbstractDependencyRuleGenerator depRuleGenerator = buildCallGraphAndPointsToAnalysis(scope, cha, entryPoints, appPath);
    CallGraph cg = depRuleGenerator.getCallGraph();
    HeapModel heapModel = depRuleGenerator.getHeapModel();
    PointerAnalysis pointerAnalysis = depRuleGenerator.getHeapGraph().getPointerAnalysis();
    */
  }

  /**
   * run the client and get results
   */
  public void runClient() {
    
  }
  
}

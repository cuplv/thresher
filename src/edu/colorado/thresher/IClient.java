package edu.colorado.thresher;

import java.io.IOException;

import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.cha.ClassHierarchyException;

public interface IClient {

  /**
   * do whatever pre-analysis is required for the client (e.g., a points-to a analysis)
   * @param path path to the .class files of the client
   */
  public void setupClient(String path) throws ClassHierarchyException, CallGraphBuilderCancelException;  

  /**
   * run the client and get results
   */
  public void runClient();
  
}

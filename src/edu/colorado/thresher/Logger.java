package edu.colorado.thresher;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.intset.BitVectorIntSet;
import com.ibm.wala.util.intset.MutableIntSet;

public class Logger {

  final String benchmark;

  final Map<String, Integer> countMap = HashMapFactory.make();

  int failures = 0;
  int timeouts = 0;
  int edgesRefuted = 0;
  int edgesWitnessed = 0;
  int totalErrors = 0; // total number of (src, snk) pairs
  int totalFields = 0; // total number of src
  int errorsRefuted = 0;
  int errorsWitnessed = 0;
  int falseWitnesses = 0;
  int numStaticFields = 0;
  int totalProducingStatements = 0;
  int curErrorTimeouts = 0;
  int maxPathStackSize = 0;
  int numPaths = 0;
  int totalPaths = 0;
  int totalPathsWithRelevantLoop = 0;

  Set<String> witnessedFields = HashSetFactory.make();

  final MutableIntSet pathsWithRelevantLoop = new BitVectorIntSet();

  public Logger(String benchmark) {
    this.benchmark = benchmark;
  }

  public void log(String str) {
    Integer count = countMap.get(str);
    int countValue;
    if (count == null)
      countValue = 0;
    else
      countValue = count.intValue();
    countMap.put(str, ++countValue);
  }

  public void logWitnessList(List<DependencyRule> witnessList) {
    Util.Debug("<witness List>");
    for (DependencyRule rule : witnessList) {
      IR ir = rule.getNode().getIR();
      IBytecodeMethod method = (IBytecodeMethod) ir.getMethod();
      int bytecodeIndex;
      try {
        bytecodeIndex = method.getBytecodeIndex(rule.getStmt().getLineNum());
      } catch (InvalidClassFileException e) {
        bytecodeIndex = -1;
      }
      int sourceLineNum = method.getLineNumber(bytecodeIndex);
      Util.Debug(rule.getShown() + " " + rule.getStmt() + " line " + sourceLineNum);
    }
    Util.Debug("</witness List>");
  }

  public String dumpCountMap() {
    StringBuffer buf = new StringBuffer();
    for (Entry<String, Integer> entry : countMap.entrySet()) {
      buf.append(entry.getValue());
      buf.append(" : ");
      buf.append(entry.getKey());
      buf.append("'s\n");
    }
    return buf.toString();
  }

  public String dumpCSV() {
    // only reporting timeouts on errors where error was witnessed (since
    // precision loss doesn't matter if we refuted the error)
    int failures = totalErrors - edgesRefuted - errorsRefuted;
    return benchmark + "," + totalErrors + "," + errorsWitnessed + "," + errorsRefuted + "," + failures + "," + edgesRefuted + ","
        + edgesWitnessed + "," + timeouts;
  }

  public String dumpColumnLabels() {
    return "benchmark" + "," + "totalErrors" + "," + "errorsWitnessed" + "," + "errorsRefuted" + "," + "failures" + ","
        + "edgesRefuted" + "," + "edgesWitnessed" + "," + "timeouts";
  }

  public void logPathWithRelevantLoop(IPathInfo path) {
    pathsWithRelevantLoop.add(path.getPathId());
  }

  public void logErrorField() {
    this.totalFields++;
  }

  public void logWitnessedField(String fld) {
    witnessedFields.add(fld);
  }

  public void logFailure() {
    curErrorTimeouts = 0;
    failures++;
  }

  public void logPathStackSize(int pathStackSize) {
    if (pathStackSize > this.maxPathStackSize)
      this.maxPathStackSize = pathStackSize;
  }

  public void logProducingStatementsForEdge(int numProducingStatements) {
    totalProducingStatements += numProducingStatements;
  }

  public void logRefutedError() {
    errorsRefuted++;
  }

  public void logWitnessedError() {
    errorsWitnessed++;
  }

  public void logEdgeRefutation() {
    this.timeouts -= curErrorTimeouts;
    Util.Print("logged refutation");
    edgesRefuted++;
  }

  public void logEdgeWitnessed() {
    curErrorTimeouts = 0;
    Util.Print("logged witness");
    this.edgesWitnessed++;
  }

  public void logNumStaticFields(int numStaticFields) {
    this.numStaticFields = numStaticFields;
  }

  public void logTotalErrors(int totalErrors) {
    this.totalErrors = totalErrors;
  }

  public void logTimeout() {
    Util.Debug("logged timeout");
    curErrorTimeouts++;
    this.timeouts++;
  }

  public void logPathCount(int numPaths) {
    this.numPaths += numPaths;
  }

  public void logFalseWitness() {
    // System.err.println("logged false witness");
    this.falseWitnesses++;
  }

  public String dumpEdgeStats() {
    String s = "Total paths: " + numPaths + "\nPaths with relevant loop: " + pathsWithRelevantLoop.size()
        + "\nmaxPathStackSize was " + maxPathStackSize + "\n";
    totalPaths += numPaths;
    totalPathsWithRelevantLoop += pathsWithRelevantLoop.size();
    this.maxPathStackSize = 0;
    this.numPaths = 0;
    this.pathsWithRelevantLoop.clear();
    return s;
  }

  public String dumpHumanReadable() {
    return totalErrors + " totals errors\n" + totalFields + " total fields\n" + errorsRefuted + " errors refuted\n"
        + errorsWitnessed + " errors witnessed\n" + edgesRefuted + " edges refuted\n" + +(totalFields - witnessedFields.size())
        + " fields refuted\n" + witnessedFields.size() + " fields witnessed\n" + edgesWitnessed + " edges witnessed\n" + totalPaths
        + " total paths\n" + totalPathsWithRelevantLoop + " paths with relevant loop\n" + timeouts + " timeouts\n" + failures
        + " failures\n";
  }

}

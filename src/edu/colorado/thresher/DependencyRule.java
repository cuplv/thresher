package edu.colorado.thresher;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.util.collections.HashSetFactory;

public class DependencyRule implements Comparable {

  public static int symbCounter = 0;
  private final PointsToEdge shown;
  private final PointerStatement stmt;
  private final TreeSet<PointsToEdge> toShow;
  // CGNode of method containing rule
  private final CGNode node;
  private final SSACFG.BasicBlock blk; // block containing rule
  private String strRepresentation;

  public DependencyRule(PointsToEdge shown, PointerStatement stmt, TreeSet<PointsToEdge> toShow, CGNode node, SSACFG.BasicBlock blk) {
    // if (toShow.contains(shown)) this.shown = null; // invalidate the rule
    // else this.shown = shown;
    this.shown = shown;
    this.stmt = stmt;
    this.toShow = toShow;// (TreeSet) Collections.unmodifiableSet(toShow);
    this.node = node;
    this.blk = blk;
    // Util.Assert(toShow.size() < 3,
    // "TRYING TO CONSTRUCT BOGUS DEPENDECY RULE");

    // TODO: sanity checks
    // Util.Assert(!toShow.contains(shown), "edge " + shown +
    // " in toShow set for " + this);
    /*
     * if (shown.getSource().isLocalVar()) { Set<CGNode> nodes = new
     * HashSet<CGNode>(); nodes.add(shown.getSource().getNode()); for
     * (PointsToEdge edge : toShow) { if (edge.getSource() instanceof
     * LocalPointerKey) { LocalPointerKey lpk = (LocalPointerKey)
     * edge.getSource(); nodes.add(lpk.getNode()); } } Util.Assert(nodes.size()
     * == 1, "more than one local context for nodes!"); }
     */
  }

  /**
   * return new DependencyRule, making substitutions described in subMap.
   * 
   * @param map
   * @return
   */
  public DependencyRule substitute(Map<SymbolicPointerVariable, PointerVariable> subMap) {
    if (subMap.isEmpty())
      return this;
    // perform substitutions suggested by subMap
    PointerVariable newSrc = shown.getSource(), newSnk = shown.getSink();
    for (PointerVariable subFor : subMap.keySet()) { // get new shown edge
      // Util.Debug("sub " + subFor + " with " + subMap.get(subFor));
      // if (shown.getSource().equals(subFor)) {
      if (shown.getSource() == subFor) {
        newSrc = subMap.get(subFor);
      }
      // if (shown.getSink().equals(subFor)) {
      if (shown.getSink() == subFor) {
        newSnk = subMap.get(subFor);
      }
    }
    PointsToEdge newShown;
    if (newSrc instanceof ConcretePointerVariable)
      newShown = new PointsToEdge((ConcretePointerVariable) newSrc, newSnk, shown.getFieldRef());
    else
      newShown = new PointsToEdge((SymbolicPointerVariable) newSrc, newSnk, shown.getFieldRef());

    // get new toShow set
    TreeSet<PointsToEdge> newToShow = new TreeSet<PointsToEdge>();
    for (PointsToEdge edge : this.toShow) {
      PointerVariable src = edge.getSource(), snk = edge.getSink();
      for (PointerVariable subFor : subMap.keySet()) {
        // if (edge.getSource().equals(subFor)) {
        if (edge.getSource() == subFor) {
          src = subMap.get(subFor);
        }
        // if (edge.getSink().equals(subFor)) {
        if (edge.getSink() == subFor) {
          snk = subMap.get(subFor);
        }
      }
      if (src instanceof ConcretePointerVariable)
        newToShow.add(new PointsToEdge((ConcretePointerVariable) src, snk, edge.getFieldRef()));
      else
        newToShow.add(new PointsToEdge((SymbolicPointerVariable) src, snk, edge.getFieldRef()));
    }
    Util.Assert(newToShow.size() == toShow.size(), "discrepancy in toShow set sizes! newToShow " + Util.printCollection(newToShow)
        + " toShow " + Util.printCollection(toShow));
    DependencyRule newRule = new DependencyRule(newShown, this.stmt, newToShow, this.node, this.blk);
    Util.Debug("new rule is " + newRule);
    return newRule;
  }

  /**
   * do this and other have the same produced edge and pre/post pair?
   * 
   * @param other
   */
  public boolean equalExceptForStatement(DependencyRule other) {
    if (!this.shown.equals(other.getShown()))
      return false;
    TreeSet<PointsToEdge> otherToShow = other.toShow;
    if (toShow.size() != otherToShow.size())
      return false;
    // sets are the same size
    Iterator<PointsToEdge> iter1 = toShow.descendingIterator();
    Iterator<PointsToEdge> iter2 = otherToShow.descendingIterator();
    while (iter1.hasNext() && iter2.hasNext()) {
      PointsToEdge edge1 = iter1.next(), edge2 = iter2.next();
      if (!edge1.equals(edge2))
        return false;
    }
    return true;
  }

  @Override
  public String toString() {
    if (strRepresentation == null) {
      String shownStr = shown == null ? "" : shown.toString();
      String stmtStr = stmt == null ? "" : stmt.toString();
      String edgeSet = "";
      boolean firstPass = true;
      for (PointsToEdge edge : toShow) {
        if (firstPass) {
          edgeSet += edge.toString();
          firstPass = false;
        } else
          edgeSet += " * " + edge.toString();
      }
      strRepresentation = "T: " + shownStr + "\n<---- " + stmtStr + "\n{" + edgeSet + "}";
    }
    return strRepresentation;
  }

  @Override
  public int compareTo(Object other) {
    DependencyRule otherRule = (DependencyRule) other;
    int shownComparison = shown.compareTo(otherRule.getShown());
    if (shownComparison != 0)
      return shownComparison;

    // int stmtComparison = stmt.compareTo(otherRule.getStmt());
    // if (stmtComparison != 0) return stmtComparison;

    TreeSet<PointsToEdge> otherToShow = otherRule.toShow;

    if (toShow.size() > otherToShow.size())
      return 1;
    else if (toShow.size() < otherToShow.size())
      return -1;
    // sets are the same size
    Iterator<PointsToEdge> iter1 = toShow.descendingIterator();
    Iterator<PointsToEdge> iter2 = otherToShow.descendingIterator();
    while (iter1.hasNext() && iter2.hasNext()) {
      PointsToEdge edge1 = iter1.next(), edge2 = iter2.next();
      int comparison = edge1.compareTo(edge2);
      if (comparison != 0)
        return comparison;
    }
    return 0;
  }

  @Override
  public boolean equals(Object other) {
    Util.Pre(other != null && other instanceof DependencyRule, "can't compare to non-dependency rule ");
    return this.compareTo(other) == 0;
  }

  @Override
  public int hashCode() {
    return this.toString().hashCode();
  }

  public PointsToEdge getShown() {
    return shown;
  }

  public PointerStatement getStmt() {
    return stmt;
  }

  public TreeSet<PointsToEdge> getToShow() {
    return toShow;
  }

  public SSACFG.BasicBlock getBlock() {
    return blk;
  }

  public CGNode getNode() {
    return node;
  }

  public boolean modifiesHeap() {
    if (shown.getSource() instanceof ConcretePointerVariable && ((ConcretePointerVariable) shown.getSource()).isHeapVar())
      return true;
    for (PointsToEdge edge : toShow) {
      if (edge.getSource() instanceof ConcretePointerVariable && ((ConcretePointerVariable) shown.getSource()).isHeapVar())
        return true;
    }
    return false;
  }

  /**
   * @return - true if this rule has *any* edges with symbolic variables, false
   *         otherwise
   */
  public boolean isSymbolic() {
    if (this.getShown().isSymbolic())
      return true;
    for (PointsToEdge edge : this.toShow) {
      if (edge.isSymbolic())
        return true;
    }
    return false;
  }

  public Set<SymbolicPointerVariable> getSymbolicVars() {
    Set<SymbolicPointerVariable> symbolicVars = HashSetFactory.make();//new HashSet<SymbolicPointerVariable>();
    symbolicVars.addAll(shown.getSymbolicVars());
    for (PointsToEdge edge : toShow) {
      symbolicVars.addAll(edge.getSymbolicVars());
    }
    return symbolicVars;
  }

  /*
   * // return a copy of this dependency rule with toSub subbed for subFor in
   * each of the edges public DependencyRule substituteMethod(CGNode toSubNode,
   * MethodReference subFor) { MethodReference toSub =
   * toSubNode.getMethod().getReference(); PointsToEdge newShown =
   * shown.substituteMethod(toSub, subFor); TreeSet<PointsToEdge> newToShow =
   * new TreeSet<PointsToEdge>(); for (PointsToEdge edge : toShow) {
   * PointsToEdge newEdge = edge.substituteMethod(toSub, subFor);
   * newToShow.add(newEdge); } return new DependencyRule(newShown, this.stmt,
   * newToShow, toSubNode); }
   */

  // private void createNewSymb() {
  // Z3Sort intSort = ctx.mkIntSort();
  // symbCounter++;
  // ctx.assertCnstr(ctx.mkEq(ctx.mkConst(ctx.mkStringSymbol(symbCounter +
  // "symb_bound"), intSort), ctx.mkInt(0, intSort)));
  // }
  /*
   * public DependencyRule intersect(DependencyRule other) { if
   * (!shown.equals(other.getShown())) return null; if
   * (!stmt.equals(other.getStmt())) return null; Set<PointsToEdge> newSet = new
   * HashSet<PointsToEdge>(); Set<PointsToEdge> otherToShow = other.getToShow();
   * //symbCounter++; boolean newSymb = false; for (PointsToEdge edge0 :
   * otherToShow) { for (PointsToEdge edge1 : toShow) { if (edge0.equals(edge1))
   * { newSet.add(edge0); } else if
   * (edge0.getSource().equals(edge1.getSource())) { if (!newSymb) {
   * Util.Assert(false, "not expecting creation of new symbolic vars!"); newSymb
   * = true; createNewSymb(); } PointerVariable src = edge0.getSource();
   * PointerVariable snk = edge0.getSink(); int symbNum = symbCounter;
   * newSet.add(new PointsToEdge(src, new PointerVariable(symbNum + "symb",
   * snk.getTypeId(), true), edge0.getFieldName())); } else if
   * (edge0.getSink().equals(edge1.getSink())) { if (!newSymb) {
   * Util.Assert(false, "not expecting creation of new symbolic vars!"); newSymb
   * = true; createNewSymb(); } PointerVariable src = edge0.getSource();
   * PointerVariable snk = edge0.getSink(); int symbNum = symbCounter;
   * newSet.add(new PointsToEdge(new PointerVariable(symbNum + "symb",
   * src.getTypeId(), true), snk, edge0.getFieldName())); } } } return new
   * DependencyRule(shown, stmt, newSet); }
   */

}

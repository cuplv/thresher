import z3.*;
import z3.java.*;
class ScalaZ3Test {
    public static void main(String[] args) {
	// test of checkWithAssumptions()
	Z3Config config = new Z3Config();
	Z3Context ctx = new Z3Context(config);
	Z3Sort intSort = ctx.mkIntSort();
	Z3Sort boolSort = ctx.mkBoolSort();
	Z3Symbol pSymb = ctx.mkStringSymbol("p");
	Z3Symbol qSymb = ctx.mkStringSymbol("q");
	Z3AST p = ctx.mkConst(pSymb, boolSort);
	Z3AST q = ctx.mkConst(qSymb, boolSort);
	Z3AST five = ctx.mkInt(5, intSort);
	ctx.assertCnstr(ctx.mkOr(p, q));
	System.out.println(ctx.check()); // should print true
	System.out.println(ctx.checkAssumptionsNoModel(p, ctx.mkNot(q))); // should print true
	
    }
}
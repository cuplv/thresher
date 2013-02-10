import z3.*;
import z3.java.*;
class Test {
    public static void main(String[] args) {
	/*
	Z3Config config = new Z3Config();
	Z3Context ctx = new Z3Context(config);
	Z3Sort intSort = ctx.mkIntSort();
	Z3Symbol pSymb = ctx.mkStringSymbol("p");
	Z3Symbol qSymb = ctx.mkStringSymbol("q");
	Z3AST five = ctx.mkInt(5, intSort);
	Z3AST six = ctx.mkInt(6, intSort);	
	Z3AST p = ctx.mkConst(pSymb, intSort);
	Z3AST q = ctx.mkConst(qSymb, intSort);
	
	ctx.assertCnstr(ctx.mkEq(six, five));
	//ctx.assertCnstr(ctx.mkEq(p, five));
	//ctx.assertCnstr(ctx.mkEq(p, six));
	boolean result = ctx.check();
	System.out.println(result);
	ctx.delete();
	*/
	// incremental test
	//	Z3ExtContext extCxt = new Z3ExtContext();
	

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
	System.out.println(ctx.check());
	//Z3AST assumption0 = ctx.mkEq(p, five);
	//Z3AST assumption1 = ctx.mkEq(q, five);
	System.out.println(ctx.checkAssumptionsNoModel(p, ctx.mkNot(q)));
	
    }
}
public class Main {

    public Main(SimpleInterface2 f) {
	Assertions.Assert(f.returnInter().getFoo().f == 0);
    }
}
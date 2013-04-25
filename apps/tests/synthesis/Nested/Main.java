public class Main {

    public Main(SimpleInterface2 f) {
	Assertions.Assert(f.returnInter().getInt() < 7);
    }
}
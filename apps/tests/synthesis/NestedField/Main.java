import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {
    }

    public void foo(SimpleInterface2 f) {
	Assertions.Assert(f.returnInter().getFoo().f == 0);
    }
}
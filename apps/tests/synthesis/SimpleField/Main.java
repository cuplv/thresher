import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {

    }

    public void foo(Foo f) {
	Assertions.Assert(f.i == 0);
    }
}
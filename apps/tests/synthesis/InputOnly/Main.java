import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {
    }

    public void foo(int i) {
	Object o = new Object();
	Assertions.Assert(i >= 0);
    }

}
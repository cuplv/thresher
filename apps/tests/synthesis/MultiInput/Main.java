import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {
    }

    public void foo(int i, Main m, int j) {
	Assertions.Assert(i >= j);
    }

}
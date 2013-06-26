import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {
    }

    public void foo(SimpleInterface i) {
	Assertions.Assert(i.getInt0() <= i.getInt1());
    }
    
}
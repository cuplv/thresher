import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {

    }

    public void foo(SimpleInterface i) {
	initialize(i);
    }

    private void initialize(SimpleInterface i) {
	if (i.getBool()) return;

	if (i.getInt0() > 7) {
	    Assertions.Assert(i.getObject() != null);
	}
    }
    
}
import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main(SimpleInterface i) {
    }
    
    public void foo(SimpleInterface i) {
	Assertions.Assert(i.getObj() == null);
    }
}
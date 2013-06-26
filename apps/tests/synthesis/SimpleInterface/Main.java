import edu.colorado.thresher.external.Assertions;

public class Main {

    public Main() {

    }
    
    public void foo(SimpleInterface i) {
	int j = i.getInt();
	Assertions.Assert(j >= 0);
    }
}
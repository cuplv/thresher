public class Main {

    public Main(SimpleInterface i) {
	initialize(i);
    }

    private void initialize(SimpleInterface i) {
	if (i.getBool()) return;

	if (i.getInt0() > 7) {
	    Assertions.Assert(i.getObject() != null);
	}
    }
    
}
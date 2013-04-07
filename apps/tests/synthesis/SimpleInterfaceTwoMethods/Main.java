public class Main {

    public Main(SimpleInterface i) {
	Assertions.Assert(i.getInt0() <= i.getInt1());
    }
    
}
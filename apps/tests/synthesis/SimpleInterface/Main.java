public class Main {

    public Main(SimpleInterface i) {
	int j = i.getInt();
	Assertions.Assert(j >= 0);
    }
    
}
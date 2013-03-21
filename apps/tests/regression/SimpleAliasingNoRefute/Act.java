public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	Obj x;
	Obj z = new Obj();
	z.f = new Obj();
	if (rand()) {
	    x = new Obj();
	    z = x;
	} else {
	    x = new Obj();
	}
	x.f = new Act();
	storyCache.put(1, z.f);
    }

    public static boolean rand() { return true; }

    static class Obj {
	public Object f;
	public Obj() {}
    }
}
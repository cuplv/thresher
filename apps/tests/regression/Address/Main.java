class Main {

    static Vector storyCache = new Vector();

    public static void main() {
	Vector v = new Vector();
	Act i1 = new Act();
	v.add(i1);
	Act i2 = (Act)v.get(0);
    }
        
    class AddrBook {
	private Vector names;
	public AddrBook() { 
	    Vector t = new Vector();
	    this.names = t; 
	}
	
	public void addEntry(String n) {
	    Vector t = this.names; 
	    t.add(n);
	}
	
	public void update() {
	    Vector t = this.names;
	    for (int i = 0; i < t.size(); i++) {
		Object name = t.get(i);
		// is this cast safe?
		//String nameStr = (String)name;
		storyCache.add(name);
	    }
	}
    }
}

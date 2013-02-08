 class Vector {
	Object[] elems; 
	int count;
	public Vector() { 
	    Object[] t = new Object[10];
	    this.elems = t; 
	}
	
	public void add(Object p) {
	    Object[] t = this.elems;
	    t[count++] = p; // writes t.arr
	}
	
	public Object get(int ind) {
	    Object[] t = this.elems;
	    return t[ind]; // reads t.arr
	} 
	
	public int size() {
	    return count;
	}
    }
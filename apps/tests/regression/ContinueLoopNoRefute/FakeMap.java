public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String str, Object value, int a, int b) {
	//	table = new Object[capacity];
	Object o1 = new Object();
	Object o2 = new Object();
	for (int i = 0; i < 5; i++) {
            if (o1 == null) {
                continue;
            }
	    
            for (int j = 0; j < 5; j++) {
                if (a != b) {
                    if (o2 == null) {
			o2 = o1;
                    } else {
			o2 = new Object();
		    }
                }
            }
            if (o2 != null)
                o1 = o2;
        }
	table[size] = value;
	return null;
    }
}
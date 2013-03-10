public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value, int count) {
	boolean success = false;
	do {
	    Object o = new Object();
	    count++;
	    i = getStr();
            try {
                count++;
		success = true;
            } catch (NullPointerException e) {
                count *= 1;
            };
        } while (!success && i != null);

	foo(value);
	return null;
    }

    private String getStr() { return "hi"; }

    private void foo(Object value) {
	table[size] = value;
    }
}
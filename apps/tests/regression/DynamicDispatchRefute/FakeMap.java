public class FakeMap extends SuperMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = 2;
	size = -1;
    }

    @Override
    public Object put(String i, Object value) {
	table[size] = value;
	return null;
    }

    public String toString() {
	table = new Object[capacity];
	return "";
    }
}

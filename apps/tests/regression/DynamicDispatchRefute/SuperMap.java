public class SuperMap {

    private final static Object[] EMPTY_TABLE = new Object[0];
    private Object[] table;
    private int capacity;
    private int size;

    public SuperMap() {
	table = EMPTY_TABLE;
	capacity = 2;
	size = -1;
    }

    public Object put(String i, Object value) {
	table[size] = value;
	return null;
    }

    public String toString() {
	table = new Object[capacity];
	return "";
    }
}

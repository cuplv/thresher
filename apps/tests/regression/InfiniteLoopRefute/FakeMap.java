import java.util.List;

public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value, List<Object> objs) {
	table = new Object[5];
	while (true) {
	    table[size] = value;
	}
    }

    private void foo(Object value) {

    }
}
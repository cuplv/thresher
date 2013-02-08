import android.content.Intent;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    private Object[] mExtras;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value, int count) {
	if (bar(count)) {
	    count++;
	}

	Intent j = null;
	if (j.hasExtra("FOO")) {
	    count--;
	}
	table[count] = value;
	return null;
    }

    public boolean bar(int i) {
	Object o = null;
	return mExtras != null && mExtras[i] == o;
    }

}
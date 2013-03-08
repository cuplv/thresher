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
	table = new Object[3];

	  for (int j = 0; j < table.length; j++) {
	      Object e = table[j];
	      if (e != null) {
		  table[j] = null;
		  do {
		      Object next = new Object();
		      count++;
		  } while (e != null);
	      }
	  }
	  if (count > 0) {
	      table[size] = value;
	  }
	  return null;
    }
}

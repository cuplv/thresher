import java.util.Map;
import java.util.Map.Entry;


public class FakeMap {
  
  private int size = 0;
  private Object[] table;
  // invariant: EMPTY_TABLE should never be written (EMPTY_TABLE.contents -\> *)
  private static Object[] EMPTY_TABLE = new Object[2];

  static {
      Assertions.Unmodifiable(EMPTY_TABLE, "contents");//Assertions.ARRAY_CONTENTS);
  }

  public FakeMap() { this.table = EMPTY_TABLE; }

    // map.entrySet().iterator().next() != null
    // map.entrySet().iterator().hasNext() != false

  // (map.size() < 1 ^ map.entrySet() returns an Iterable containing an Entry e such that 
  // e.getKey() does not return null)
  public FakeMap(Map map) {
    if (map.size() < 1) this.table = EMPTY_TABLE;
    else this.table = new Object[8];
    constructorPutAll(map);
  }

  // (map.entrySet() returns an Iterable containing an Entry e such that e.getKey() 
  // does not return null ^ this.table -> EMPTY_TABLE)
  private void constructorPutAll(Map<Object,Object>  map) {
    for (Entry<Object,Object> e : map.entrySet()) {
      constructorPut(e.getKey(), e.getValue());
    }
  }

  // (this.table -> EMPTY_TABLE ^ key != null)
  private void constructorPut(Object key, Object value) {  
    if (key == null) return;
    int index = key.hashCode() & (table.length - 1);
    Entry newEntry = new FakeMapEntry(key, value);
    if (table == EMPTY_TABLE) {
	System.out.println("Failed assertion!");
	System.exit(1);
    }
    table[index] = newEntry; 
    size++;
  }

  static class FakeMapEntry<K, V> implements Entry<K, V> {
    final K key;
    V value;

    FakeMapEntry(K key, V value) {
      this.key = key;
      this.value = value;
    }

    public final K getKey() {
      return key;
    }

    public final V getValue() {
      return value;
    }
    
    public final V setValue(V value) {
      V oldValue = this.value;
      this.value = value;
      return oldValue;
    }
  }
 
}
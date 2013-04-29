import java.util.Map;
import java.util.Map.Entry;


public class FakeMap {
  
  private int size = 0;
  private Object[] table;
  private static Object[] EMPTY_TABLE = new Object[2];

  public FakeMap() { this.table = EMPTY_TABLE; }

  public FakeMap(Map map) {
    if (map.size() < 1) this.table = EMPTY_TABLE;
    else this.table = new Object[8];
    constructorPutAll(map);
  }

  private void constructorPutAll(Map<Object,Object>  map) {
    for (Entry<Object,Object> e : map.entrySet()) {
      constructorPut(e.getKey(), e.getValue());
    }
  }

  private void constructorPut(Object key, Object value) {  
    if (key == null) return;
    int index = key.hashCode() & (table.length - 1);
    Entry newEntry = new FakeMapEntry(key, value);
    Assertions.Assert(table != EMPTY_TABLE);
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
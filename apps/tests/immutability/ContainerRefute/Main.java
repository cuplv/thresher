import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.HashMap;


class Main {

    public static void main(String[] args) {
	Map<Integer, List<String>> m = new HashMap<Integer, List<String>>();
	m.put(5, new LinkedList<String>());
	List<String> s = m.get(5);
	


	for (String key : m.keySet()) {
	    List<String> l = m.get(keys[i]);
	    if (l == null) {
		l = new ArrayList<String>();
		m.put(keys[i], l);
	    }
	    m.put(key, Collections.unmodifiableList(m.get(key)));
	}

	LinkedList<String> l = new LinkedList<String>();
	m.write("hi");
	List<String> immutable = Collections.unmodifiableList(l);
	m.f = immutable;
    }
}
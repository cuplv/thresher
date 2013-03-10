import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;


class Main {

    public static void main(String[] args) {

	Map<Integer, List<String>> m = new HashMap<Integer, List<String>>();
	m.put(5, new LinkedList<String>());
	List<String> s = m.get(5);
	s.add("hi");
	for (int key : m.keySet()) {
	    m.put(key, Collections.unmodifiableList(m.get(key)));
	}
    }
}
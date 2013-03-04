import java.util.Collections;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;


class Main {

    public static void main(String[] args) {
	List<List<String>> m = new ArrayList<List<String>>();
	m.add(new ArrayList<String>());
	List<String> s = m.get(0);
	m.set(0, Collections.unmodifiableList(s));
	m.get(0).add("hi");

	/*
	Map<Integer, List<String>> m = new HashMap<Integer, List<String>>();
	m.put(5, new LinkedList<String>());

	for (int key : m.keySet()) {
	    m.put(key, Collections.unmodifiableList(m.get(key)));
	}

	List<String> s = m.get(5);
	s.add("hi");
	*/
    }
}
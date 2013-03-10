import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;


class Main {

    static class Foo {
	public Foo() { }
    }

    public Main() { }

    public static void main(String[] args) {
	Map<Integer, List<String>> m = new HashMap<Integer, List<String>>();
	Main o = new Main();
	m.put(5, new LinkedList<String>());
	Foo f = new Foo();
	for (int key : m.keySet()) {
	    m.put(key, Collections.unmodifiableList(m.get(key)));
	}

	List<String> s = m.get(5);
	s.add("hi");
    }
}
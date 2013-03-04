import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.ArrayList;

class Main {

    public static void main(String[] args) {
	List<List<String>> m = new ArrayList<List<String>>();
	m.add(new ArrayList<String>());
	List<String> s = m.get(0);
	m.get(0).add("hi");
	m.set(0, Collections.unmodifiableList(s));
    }
}
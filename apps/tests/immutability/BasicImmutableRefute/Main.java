import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	LinkedList<String> l = new LinkedList<String>();
	l.add("hi");
	List<String> immutable = Collections.unmodifiableList(l);
    }
}
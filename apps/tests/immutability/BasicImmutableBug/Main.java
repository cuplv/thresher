import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	LinkedList<String> l = new LinkedList<String>();
	List<String> immutable = Collections.unmodifiableList(l);
	immutable.add("hi");
    }
}
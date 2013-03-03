import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public List<String> f;

    public Main() {

    }

    public void write(String s) {
	if (f != null) {
	    f.add(s);
	}
    } 

    public static void main(String[] args) {
	Main m = new Main();

	LinkedList<String> l = new LinkedList<String>();
	m.write("hi");
	List<String> immutable = Collections.unmodifiableList(l);
	m.f = immutable;
    }
}
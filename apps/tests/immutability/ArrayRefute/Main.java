import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;


class Main {

    public static void main(String[] args) {
	List<String>[] arr = new List[5];
	arr[0] = new LinkedList<String>();
	arr[0].add("hi");
	arr[0] = Collections.unmodifiableList(arr[0]);
    }
}
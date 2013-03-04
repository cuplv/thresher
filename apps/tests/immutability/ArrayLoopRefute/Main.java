import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;


class Main {

    public static void main(String[] args) {
	List<String>[] arr = new List[5];
	for (int i = 0; i < arr.length; i++) {
	    arr[i] = new LinkedList<String>();
	}

	arr[0].add("hi");

	for (int i = 0; i < arr.length; i++) {
	    arr[i] = Collections.unmodifiableList(arr[0]);
	}

    }
}
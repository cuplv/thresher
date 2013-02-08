public class Node {

    Node next; Object data;

    public Node() {}

    public static Node appendNode(Node n) {
	Node t = new Node();
	n.next = t;
	return t;  
    }

}
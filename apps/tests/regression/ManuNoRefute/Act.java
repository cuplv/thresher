public class Act {
    public Act() {}
    
    public static Node storyCache;

    public static void main(String[] args) {

	Node x0 = new Node();
	storyCache = x0;
	Node x1 = Node.appendNode(x0);
	Node x2 = Node.appendNode(x1);
	x2.data = new Act();
    }
}
import java.util.ArrayList;

public class Act {

    int size;

    public Act() {}
    
    public static ArrayList<Object> storyCache = new ArrayList<Object>();

    public static void main(String[] args) {
	//	ArrayList<Act> localList = new ArrayList<Act>();
	//	localList.set(3, new Act());
	storyCache.add(new Object());
	storyCache.set(0, new Act());
	//storyCache.put("b", new Object());
	//storyCache.put("b", new Act());
	//storyCache.put(new Object());
    }
}
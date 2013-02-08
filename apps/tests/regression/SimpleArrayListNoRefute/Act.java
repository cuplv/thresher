import java.util.ArrayList;

public class Act {

    int size;

    public Act() {}
    
    public static ArrayList<Act> storyCache = new ArrayList<Act>();

    public static void main(String[] args) {
	//	ArrayList<Act> localList = new ArrayList<Act>();
	//	localList.add(new Act());
	storyCache.add(new Act());
    }
}
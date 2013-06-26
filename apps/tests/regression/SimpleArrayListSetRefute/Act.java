import edu.colorado.thresher.external.Annotations.*;
import java.util.ArrayList;

@noStaticRef public class Act {

    int size;

    public Act() {}
    
    public static ArrayList<Object> storyCache = new ArrayList<Object>();

    public static void main(String[] args) {
	//	ArrayList<Act> localList = new ArrayList<Act>();
	//	localList.set(3, new Act());
	storyCache.set(0, new Act());
	//storyCache.put("b", new Object());
	//storyCache.put("b", new Act());
	//storyCache.put(new Object());
    }
}
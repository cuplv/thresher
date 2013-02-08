import java.util.HashMap;
import java.util.Map;

public class Act {

    int size;

    public Act() {}
    
    public static Map<String,Object> storyCache = new HashMap<String,Object>();

    public static void main(String[] args) {
	Map<String,Act> localMap = new HashMap<String,Act>();
	localMap.put("a", new Act());
	storyCache.put("b", new Object());
	//storyCache.put("b", new Act());
	//storyCache.put(new Object());
    }
}
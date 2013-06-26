import edu.colorado.thresher.external.Annotations.*;
import java.util.WeakHashMap;

@noStaticRef public class Act {

    int size;

    public Act() {}
    
    public static WeakHashMap<String,Object> storyCache = new WeakHashMap<String,Object>();

    public static void main(String[] args) {
	WeakHashMap<String,Act> localMap = new WeakHashMap<String,Act>();
	localMap.put("a", new Act());
	storyCache.put("b", new Object());
	//storyCache.put("b", new Act());
	//storyCache.put(new Object());
    }
}
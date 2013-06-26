import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static SuperMap storyCache = new FakeMap();

    public static void main(String[] args) {
	
	SuperMap localMap;
	if (nondet()) {
	    localMap = new FakeMap();
	} else {
	    localMap = new SuperMap();
	}
	localMap.put("a", new Act());

	storyCache.put("b", new Object());
    }

    public static boolean nondet() {
	return true;
    }
}
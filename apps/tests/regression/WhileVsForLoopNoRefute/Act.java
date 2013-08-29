import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static Object storyCache;

    public void foo(int i ) { 
	if (i == 1) this.f = new Act(); 
	else this.f = new Object();
    }   

    public static int getInt() { return 1; }

    public void method() {
	int x = getInt();
	int j = 0;
	for (int i = 0; i < 17; foo(x), i++) {	    
	    j++;
	    if (j == 1) continue;	    
	    else if (j == 2) {
		j /= 1;
		break;
	    }
	    storyCache = new Object();
	    j *= 1;
	    break;
	}
	storyCache = this.f;
    }
    
    public Object f;

    public static void main(String[] args) {
	Act a = new Act();
	a.method();
    }

}
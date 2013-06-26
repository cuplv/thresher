package com.example.helloandroid;

import android.app.*;
import android.content.*;
import android.graphics.drawable.*;
import android.os.*;
import android.test.mock.*;
import android.widget.*;

public class HelloAndroid extends Activity {
    
    private static Drawable sBackground;
    
    @Override
    public void onCreate(Bundle state) {
    	super.onCreate(state);

    	TextView label = new TextView(this);
    	label.setText("Leaks are bad");
    	label.onTouchEvent(null);

    	//DrawableContainer local = new DrawableContainer();
    	if (sBackground == null) {
    		sBackground = new DrawableContainer();
    	}
    	label.setBackgroundDrawable(sBackground);
    	//label.setBackgroundDrawable(local);
    	setContentView(label);
    }
        
    
    /*
    public void fakeStart() {
    	Context ctx = new MockContext();
    	HelloAndroid act = new HelloAndroid();
    	act.attach(this, null, null, null, null, null, null, null, this, null, null, null);
    	act.onCreate(new Bundle());
    	act.attachBaseContext(this);
    	//this.attach(this, null, null, null, null, null, null, null, this, null, null, null);
    	this.attach(this, null, null, null, null, null, null, null, this, null, null, null);
    	attachBaseContext(this);
    	Intent myIntent = new Intent(act, HelloAndroid.class);
    	Intent myIntent2 = new Intent(this, HelloAndroid.class);
    	this.startActivity(myIntent);
    	this.startActivity(myIntent2);
    	this.onCreate(new Bundle());
    }
*/
 
	/*
	//private static final LinkedList<String> storyCache = new LinkedList<String>();
	//private static final HashMap<Object,Object> storyCache = new HashMap<Object,Object>();
	private static final FakeMap<String,String> storyCache = new FakeMap<String,String>();
	//private static final FakeMap<String,String> storyCache = new FakeMap<String,String>(1);
	  */
	  //@Override
	    //public void onCreate(Bundle savedInstanceState) {
		 // FakeMap<String,Activity> acts = new FakeMap<String,Activity>();
		  //acts.put("5", this);
		  
		  //Object x = new Object();
		  //while (true) { 
			//  Mine m = new Mine();
		  //}
		  //Mine g = new Mine();
		  
		  // 1
		  //List<CategorizedProgram> orderedList = new ArrayList<CategorizedProgram>();
		  //orderedList.add(new CategorizedProgram());
		  // 2
		  //HashMap<String, Activity> acts = new HashMap<String, Activity>();
		  //acts.put("5", this);
		  // 3
		  //storyCache.add("5");
		  //LinkedList<Activity> l = new LinkedList<Activity>();
		  //l.add(this);
		  //Activity acts[] = new Activity[20];
		  //acts[0] = this;
		  
	  }
	  
	// private class CategorizedProgram {
		// public CategorizedProgram() {}
	  //}
	  
/*	
    //private static Drawable sBackground;
	private static LinkedList<Drawable> sBackground;
    private static int instance_num = 0;
    private static int drawables_created = 0;

    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
	
        TextView label = new TextView(this);
        label.setText("THIS IS MY TEXT " + (++instance_num));
        if (sBackground == null) {
        	sBackground = new LinkedList<Drawable>();
        	//label.setText("THIS IS MY TEXT " + instance_num + " " + (++drawables_created));
        	//sBackground = new BitmapDrawable();
        	sBackground.add(new BitmapDrawable());
        }
        //label.setBackgroundDrawable(sBackground);
        label.setBackgroundDrawable(sBackground.get(0));
    	//Drawable d = new BitmapDrawable();
    	//label.setBackgroundDrawable(d);	
        setContentView(label);
        
        
        //act.onCreate(savedInstanceState);
    }
  */  
	/*
    private static ArrayList<ApplicationInfo> mApplications;
	  @Override
	    public void onDestroy() {
	        super.onDestroy();

	        // Remove the callback for the cached drawables or we leak
	        // the previous Home screen on orientation change
	        final int count = mApplications.size();
	        for (int i = 0; i < count; i++) {
	            mApplications.get(i).icon.setCallback(null);
	        }
	  }
	  */
//}
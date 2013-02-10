package org.jtb.droidlife;

import java.util.ArrayList;
import java.util.List;

import android.app.Activity;
import android.util.Log;
import android.view.MotionEvent;
import android.view.View;

public class SwipeDetector implements View.OnTouchListener {
	public static interface SwipeListener {
		void onRightToLeft();

		void onLeftToRight();

		void onTopToBottom();

		void onBottomToTop();
	}

	private Activity activity;
	static final int MIN_DISTANCE = 100;
	private float downX, downY, upX, upY;
	List<SwipeListener> listeners = new ArrayList<SwipeListener>();

	void addListener(SwipeListener listener) {
		listeners.add(listener);
	}

	public void onRightToLeftSwipe() {
		//Log.i("droidlife", "RightToLeftSwipe!");
		for (SwipeListener sl : listeners) {
			sl.onRightToLeft();
		}
	}

	public void onLeftToRightSwipe() {
		//Log.i("droidlife", "LeftToRightSwipe!");
		for (SwipeListener sl : listeners) {
			sl.onLeftToRight();
		}
	}

	public void onTopToBottomSwipe() {
		//Log.i("droidlife", "onTopToBottomSwipe!");
		for (SwipeListener sl : listeners) {
			sl.onTopToBottom();
		}
	}

	public void onBottomToTopSwipe() {
		//Log.i("droidlife", "onBottomToTopSwipe!");
		for (SwipeListener sl : listeners) {
			sl.onBottomToTop();
		}
	}

	public boolean onTouch(View v, MotionEvent event) {
		switch (event.getAction()) {
		case MotionEvent.ACTION_DOWN: {
			downX = event.getX();
			downY = event.getY();
			return false;
		}
		case MotionEvent.ACTION_UP: {
			upX = event.getX();
			upY = event.getY();

			float deltaX = downX - upX;
			float deltaY = downY - upY;

			// swipe horizontal?
			if (Math.abs(deltaX) > MIN_DISTANCE) {
				// left or right
				if (deltaX < 0) {
					this.onLeftToRightSwipe();
					return true;
				}
				if (deltaX > 0) {
					this.onRightToLeftSwipe();
					return true;
				}
			} else {
//				Log.i("droidlife", "horizontal swipe was only " + Math.abs(deltaX)
//						+ " long, need at least " + MIN_DISTANCE);
			}

			// swipe vertical?
			if (Math.abs(deltaY) > MIN_DISTANCE) {
				// top or down
				if (deltaY < 0) {
					this.onTopToBottomSwipe();
					return true;
				}
				if (deltaY > 0) {
					this.onBottomToTopSwipe();
					return true;
				}
			} else {
//				Log.i("droidlife", "vertical was only " + Math.abs(deltaY)
//						+ " long, need at least " + MIN_DISTANCE);
			}
		}
		}
		return false;
	}

}
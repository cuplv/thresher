package org.jtb.droidlife;

import org.jtb.droidlife.model.World;

import android.content.Context;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.RectF;
import android.os.Handler;
import android.util.AttributeSet;
import android.util.Log;
import android.view.SurfaceHolder;
import android.view.SurfaceView;

class DesignView extends SurfaceView implements Seedable {

	private static Paint POINT_PAINT = new Paint();
	private static Paint XY_PAINT = new Paint();

	static {
		POINT_PAINT.setColor(Color.BLUE);
		POINT_PAINT.setStyle(Paint.Style.STROKE);
		POINT_PAINT.setStrokeWidth(0);

		XY_PAINT.setColor(Color.DKGRAY);
		XY_PAINT.setStyle(Paint.Style.STROKE);
		XY_PAINT.setStrokeWidth(0);
	}

	private Context mContext;
	private int mCanvasWidth;
	private int mCanvasHeight;
	private World mWorld;
	private SurfaceHolder mSurfaceHolder;
	private Prefs prefs;
	private Handler mActivityHandler;
	private int mCellSize;
	private int mX, mY;
	private int mXMid, mYMid;
	private int mXMax, mYMax;
	private Seeder mSeeder;

	public DesignView(Context context, AttributeSet attrs) {
		super(context, attrs);

		mContext = context;
		setFocusable(true); // make sure we get key events
		prefs = new Prefs(context);
		mCellSize = prefs.getCellSize();
	}

	@Override
	public void onWindowFocusChanged(boolean hasWindowFocus) {
	}

	public void setSize(int width, int height) {
		mCanvasWidth = width;
		mCanvasHeight = height;
	}

	public void setSurfaceHolder(SurfaceHolder surfaceHolder) {
		this.mSurfaceHolder = surfaceHolder;
	}

	public boolean isSeeded() {
		return mWorld != null;
	}

	public void seed(Seeder seeder) {
		mSeeder = seeder;

		int[] birthNeighbors = prefs.getBirthRule();
		int[] surviveNeighbors = prefs.getSurvivalRule();

		mWorld = new World(mCanvasWidth / mCellSize, mCanvasHeight / mCellSize,
				mCellSize, birthNeighbors, surviveNeighbors, prefs.isWrap());

		mXMax = mWorld.current.length - 1;
		mYMax = mWorld.current[0].length - 1;
		mXMid = mXMax / 2;
		mYMid = mYMax / 2;
		mX = mXMid;
		mY = mYMid;

		if (mSeeder != null) {
			mSeeder.seed(mWorld, false);
		}

		draw();
	}

	public boolean isLiving() {
		return mWorld.current[mX][mY].isLiving();
	}

	public void toggle() {
		if (mWorld.current[mX][mY].isLiving()) {
			mWorld.current[mX][mY].die();
		} else {
			mWorld.current[mX][mY].spawn(Color.WHITE);
		}
		draw();
	}

	private void drawPointer(Canvas c) {
		RectF rect = new RectF();
		int rx1 = mX * mCellSize - mCellSize / 2;
		int ry1 = mY * mCellSize - mCellSize / 2;
		int rx2 = mX * mCellSize + mCellSize / 2;
		int ry2 = mY * mCellSize + mCellSize / 2;

		rect.set(rx1, ry1, rx2, ry2);
		c.drawRect(rect, POINT_PAINT);
	}

	private void drawXY(Canvas c) {
		int x1 = mXMid * mCellSize;
		int y1 = 0;
		int x2 = x1;
		int y2 = mYMax * mCellSize;

		c.drawLine(x1, y1, x2, y2, XY_PAINT);

		x1 = 0;
		y1 = mYMid * mCellSize;
		x2 = mXMax * mCellSize;
		y2 = y1;

		c.drawLine(x1, y1, x2, y2, XY_PAINT);

	}

	public void refresh() {
		draw();
	}

	private void draw() {
		Canvas c = null;
		try {
			c = mSurfaceHolder.lockCanvas(null);
			if (c == null) {
				Log.w(getClass().getSimpleName(),
						"tried to draw with null canvas");
				return;
			}
			synchronized (mSurfaceHolder) {
				c.drawARGB(255, 0, 0, 0);
				drawXY(c);
				mWorld.draw(c);
				drawPointer(c);
			}
		} finally {
			if (c != null) {
				mSurfaceHolder.unlockCanvasAndPost(c);
			}
		}

		int x = mX - mXMid;
		int y = mY - mYMid;

		mActivityHandler.sendMessage(mActivityHandler.obtainMessage(
				DesignActivity.UPDATE_X_WHAT, Integer.valueOf(x)));
		mActivityHandler.sendMessage(mActivityHandler.obtainMessage(
				DesignActivity.UPDATE_Y_WHAT, Integer.valueOf(y)));

	}

	public void die() {
		mWorld.current[mX][mY].die();
		draw();
	}

	public void clear() {
		mWorld.clear();
		draw();
	}

	public void setActivityHandler(Handler mActivityHandler) {
		this.mActivityHandler = mActivityHandler;
	}

	public void moveX(int dir) {
		if (dir > 0) {
			mX = Math.min(mXMax, mX + dir);
		} else {
			mX = Math.max(0, mX + dir);
		}
		draw();
	}

	public void moveY(int dir) {
		if (dir > 0) {
			mY = Math.min(mYMax, mY + dir);
		} else {
			mY = Math.max(0, mY + dir);
		}
		draw();
	}

	public String save(String name) {
		SeedSource ss;

		if (mSeeder == null) {
			ss = SeedSource.DEFAULT_WRITABLE;
		} else if (!mSeeder.getSeedSource().isWritable()) {
			ss = SeedSource.DEFAULT_WRITABLE;
		} else {
			ss = mSeeder.getSeedSource();
		}

		if (!ss.isWritable()) {
			throw new AssertionError("seed is not writable");
		}

		ss.writeSeed(name, mWorld);
		SeederManager.getInstance(mContext).refresh();

		return name;
	}

}

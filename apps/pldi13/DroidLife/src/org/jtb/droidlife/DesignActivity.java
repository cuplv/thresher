package org.jtb.droidlife;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.SharedPreferences;
import android.content.SharedPreferences.OnSharedPreferenceChangeListener;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.preference.PreferenceManager;
//import android.support.v4.view.MenuItemCompat;
import android.util.Log;
import android.view.KeyEvent;
import android.view.Menu;
import android.view.MenuItem;
import android.view.SurfaceHolder;
import android.view.View;
import android.view.Window;
import android.view.View.OnClickListener;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.TextView;
import android.widget.Toast;

public class DesignActivity extends Activity implements SurfaceHolder.Callback {
	private static final int HELP_DIALOG = 0;
	private static final int INFO_DIALOG = 2;

	private static final int MENU_SIMULATE = 0;
	private static final int MENU_CLEAR = 1;
	private static final int MENU_HELP = 2;
	private static final int MENU_INFO = 3;

	static final int UPDATE_X_WHAT = 0;
	static final int UPDATE_Y_WHAT = 1;

	private static final int SIMULATE_REQUEST = 0;

	private AlertDialog mHelpDialog;
	private AlertDialog mInfoDialog;

	private DesignView mDesignView;
	private Menu mMenu;
	private LinearLayout mMainLayout;
	private Prefs mPrefs;
	private TextView mXText;
	private TextView mYText;
	private String mName;
	private Integer mPosition = null;
	private TextView mNameText;

	private Handler mHandler = new Handler() {
		@Override
		public void handleMessage(Message msg) {
			switch (msg.what) {
			case UPDATE_X_WHAT:
				int x = (Integer) msg.obj;
				mXText.setText("X: " + x);
				break;
			case UPDATE_Y_WHAT:
				int y = (Integer) msg.obj;
				mYText.setText("Y: " + y);
				break;
			}
		}
	};

	@Override
	public boolean onCreateOptionsMenu(Menu menu) {
		super.onCreateOptionsMenu(menu);
		mMenu = menu;
		MenuItem mi;
		
		mi = menu.add(0, MENU_SIMULATE, 0, R.string.menu_simulate).setIcon(
				android.R.drawable.ic_menu_share);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);
		mi = menu.add(0, MENU_CLEAR, 0, R.string.menu_clear).setIcon(
				android.R.drawable.ic_menu_close_clear_cancel);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);
		mi = menu.add(0, MENU_HELP, 0, R.string.menu_help).setIcon(
				android.R.drawable.ic_menu_help);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_NEVER);
		mi = menu.add(0, MENU_INFO, 0, R.string.menu_info).setIcon(
				android.R.drawable.ic_menu_info_details);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_NEVER);

		return true;
	}

	@Override
	public boolean onPrepareOptionsMenu(Menu menu) {
		return true;
	}

	@Override
	public boolean onOptionsItemSelected(MenuItem item) {
		switch (item.getItemId()) {
		case MENU_CLEAR:
			mDesignView.clear();
			return true;
		case MENU_SIMULATE:
			save();
			mPosition = SeederManager.getInstance(this).getPosition(mName);
			Intent i = new Intent(this, GameActivity.class);
			i.putExtra("org.jtb.droidlife.seeder.position", mPosition);
			startActivity(i);
			return true;
		case MENU_HELP:
			showDialog(HELP_DIALOG);
			return true;
		case MENU_INFO:
			showDialog(INFO_DIALOG);
			return true;
		}

		return false;
	}

	public String save() {
		mName = mDesignView.save(mName);
		return mName;
	}

	@Override
	protected void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		setContentView(R.layout.design);

		mDesignView = (DesignView) findViewById(R.id.design_view);
		mDesignView.setActivityHandler(mHandler);
		mDesignView.getHolder().addCallback(this);
		mDesignView.setOnClickListener(new OnClickListener() {
			@Override
			public void onClick(View arg0) {
				mDesignView.toggle();
			}
		});

		mMainLayout = (LinearLayout) findViewById(R.id.main_layout);
		mXText = (TextView) findViewById(R.id.x_text);
		mYText = (TextView) findViewById(R.id.y_text);
		mNameText = (TextView) findViewById(R.id.name_text);

		mPrefs = new Prefs(this);

		mPosition = savedInstanceState != null ? (Integer) savedInstanceState
				.get("org.jtb.droidlife.seeder.position") : null;
		if (mPosition == null) {
			Bundle extras = getIntent().getExtras();
			mPosition = extras != null ? (Integer) extras
					.get("org.jtb.droidlife.seeder.position") : null;
		}
		if (mPosition != null) {
			mName = SeederManager.getInstance(this).getSeeder(mPosition)
					.getName();
		} else {
			mName = savedInstanceState != null ? (String) savedInstanceState
					.get("org.jtb.droidlife.seeder.name") : null;
			if (mName == null) {
				Bundle extras = getIntent().getExtras();
				mName = extras != null ? (String) extras
						.get("org.jtb.droidlife.seeder.name") : null;
			}
			if (mName == null) {
				Log.e(getClass().getSimpleName(), "no name passed");
				return;
			}
		}
		mNameText.setText("Designing: " + mName);

		SwipeDetector sd = new SwipeDetector();
		mDesignView.setOnTouchListener(sd);
		sd.addListener(new SwipeDetector.SwipeListener() {

			@Override
			public void onTopToBottom() {
				mDesignView.moveY(1);
			}

			@Override
			public void onRightToLeft() {
				mDesignView.moveX(-1);
			}

			@Override
			public void onLeftToRight() {
				mDesignView.moveX(1);
			}

			@Override
			public void onBottomToTop() {
				mDesignView.moveY(-1);
			}
		});
	}

	@Override
	protected void onPause() {
		super.onPause();
	}

	@Override
	protected void onResume() {
		super.onResume();
	}

	protected Dialog onCreateDialog(int id) {
		AlertDialog.Builder builder;

		switch (id) {
		case HELP_DIALOG:
			builder = new CustomDialog.Builder(this, R.layout.design_help);
			mHelpDialog = builder.create();
			return mHelpDialog;
		case INFO_DIALOG:
			builder = new CustomDialog.Builder(this, R.layout.info);
			mInfoDialog = builder.create();
			return mInfoDialog;
		}

		return null;
	}

	public boolean onKeyDown(int keyCode, KeyEvent event) {
		switch (keyCode) {
		case KeyEvent.KEYCODE_BACK:
			save();
			break;
		case KeyEvent.KEYCODE_DPAD_CENTER:
			mDesignView.toggle();
			break;
		case KeyEvent.KEYCODE_DPAD_LEFT:
			mDesignView.moveX(-1);
			break;
		case KeyEvent.KEYCODE_DPAD_RIGHT:
			mDesignView.moveX(1);
			break;
		case KeyEvent.KEYCODE_DPAD_UP:
			mDesignView.moveY(-1);
			break;
		case KeyEvent.KEYCODE_DPAD_DOWN:
			mDesignView.moveY(1);
			break;
		}
		return super.onKeyDown(keyCode, event);
	}

	protected void onActivityResult(int requestCode, int resultCode, Intent data) {
		switch (requestCode) {
		}
	}

	private void seed() {
		AlertDialog.Builder builder = null;
		Seeder seeder = null;

		if (mPosition != null) {
			seeder = SeederManager.getInstance(this).getSeeder(mPosition);
			mDesignView.seed(seeder);
		} else {
			mDesignView.seed(null);
		}
	}

	public void surfaceChanged(SurfaceHolder holder, int format, int width,
			int height) {
		mDesignView.setSize(width, height);
		seed();
	}

	public void surfaceCreated(SurfaceHolder holder) {
		mDesignView.setSurfaceHolder(holder);
	}

	public void surfaceDestroyed(SurfaceHolder holder) {
	}
}

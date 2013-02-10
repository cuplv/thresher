package org.jtb.droidlife;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.SharedPreferences.OnSharedPreferenceChangeListener;
import android.os.Bundle;
import android.os.Debug;
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
import android.view.View.OnClickListener;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.TextView;

public class GameActivity extends Activity implements
		OnSharedPreferenceChangeListener, SurfaceHolder.Callback {

	private static final int DESIGN_REQUEST = 0;

	static final int UPDATE_TYPE_WHAT = 0;
	static final int UPDATE_GEN_WHAT = 1;
	static final int UPDATE_POP_WHAT = 2;
	static final int UPDATE_STATUS_WHAT = 3;
	static final int UPDATE_NAME_WHAT = 4;

	static final int HELP_DIALOG = 0;
	static final int INFO_DIALOG = 1;
	static final int GAME_EDIT_DIALOG = 2;

	private static final int MENU_PLAY = 0;
	private static final int MENU_PAUSE = 1;
	private static final int MENU_RESEED = 2;
	private static final int MENU_HELP = 3;
	private static final int MENU_INFO = 4;
	private static final int MENU_EDIT = 5;

	private AlertDialog mHelpDialog;
	private AlertDialog mInfoDialog;
	private AlertDialog mGameEditDialog;

	private GameView mGameView;
	private Menu mMenu;
	private TextView mGenText;
	private TextView mTypeText;
	private TextView mPopText;
	private TextView mNameText;
	private ImageView mStatusImage;
	private LinearLayout mMainLayout;
	private Prefs mPrefs;
	private Integer mPosition;

	private Handler mHandler = new Handler() {
		@Override
		public void handleMessage(Message msg) {
			switch (msg.what) {
			case UPDATE_TYPE_WHAT:
				String type = (String) msg.obj;
				mTypeText.setText("Type: " + type);
				break;
			case UPDATE_NAME_WHAT:
				String name = (String) msg.obj;
				mNameText.setText("Simulating: " + name);
				break;
			case UPDATE_GEN_WHAT:
				int gen = (Integer) msg.obj;
				mGenText.setText(String.format("Gen: %06d", gen));
				break;
			case UPDATE_POP_WHAT:
				int pop = (Integer) msg.obj;
				mPopText.setText(String.format("Pop: %04d", pop));
				break;
			case UPDATE_STATUS_WHAT:
				boolean playing = (Boolean) msg.obj;
				if (playing) {
					mStatusImage.setImageResource(R.drawable.play);
				} else {
					mStatusImage.setImageResource(R.drawable.pause);
				}
				setMenu();
				break;
			}
		}
	};

	@Override
	public boolean onCreateOptionsMenu(Menu menu) {
		super.onCreateOptionsMenu(menu);
		mMenu = menu;
		MenuItem mi;
		
		mi = menu.add(1, MENU_PLAY, 0, R.string.menu_play).setIcon(
				android.R.drawable.ic_media_play);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);

		mi = menu.add(2, MENU_PAUSE, 1, R.string.menu_pause).setIcon(
				android.R.drawable.ic_media_pause);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);
		
		mi = menu.add(3, MENU_RESEED, 2, R.string.menu_reseed).setIcon(
				android.R.drawable.ic_menu_share);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);

		mi = menu.add(0, MENU_EDIT, 3, R.string.menu_edit).setIcon(
				android.R.drawable.ic_menu_edit);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);

		mi = menu.add(3, MENU_HELP, 4, R.string.menu_help).setIcon(
				android.R.drawable.ic_menu_help);
		//MenuItemCompat.setShowAsAction(mi,
				//MenuItemCompat.SHOW_AS_ACTION_NEVER);

		mi = menu.add(3, MENU_INFO, 5, R.string.menu_info).setIcon(
				android.R.drawable.ic_menu_info_details);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_NEVER);
		
		return true;
	}

	private void setMenu() {
		if (mMenu == null) {
			return;
		}
		
		if (mGameView.isRunning()) {
			mMenu.setGroupVisible(0, false);
			mMenu.setGroupVisible(1, false);
			mMenu.setGroupVisible(2, true);
		} else if (mGameView.isSeeded()) {
			mMenu.setGroupVisible(0, true);
			mMenu.setGroupVisible(1, true);
			mMenu.setGroupVisible(2, false);
		} else {
			mMenu.setGroupVisible(0, true);
			mMenu.setGroupVisible(1, false);
			mMenu.setGroupVisible(2, false);
		}		
	}
	
	@Override
	public boolean onPrepareOptionsMenu(Menu menu) {	
		setMenu();
		return true;
	}

	@Override
	public boolean onOptionsItemSelected(MenuItem item) {
		switch (item.getItemId()) {
		case MENU_PLAY:
			//Debug.startMethodTracing("gameview");
			mGameView.start();
			break;
		case MENU_PAUSE:
			mGameView.stop();
			//Debug.stopMethodTracing();
			break;
		case MENU_RESEED:
			if (mGameView.isRunning()) {
				mGameView.stop();
			}
			seed();
			break;
		case MENU_HELP:
			showDialog(HELP_DIALOG);
			break;
		case MENU_INFO:
			showDialog(INFO_DIALOG);
			break;
		case MENU_EDIT:
			showDialog(GAME_EDIT_DIALOG);
			break;
		}
		return true;
	}

	public void save(String name) {
		name = mGameView.save(name);
		mPosition = SeederManager.getInstance(this).getPosition(name);
	}

	@Override
	protected void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		setContentView(R.layout.game);

		mGameView = (GameView) findViewById(R.id.game);
		mGameView.setActivityHandler(mHandler);
		mGameView.getHolder().addCallback(this);
		mGameView.setOnClickListener(new OnClickListener() {
			@Override
			public void onClick(View arg0) {
				if (mGameView.isRunning()) {
					mGameView.stop();
				} else if (mGameView.isSeeded()) {
					mGameView.start();
				}
			}
		});

		mTypeText = (TextView) findViewById(R.id.type_text);
		mGenText = (TextView) findViewById(R.id.generation_text);
		mPopText = (TextView) findViewById(R.id.population_text);
		mNameText = (TextView) findViewById(R.id.name_text);
		mStatusImage = (ImageView) findViewById(R.id.status_image);
		mMainLayout = (LinearLayout) findViewById(R.id.main_layout);

		mPrefs = new Prefs(this);

		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(this);
		prefs.registerOnSharedPreferenceChangeListener(this);

		mPosition = savedInstanceState != null ? (Integer) savedInstanceState
				.get("org.jtb.droidlife.seeder.position") : null;
		if (mPosition == null) {
			Bundle extras = getIntent().getExtras();
			mPosition = extras != null ? (Integer) extras
					.get("org.jtb.droidlife.seeder.position") : null;
		}
		if (mPosition == null) {
			Log.e(getClass().getSimpleName(), "no position passed");
			return;
		}

		SwipeDetector sd = new SwipeDetector();
		mGameView.setOnTouchListener(sd);
		sd.addListener(new SwipeDetector.SwipeListener() {

			@Override
			public void onTopToBottom() {
				// TODO Auto-generated method stub

			}

			@Override
			public void onRightToLeft() {
				if (mGameView.isSeeded() && !mGameView.isRunning()) {
					mGameView.step();
				}
			}

			@Override
			public void onLeftToRight() {
				// TODO Auto-generated method stub

			}

			@Override
			public void onBottomToTop() {
				mGameView.stop();
				seed();
			}
		});
	}

	private void seed() {
		Seeder seeder = SeederManager.getInstance(this).getSeeder(mPosition);
		mGameView.seed(seeder);
	}

	@Override
	protected void onPause() {
		super.onPause();
		mGameView.stop();
	}

	@Override
	protected void onResume() {
		super.onResume();
	}

	protected Dialog onCreateDialog(int id) {
		AlertDialog.Builder builder;

		switch (id) {
		case GAME_EDIT_DIALOG:
			builder = new GameEditDialog.Builder(this);
			mGameEditDialog = builder.create();
			return mGameEditDialog;
		case HELP_DIALOG:
			builder = new CustomDialog.Builder(this, R.layout.game_help);
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
		case KeyEvent.KEYCODE_DPAD_CENTER:
			if (mGameView.isRunning()) {
				mGameView.stop();
			} else if (mGameView.isSeeded()) {
				mGameView.start();
			}
			break;
		case KeyEvent.KEYCODE_DPAD_RIGHT:
			if (mGameView.isSeeded() && !mGameView.isRunning()) {
				mGameView.step();
			}
			break;
		case KeyEvent.KEYCODE_DPAD_UP:
			seed();
			break;
		}
		return super.onKeyDown(keyCode, event);
	}

	public void onSharedPreferenceChanged(SharedPreferences sp, String key) {
		Log.d(getClass().getSimpleName(), "pref changed:" + key);
		if (key.equals("keepScreenOn")) {
			mMainLayout.setKeepScreenOn(mPrefs.isKeepScreenOn());
		}
	}

	protected void onActivityResult(int requestCode, int resultCode, Intent data) {
		switch (requestCode) {
		case DESIGN_REQUEST:
			// ?
			break;
		}
	}

	public void surfaceChanged(SurfaceHolder holder, int format, int width,
			int height) {
		mGameView.setSize(width, height);
		seed();
	}

	public void surfaceCreated(SurfaceHolder holder) {
		mGameView.setSurfaceHolder(holder);
	}

	public void surfaceDestroyed(SurfaceHolder holder) {
		mGameView.stop();
	}
}

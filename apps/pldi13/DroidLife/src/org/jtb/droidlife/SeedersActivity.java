package org.jtb.droidlife;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.content.Intent;
import android.os.Bundle;
//import android.support.v4.view.MenuItemCompat;
import android.view.Menu;
import android.view.MenuItem;
import android.view.View;
import android.widget.AdapterView;
import android.widget.AdapterView.OnItemClickListener;
import android.widget.AdapterView.OnItemLongClickListener;
import android.widget.ListView;
import android.widget.TextView;

public class SeedersActivity extends Activity {
	private static final int HELP_DIALOG = 0;
	private static final int NEW_DIALOG = 1;
	private static final int INFO_DIALOG = 2;

	private static final int MENU_NEW = 0;
	private static final int MENU_PREFS = 1;
	private static final int MENU_HELP = 2;
	private static final int MENU_INFO = 3;

	static final int DESIGN_REQUEST = 0;

	private ListView mSeederList;
	private SeedersActivity mThis;
	private TextView mEmptyListText;

	private AlertDialog mHelpDialog;
	private AlertDialog mInfoDialog;
	private AlertDialog mSeederClickDialog;
	private AlertDialog mNewDialog;

	@Override
	public void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		setContentView(R.layout.seeders);

		AssetCopier ac = new AssetCopier(this);
		ac.copy();

		mThis = this;

		mSeederList = (ListView) findViewById(R.id.seeder_list);
		mSeederList.setOnItemClickListener(new OnItemClickListener() {
			public void onItemClick(AdapterView<?> parent, View v,
					int position, long id) {
				Seeder seeder = SeederManager.getInstance(mThis).getSeeder(
						position);

				AlertDialog.Builder builder = seeder.getSeederDialogBuilder(
						mThis, position, GameActivity.class);
				if (builder != null) {
					AlertDialog ad = builder.create();
					ad.setOwnerActivity(mThis);
					ad.show();
				} else {
					Intent i = new Intent(mThis, GameActivity.class);
					i.putExtra("org.jtb.droidlife.seeder.position", position);
					mThis.startActivity(i);
				}
			}
		});
		mSeederList.setOnItemLongClickListener(new OnItemLongClickListener() {
			public boolean onItemLongClick(AdapterView<?> parent, View v,
					int position, long id) {
				AlertDialog.Builder builder = new SeederClickDialog.Builder(
						mThis, position);
				mSeederClickDialog = builder.create();
				mSeederClickDialog.setOwnerActivity(mThis);
				mSeederClickDialog.show();
				return true;
			}
		});

		mEmptyListText = (TextView) findViewById(R.id.empty_list_text);
	}

	@Override
	public void onResume() {
		super.onResume();
		update();
	}

	@Override
	public boolean onCreateOptionsMenu(Menu menu) {
		boolean result = super.onCreateOptionsMenu(menu);
		MenuItem mi;

		mi = menu.add(0, MENU_NEW, 0, R.string.menu_new).setIcon(
				android.R.drawable.ic_menu_add);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);
		mi = menu.add(0, MENU_PREFS, 0, R.string.menu_prefs).setIcon(
				android.R.drawable.ic_menu_preferences);
		//MenuItemCompat.setShowAsAction(mi,
			//	MenuItemCompat.SHOW_AS_ACTION_IF_ROOM);
		mi = menu.add(0, MENU_HELP, 0, R.string.menu_help).setIcon(
				android.R.drawable.ic_menu_help);
		//MenuItemCompat.setShowAsAction(mi, MenuItemCompat.SHOW_AS_ACTION_NEVER);
		mi = menu.add(0, MENU_INFO, 0, R.string.menu_info).setIcon(
				android.R.drawable.ic_menu_info_details);
		//MenuItemCompat.setShowAsAction(mi, MenuItemCompat.SHOW_AS_ACTION_NEVER);

		return result;
	}

	@Override
	public boolean onOptionsItemSelected(MenuItem item) {
		switch (item.getItemId()) {
		case MENU_NEW:
			showDialog(NEW_DIALOG);
			return true;
		case MENU_PREFS:
			Intent i = new Intent(this, PrefsActivity.class);
			startActivity(i);
			return true;
		case MENU_HELP:
			showDialog(HELP_DIALOG);
			return true;
		case MENU_INFO:
			showDialog(INFO_DIALOG);
			return true;
		}

		return super.onOptionsItemSelected(item);
	}

	protected void onActivityResult(int requestCode, int resultCode, Intent data) {
		switch (requestCode) {
		case DESIGN_REQUEST:
			update();
			break;
		}
	}

	protected Dialog onCreateDialog(int id) {
		AlertDialog.Builder builder;

		switch (id) {
		case NEW_DIALOG:
			builder = new NewDialog.Builder(this);
			mNewDialog = builder.create();
			return mNewDialog;
		case HELP_DIALOG:
			builder = new CustomDialog.Builder(this, R.layout.seeders_help);
			mHelpDialog = builder.create();
			return mHelpDialog;
		case INFO_DIALOG:
			builder = new CustomDialog.Builder(this, R.layout.info);
			mInfoDialog = builder.create();
			return mInfoDialog;
		}
		return null;
	}

	void update() {
		SeederManager.getInstance(this).refresh();

		if (SeederManager.getInstance(this).getSize() == 0) {
			mSeederList.setVisibility(View.GONE);
			mEmptyListText.setVisibility(View.VISIBLE);
		} else {
			mSeederList.setVisibility(View.VISIBLE);
			mEmptyListText.setVisibility(View.GONE);
			SeederAdapter sa = new SeederAdapter(this, SeederManager
					.getInstance(this).getSeeders());
			mSeederList.setAdapter(sa);
		}
	}
}
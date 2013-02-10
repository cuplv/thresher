package org.jtb.droidlife;

import java.util.ArrayList;
import java.util.List;

import android.app.AlertDialog;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;

public class SeederClickDialog extends AlertDialog {
	public static class Builder extends AlertDialog.Builder {
		private int mPosition;
		private SeedersActivity mActivity;

		public Builder(SeedersActivity activity, int position) {
			super(activity);

			this.mActivity = activity;
			this.mPosition = position;

			Seeder seeder = SeederManager.getInstance(mActivity).getSeeder(mPosition);
			String[] items;

			if (seeder.getSeedSource().isWritable()) {
				items = new String[4];
				items[0] = "Simulate";
				items[1] = "Edit";
				items[2] = "Remove";
				items[3] = "Send";
			} else {
				items = new String[1];
				items[0] = "Simulate";
			}

			setItems(items, new DialogInterface.OnClickListener() {
				public void onClick(DialogInterface dialog, int which) {
					Seeder seeder = SeederManager.getInstance(mActivity)
							.getSeeder(mPosition);
					AlertDialog ad = (AlertDialog) dialog;
					switch (which) {
					case 0:
						AlertDialog.Builder builder = seeder
								.getSeederDialogBuilder(mActivity, mPosition,
										GameActivity.class);
						if (builder != null) {
							ad = builder.create();
							ad.setOwnerActivity(mActivity);
							ad.show();
						} else {
							Intent i = new Intent(mActivity, GameActivity.class);
							i.putExtra("org.jtb.droidlife.seeder.position",
									mPosition);
							mActivity.startActivity(i);
						}
						break;
					case 1:
						builder = seeder.getSeederDialogBuilder(mActivity,
								mPosition, DesignActivity.class);
						if (builder != null) {
							ad = builder.create();
							ad.setOwnerActivity(mActivity);
							ad.show();
						} else {
							Intent i = new Intent(mActivity, DesignActivity.class);
							i.putExtra("org.jtb.droidlife.seeder.position",
									mPosition);
							mActivity.startActivity(i);
						}
						break;
					case 2:
						seeder.remove();
						mActivity.update();
						break;
					case 3:
						SeedSender ss = new SeedSender(mActivity);
						ss.send(seeder.getName(), (FileSeedSource)seeder.getSeedSource());
						break;
					}
				}
			});
			setNegativeButton(R.string.cancel,
					new DialogInterface.OnClickListener() {
						public void onClick(DialogInterface dialog, int which) {
							dialog.dismiss();
						}
					});
		}
	}

	public SeederClickDialog(Context context) {
		super(context);
	}
}

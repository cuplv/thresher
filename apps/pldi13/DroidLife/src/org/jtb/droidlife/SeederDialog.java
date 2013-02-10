package org.jtb.droidlife;

import android.app.AlertDialog;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.view.LayoutInflater;
import android.view.View;

public abstract class SeederDialog extends AlertDialog {
	public abstract static class Builder extends AlertDialog.Builder {
		protected View mLayout;
		protected Context mContext;
		protected int mPosition;
		protected Class mActivityClass;

		public Builder(Context context, int position, Class activityClass) {
			super(context);
			mPosition = position;
			mContext = context;
			mActivityClass = activityClass;

			Seeder seeder = SeederManager.getInstance(mContext).getSeeder(
					mPosition);

			LayoutInflater inflater = (LayoutInflater) context
					.getSystemService(Context.LAYOUT_INFLATER_SERVICE);
			mLayout = inflater.inflate(getLayout(), null);
			setView(mLayout);

			initViews();
			setViews();

			setTitle(seeder.toString());
			setIcon(android.R.drawable.ic_dialog_info);

			setPositiveButton(R.string.ok,
					new DialogInterface.OnClickListener() {
						public void onClick(DialogInterface dialog, int which) {
							if (setSeeder()) {
								Intent i = new Intent(mContext, mActivityClass);
								i.putExtra("org.jtb.droidlife.seeder.position",
										mPosition);
								mContext.startActivity(i);
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

		public abstract int getLayout();

		public abstract void initViews();

		public abstract void setViews();

		public abstract boolean setSeeder();
	}

	public SeederDialog(Context context) {
		super(context);
	}
}

package org.jtb.droidlife;

import android.app.AlertDialog;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.view.LayoutInflater;
import android.view.View;
import android.widget.EditText;
import android.widget.Toast;

public class NewDialog extends AlertDialog {

	public static class Builder extends AlertDialog.Builder {
		private SeedersActivity mActivity;
		private EditText mNameEdit;

		public Builder(SeedersActivity activity) {
			super(activity);

			mActivity = activity;

			LayoutInflater inflater = (LayoutInflater) activity
					.getSystemService(Context.LAYOUT_INFLATER_SERVICE);
			View layout = inflater.inflate(R.layout.new_dialog, null);
			setView(layout);
			setTitle("Name");
			setIcon(android.R.drawable.ic_dialog_info);

			mNameEdit = (EditText) layout.findViewById(R.id.name_edit);
			setPositiveButton(R.string.ok,
					new DialogInterface.OnClickListener() {
						public void onClick(DialogInterface dialog, int which) {
							String name = mNameEdit.getText().toString();
							int i = SeederManager.getInstance(mActivity)
									.getPosition(name);
							if (i != -1) {
								Toast.makeText(mActivity,
										"That name is already in use.",
										Toast.LENGTH_LONG).show();
								return;

							}
							Intent intent = new Intent(mActivity,
									DesignActivity.class);
							intent.putExtra("org.jtb.droidlife.seeder.name",
									name);
							mActivity.startActivity(intent);
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

	public NewDialog(Context context) {
		super(context);
	}
}

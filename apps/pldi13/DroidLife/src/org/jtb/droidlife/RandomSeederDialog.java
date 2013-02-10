package org.jtb.droidlife;

import android.content.Context;
import android.widget.EditText;
import android.widget.Toast;

public class RandomSeederDialog extends SeederDialog {
	public static class Builder extends SeederDialog.Builder {
		private EditText mLoadEdit;

		public Builder(Context context, int position, Class activityClass) {
			super(context, position, activityClass);
		}

		public int getLayout() {
			return R.layout.random_seeder_dialog;
		}

		public void initViews() {
			mLoadEdit = (EditText) mLayout.findViewById(R.id.load_edit);
		}

		public void setViews() {
			Seeder seeder = SeederManager.getInstance(mContext).getSeeder(
					mPosition);
			mLoadEdit.setText(Integer.toString(((RandomSeeder) seeder)
					.getLoad()));
		}

		public boolean setSeeder() {
			Seeder seeder = SeederManager.getInstance(mContext).getSeeder(
					mPosition);
			int load;
			try {
				load = Integer.parseInt(mLoadEdit.getText().toString());
				if (load <= 0) {
					Toast.makeText(mContext, "Enter a number greater than 0.",
							Toast.LENGTH_LONG).show();
					mLoadEdit.setText("5");					
					return false;
				}
				((RandomSeeder) seeder).setLoad(load);
				return true;
			} catch (NumberFormatException nfe) {
				Toast.makeText(mContext, "Enter a valid integer.",
						Toast.LENGTH_LONG).show();
				mLoadEdit.setText("5");
				return false;
			}
		}
	}

	public RandomSeederDialog(Context context) {
		super(context);
	}
}

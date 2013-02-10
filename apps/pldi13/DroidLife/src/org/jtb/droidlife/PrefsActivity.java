package org.jtb.droidlife;

import android.app.Activity;
import android.app.AlertDialog;
import android.content.Intent;
import android.os.Bundle;
import android.preference.CheckBoxPreference;
import android.preference.EditTextPreference;
import android.preference.ListPreference;
import android.preference.Preference;
import android.preference.PreferenceActivity;
import android.widget.Toast;

public class PrefsActivity extends PreferenceActivity {
	private PrefsActivity mThis;

	@Override
	public void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
		addPreferencesFromResource(R.layout.prefs);

		mThis = this;
		setResult(Activity.RESULT_OK);
	}

	@Override
	public void onPause() {
		super.onPause();
	}
}

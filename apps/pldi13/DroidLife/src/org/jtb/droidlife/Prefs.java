package org.jtb.droidlife;

import android.content.Context;
import android.content.SharedPreferences;
import android.content.SharedPreferences.Editor;
import android.preference.PreferenceManager;

public class Prefs {
	private Context context = null;

	public Prefs(Context context) {
		this.context = context;
	}

	private String getString(String key, String def) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		String s = prefs.getString(key, def);
		return s;
	}

	private int getInt(String key, int def) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		int i = Integer.parseInt(prefs.getString(key, Integer.toString(def)));
		return i;
	}

	private float getFloat(String key, float def) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		float f = Float.parseFloat(prefs.getString(key, Float.toString(def)));
		return f;
	}

	private long getLong(String key, long def) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		long l = Long.parseLong(prefs.getString(key, Long.toString(def)));
		return l;
	}

	private void setString(String key, String val) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		Editor e = prefs.edit();
		e.putString(key, val);
		e.commit();
	}

	private void setBoolean(String key, boolean val) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		Editor e = prefs.edit();
		e.putBoolean(key, val);
		e.commit();
	}

	private void setInt(String key, int val) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		Editor e = prefs.edit();
		e.putString(key, Integer.toString(val));
		e.commit();
	}

	private void setLong(String key, long val) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		Editor e = prefs.edit();
		e.putString(key, Long.toString(val));
		e.commit();
	}

	private boolean getBoolean(String key, boolean def) {
		SharedPreferences prefs = PreferenceManager
				.getDefaultSharedPreferences(context);
		boolean b = prefs.getBoolean(key, def);
		return b;
	}

	private int[] getIntArray(String key, String def) {
		String s = getString(key, def);
		int[] ia = new int[s.length()];
		for (int i = 0; i < s.length(); i++) {
			ia[i] = s.charAt(i) - '0';
		}
		return ia;
	}
	
	public int[] getBirthRule() {
		int[] ia = getIntArray("birthRule", "3");
		return ia;
	}

	public int[] getSurvivalRule() {
		int[] ia = getIntArray("survivalRule", "23");
		return ia;
	}
	
	public int getCellSize() {
		return getInt("cellSize", 5);
	}
	
	public boolean isKeepScreenOn() {
		return getBoolean("keepScreenOn", true);
	}

	public boolean isUpgradedTo(int version) {
		int upgradedTo = getInt("upgradedTo", 0);
		if (upgradedTo >= version) {
			return true;
		}
		return false;
	}

	public void setUpgradedTo(int version) {
		setInt("upgradedTo", version);
	}
	
	public boolean isWrap() {
		return getBoolean("wrap", false);
	}
	
	public boolean isColored() {
		return getBoolean("colored", true);
	}
}

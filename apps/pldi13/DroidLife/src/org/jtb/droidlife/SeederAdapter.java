package org.jtb.droidlife;

import java.util.ArrayList;

import android.app.Activity;
import android.graphics.Typeface;
import android.view.LayoutInflater;
import android.view.View;
import android.view.ViewGroup;
import android.widget.ArrayAdapter;
import android.widget.TextView;

public class SeederAdapter extends ArrayAdapter<Seeder> {
	private LayoutInflater inflater;
	private ArrayList<Seeder> mSeeders;

	SeederAdapter(Activity context, ArrayList<Seeder> seeders) {
		super(context, R.layout.seeder_row, seeders);
		this.inflater = context.getLayoutInflater();
		this.mSeeders = seeders;
	}

	public View getView(int position, View convertView, ViewGroup parent) {
		View view = convertView;
		if (view == null) {
			view = inflater.inflate(R.layout.seeder_row, null);			
		}
		
		Seeder seeder = mSeeders.get(position);

		TextView nameText = (TextView) view.findViewById(R.id.name_text);
		nameText.setText(seeder.toString());

		return view;
	}
}

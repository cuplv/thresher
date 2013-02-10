package org.jtb.droidlife;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import android.content.Context;

public class SeederManager {
	private static SeederManager seederManager;

	private Context context;
	private SeedSource[] seedSources;
	private ArrayList<Seeder> seeders;

	private SeederManager(Context context) {
		this.context = context;

		seedSources = new SeedSource[] { new GeneratedSeedSource(),
				new Life106SeedSource(),
				new RLESeedSource() };

		refresh();
	}

	public static SeederManager getInstance(Context context) {
		if (seederManager == null) {
			seederManager = new SeederManager(context);
		}
		return seederManager;
	}

	public void refresh() {
		HashSet<Seeder> seederSet = new HashSet<Seeder>();
		for (int i = 0; i < seedSources.length; i++) {
			ArrayList<Seeder> s = seedSources[i].getSeeders();
			seederSet.addAll(s);
		}
		seeders = new ArrayList<Seeder>(seederSet);
		Collections.sort(seeders);
	}

	public int getSize() {
		return seeders.size();
	}
	
	public ArrayList<Seeder> getSeeders() {
		return seeders;
	}
	
	public int getPosition(String name) {
		for (int i = 0; i < seeders.size(); i++) {
			Seeder s = seeders.get(i);
			if (s.getName().equals(name)) {
				return i;
			}
		}
		return -1;
	}
	
	public Seeder getSeeder(int pos) {
		return seeders.get(pos);
	}
}

package org.jtb.droidlife;

import java.util.ArrayList;

public class GeneratedSeedSource extends SeedSource {
	private ArrayList<Seeder> seeders;
	
	public GeneratedSeedSource() {
		seeders = new ArrayList<Seeder>();
		seeders.add(new RandomSeeder(this));
		
	}
	
	public ArrayList<Seeder> getSeeders() {
		return seeders;
	}
	
	public boolean isWritable() {
		return false;
	}

}

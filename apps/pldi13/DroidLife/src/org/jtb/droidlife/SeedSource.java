package org.jtb.droidlife;

import java.util.ArrayList;

import org.jtb.droidlife.model.World;

public abstract class SeedSource {
	public static final SeedSource DEFAULT_WRITABLE = new RLESeedSource();
	
	public abstract ArrayList<Seeder> getSeeders();
	
	public boolean isWritable() {
		return false;
	}
	public void writeSeed(String name, World world) {
		return;
	}
	public void removeSeed(Seeder seeder) {
		return;
	}
}

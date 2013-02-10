package org.jtb.droidlife;

public abstract class GeneratedSeeder extends Seeder {

	public GeneratedSeeder(SeedSource seedSource, String name) {
		super(seedSource, name);
	}	
	
	@Override
	public String toString() {
		return super.toString() + " (generated)";
	}
}

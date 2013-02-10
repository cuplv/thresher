package org.jtb.droidlife;

public class Life106SeedSource extends SDCardSeedSource {
	public Life106SeedSource() {
		super("life106");
	}

	@Override
	protected Seeder newSeeder(String name) {
		return new Life106Seeder(this, name);
	}

	public boolean isWritable() {
		return true;
	}	
	
	protected SeedWriter getSeedWriter() {
		return new Life106Writer();
	}

	@Override
	protected String getFileExtension() {
		return "lif";
	}
}

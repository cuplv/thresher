package org.jtb.droidlife;

public class RLESeedSource extends SDCardSeedSource {
	public RLESeedSource() {
		super("rle");
	}

	@Override
	protected Seeder newSeeder(String name) {
		return new RLESeeder(this, name);
	}
	
	public boolean isWritable() {
		return true;
	}

	@Override
	protected SeedWriter getSeedWriter() {
		return new RLEWriter();
	}

	@Override
	protected String getFileExtension() {
		return "rle";
	}
}

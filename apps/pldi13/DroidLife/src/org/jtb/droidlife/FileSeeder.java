package org.jtb.droidlife;

public abstract class FileSeeder extends Seeder {
	protected FileSeedSource fileSeedSource;
	
	public FileSeeder(FileSeedSource fileSeedSource, String name) {
		super(fileSeedSource, name);
		this.fileSeedSource = fileSeedSource;
	}
}

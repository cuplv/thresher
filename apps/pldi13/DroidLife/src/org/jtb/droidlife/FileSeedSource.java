package org.jtb.droidlife;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Random;

import android.content.res.AssetManager;
import android.util.Log;

public abstract class FileSeedSource extends SeedSource {
	protected String path;

	public FileSeedSource(String path) {
		this.path = path;
	}

	protected abstract String[] getNames();

	protected abstract Seeder newSeeder(String name);

	public ArrayList<Seeder> getSeeders() {
		String[] names = getNames();
		ArrayList<Seeder> seeders = new ArrayList<Seeder>();
		if (names != null) {
			for (int i = 0; i < names.length; i++) {
				Seeder seeder = newSeeder(names[i]);
				seeders.add(seeder);
			}
		}

		return seeders;
	}

	public abstract Reader getReader(String name);
	protected abstract String getFileExtension();	
	public abstract String getFileName(String name);
	public abstract String getFilePath(String name);
	public abstract String getFileContent(String name);
}

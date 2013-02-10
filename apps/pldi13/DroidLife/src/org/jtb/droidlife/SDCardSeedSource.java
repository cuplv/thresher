package org.jtb.droidlife;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

import org.jtb.droidlife.model.World;

import android.os.Environment;
import android.util.Log;

public abstract class SDCardSeedSource extends FileSeedSource {
	protected static final String SDCARD_PREFIX = Environment
			.getExternalStorageDirectory() + "/droidlife/";

	public SDCardSeedSource(String path) {
		super(SDCARD_PREFIX + "/" + path);
	}

	public String[] getNames() {
		String[] fileNames = new File(path).list();
		if (fileNames == null) {
			return new String[0];
		}
		String[] names = new String[fileNames.length];
		for (int i = 0; i < fileNames.length; i++) {
			int dotIndex = fileNames[i].lastIndexOf('.');
			if (dotIndex == -1) {
				names[i] = fileNames[i];
			} else {
				names[i] = fileNames[i].substring(0, dotIndex);
			}
		}
		return names;
	}

	@Override
	public Reader getReader(String name) {
		Reader reader = null;
		File f = null;
		try {
			f = new File(getFilePath(name));
			reader = new FileReader(f);
		} catch (FileNotFoundException e) {
			Log.e(getClass().getSimpleName(), "could not open file: " + f, e);
		}
		return reader;
	}

	@Override
	public void writeSeed(String name, World world) {
		if (!isWritable()) {
			throw new AssertionError("called for non-writable seed source");
		}
		Writer w = null;
		try {
			File f = new File(getFilePath(name));
			w = new FileWriter(f);
			SeedWriter wr = getSeedWriter();
			wr.write(world, name, w);
		} catch (IOException e) {
			Log.e(getClass().getSimpleName(), "error saving file", e);
		} finally {
			try {
				if (w != null) {
					w.close();
				}
			} catch (IOException e) {
				Log.e(getClass().getSimpleName(), "error closing file", e);
			}
		}
	}

	@Override
	public void removeSeed(Seeder seeder) {
		File f = new File(path + "/" + seeder.getName());
		f.delete();
	}

	public String getFileName(String name) {
		return name + "." + getFileExtension();
	}

	public String getFilePath(String name) {
		return path + "/" + getFileName(name);
	}

	protected abstract SeedWriter getSeedWriter();

	public String getFileContent(String name) {
		Reader reader = getReader(name);
		BufferedReader br = new BufferedReader(reader);
		String line;
		StringBuilder sb = new StringBuilder();

		try {
			while ((line = br.readLine()) != null) {
				sb.append(line);
				sb.append("\n");
			}
			return sb.toString();
		} catch (IOException e) {
			Log.e(getClass().getSimpleName(), "could not read file contents", e);
			return null;
		} finally {
			if (reader != null) {
				try {
					reader.close();
				} catch (IOException e) {
				}
			}
		}

	}
}

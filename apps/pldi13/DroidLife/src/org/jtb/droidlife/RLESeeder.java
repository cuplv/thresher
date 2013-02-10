package org.jtb.droidlife;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.jtb.droidlife.model.World;

import android.graphics.Color;
import android.util.Log;

public class RLESeeder extends FileSeeder {
	private static final Pattern HEADER_PATTERN = Pattern
			.compile("x\\s*=\\s*(\\d+)\\s*,\\s*y\\s*=\\s*(\\d+)(?:\\s*,\\s*rule\\s*=\\s*(.*))?");

	public RLESeeder(FileSeedSource fileSeedSource, String name) {
		super(fileSeedSource, name);
	}

	@Override
	public void seed(World world, boolean colored) {
		read(world, colored);
	}

	private void read(World world, boolean colored) {
		Reader reader = null;
		int xmax = world.current.length - 1;
		int ymax = world.current[0].length - 1;
		int xmid = xmax / 2;
		int ymid = ymax / 2;

		try {
			reader = fileSeedSource.getReader(name);
			BufferedReader br = new BufferedReader(reader);

			String line;
			boolean headerRead = false;
			int sizeX = 0, sizeY = 0;
			int xStart = 0, yStart = 0;
			int x = 0, y = 0;
			
			while ((line = br.readLine()) != null) {
				if (line.startsWith("#") || line.length() == 0) {
					continue;
				}
				if (!headerRead) {
					Matcher m = HEADER_PATTERN.matcher(line);
					if (m.matches()) {
						sizeX = Integer.parseInt(m.group(1));
						xStart = xmid - sizeX / 2;
						x = xStart;
						sizeY = Integer.parseInt(m.group(2));
						yStart = ymid - sizeY / 2;
						y = yStart;
						String ruleString = m.group(3);
						world.setRule(ruleString);
						headerRead = true;
						continue;
					}
				}

				RLEStringRunIterator i = new RLEStringRunIterator(line);

				while (i.hasNext()) {
					RLERun run = i.next();
					if (run.type == RLERun.Type.EOL) {
						y += run.length;
						x = xStart;
					} else {
						populateRun(world, x, y, run, colored);
						x += run.length;
					}
				}
			}
		} catch (IOException e) {
			Log.e(getClass().getSimpleName(), "could not read", e);
		} finally {
			if (reader != null) {
				try {
					reader.close();
				} catch (IOException e) {
				}
			}
		}
	}

	private void populateRun(World world, int x, int y, RLERun run,
			boolean colored) {
		if (run.type == RLERun.Type.DEAD) {
			// assume empty world
			return;
		}

		for (int i = x; i < x + run.length; i++) {
			if (i < 1 || i > world.current.length - 2 || y < 1
					|| y > world.current[0].length - 2) {
				continue;
			}
			if (colored) {
				world.current[i][y].spawn();
			} else {
				world.current[i][y].spawn(Color.WHITE);
			}
		}
	}
}

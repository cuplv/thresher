package org.jtb.droidlife;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.ArrayList;

import org.jtb.droidlife.model.World;

import android.graphics.Color;
import android.util.Log;

public class Life106Seeder extends FileSeeder {
	private static class Point {
		int x, y;
	}

	private ArrayList<Point> points;

	public Life106Seeder(FileSeedSource fileSeedSource, String name) {
		super(fileSeedSource, name);
	}

	@Override
	public void seed(World world, boolean colored) {
		read();
		populate(world, colored);
	}

	private void read() {
		Reader reader = null;

		try {
			reader = fileSeedSource.getReader(name);
			BufferedReader br = new BufferedReader(reader);

			points = new ArrayList<Point>();
			String line;

			while ((line = br.readLine()) != null) {
				if (line.startsWith("#")) {
					continue;
				}
				String[] sps = line.split("\\s");
				if (sps.length != 2) {
					Log.w(getClass().getSimpleName(), "invalid line: " + line);
					continue;
				}
				try {
					Point p = new Point();
					p.x = Integer.parseInt(sps[0]);
					p.y = Integer.parseInt(sps[1]);
					points.add(p);
				} catch (NumberFormatException nfe) {
					Log.w(getClass().getSimpleName(), nfe);
					continue;
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

	private void populate(World world, boolean colored) {
		int xmax = world.current.length - 1;
		int ymax = world.current[0].length - 1;
		int xmid = xmax / 2;
		int ymid = ymax / 2;

		for (int i = 0; i < points.size(); i++) {
			int x = xmid + points.get(i).x;
			int y = ymid + points.get(i).y;

			if (x < 0 || x > xmax || y < 0 || y > ymax) {
				continue;
			}

			if (colored) {
				world.current[x][y].spawn();
			} else {
				world.current[x][y].spawn(Color.WHITE);
			}
		}
	}
}

package org.jtb.droidlife;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Date;

import org.jtb.droidlife.model.World;

public class RLEWriter extends SeedWriter {
	@Override
	public void write(World world, String name, Writer os) throws IOException {
		BufferedWriter bw = new BufferedWriter(os);

		// write meta

		bw.write("#N " + name + "\n");
		bw.write("#C " + DATE_FORMAT.format(new Date()) + "\n");
		bw.write("#C created by / generated with DroidLife\n");
		bw.write("#C jeffrey.blattman@gmail.com\n");

		// get bounding box to keep file as small
		// and simple as possible

		int startX = getStartX(world);
		if (startX == -1) {
			// no live cells, write empty file
			bw.write("x = 0, y = 0, rule = " + world.getRule() + "\n");
			return;
		}
		int startY = getStartY(world);
		int endX = getEndX(world);
		int endY = getEndY(world);

		int xSize = endX - startX + 1;
		int ySize = endY - startY + 1;

		// write header

		bw.write("x = " + xSize + ", y = " + ySize + ", rule = "
				+ world.getRule() + "\n");

		RLEWorldRunIterator i = new RLEWorldRunIterator(world, startX, startY,
				endX, endY);
		StringBuilder buffer = new StringBuilder();

		// write runs

		RLERun run;
		while ((run = i.next()) != null) {
			String r = run.toString();
			if (run.type == RLERun.Type.EOL && !i.hasNext()) {
				// EOF case, don't write newline, we will
				// wrote EOF marker below
				continue;
			}
			if (buffer.length() + r.length() > 70) {
				// keep lines < 70 chars
				bw.write(buffer.toString());
				bw.write('\n');
				buffer = new StringBuilder();
			}
			buffer.append(r);
		}

		bw.write(buffer.toString());
		// EOF marker
		bw.write("!\n");
		bw.flush();
	}

	private int getStartX(World world) {
		for (int i = 0; i < world.current.length; i++) {
			for (int j = 0; j < world.current[i].length; j++) {
				if (world.current[i][j].isLiving()) {
					return i;
				}
			}
		}
		return -1;
	}

	private int getStartY(World world) {
		for (int j = 0; j < world.current[0].length; j++) {
			for (int i = 0; i < world.current.length; i++) {
				if (world.current[i][j].isLiving()) {
					return j;
				}
			}
		}
		return -1;
	}

	private int getEndX(World world) {
		for (int i = world.current.length - 1; i >= 0; i--) {
			for (int j = 0; j < world.current[i].length; j++) {
				if (world.current[i][j].isLiving()) {
					return i;
				}
			}
		}
		return -1;
	}

	private int getEndY(World world) {
		for (int j = world.current[0].length - 1; j >= 0; j--) {
			for (int i = 0; i < world.current.length; i++) {
				if (world.current[i][j].isLiving()) {
					return j;
				}
			}
		}
		return -1;
	}
}

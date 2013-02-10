package org.jtb.droidlife;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Date;

import org.jtb.droidlife.model.World;

public class Life106Writer extends SeedWriter {
	@Override
	public void write(World world, String name, Writer os) throws IOException {
		int xmid = (world.current.length-2) / 2;
		int ymid = (world.current[0].length-2) / 2;
		
		BufferedWriter bw = new BufferedWriter(os);
		bw.write("#Life 1.06\n");
		bw.write("#" + name + "\n");
		bw.write("#" + DATE_FORMAT.format(new Date()) + "\n");
		bw.write("#created by / generated with DroidLife\n");
		bw.write("#jeffrey.blattman@gmail.com\n");

		for (int i = 1; i < world.current.length-1; i++) {
			int x = i - xmid;
			for (int j = 1; j < world.current[i].length-1; j++) {
				int y = j - ymid;
				if (world.current[i][j].isLiving()) {
					String s = x + " " + y + "\n";
					bw.write(s);
				}
			}
		}
		bw.flush();
		bw.close();
	}
	
}

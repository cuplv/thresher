package org.jtb.droidlife;

import org.jtb.droidlife.model.World;

public class RLEWorldRunIterator {
	private World world;
	private int startX, endX, endY;
	private int xPos, yPos;

	public RLEWorldRunIterator(World world, int startX, int startY, int endX,
			int endY) {
		this.world = world;
		this.startX = startX;
		this.endX = endX;
		this.endY = endY;

		xPos = startX;
		yPos = startY;
	}

	public RLERun next() {
		if (!hasNext()) {
			return null;
		}

		RLERun run = new RLERun();
		
		if (xPos > endX) {
			// new line 
			xPos = startX;
			run.type = RLERun.Type.EOL;
			// new line run length
			int ce = countEmptyLines(yPos + 1);
			run.length = 1 + ce;
			yPos += run.length;
			
			return run;
		}
		
		//
		// not a new line, run of live or dead then
		//
		
		if (world.current[xPos][yPos].isLiving()) {
			run.type = RLERun.Type.ALIVE;
		} else {
			run.type = RLERun.Type.DEAD;
		}
		
		while (xPos <= endX
				&& world.current[xPos][yPos].isLiving() == run.isLiving()) {
			run.length++;
			xPos++;
			if (xPos > endX && run.type == RLERun.Type.DEAD) {
				// if rest of line is dead, skip to new line
				// case
				return next();
			}
		}

		return run;
	}

	private int countEmptyLines(int lookY) {
		int count = 0;
		for (int j = lookY; j <= endY; j++) {
			for (int i = startX; i <= endX; i++) {
				if (world.current[i][j].isLiving()) {
					return count;
				}
			}
			count++;
		}
		return count;
	}

	public boolean hasNext() {
		return yPos <= endY;
	}
}

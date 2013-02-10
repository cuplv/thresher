package org.jtb.droidlife.model;

import java.util.Random;

import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;

public class Cell {
	private static Random RANDOM = new Random(System.currentTimeMillis());
	private static float COLOR_FACTOR = 1.5f;
	private static Paint CIRCLE_PAINT;

	static {
		CIRCLE_PAINT = new Paint();
		CIRCLE_PAINT.setAntiAlias(true);
	}

	private Cell[] neighbors = new Cell[8];
	private int x, y, size, cX, cY, radius;
	private World world;
	private int color = Color.WHITE;
	private boolean wrap;
	private Cell nullCell;

	int age = -1;

	private Cell() {
	}
	
	public Cell(World world, int x, int y, int size, boolean wrap) {
		this.world = world;
		this.x = x;
		this.y = y;
		this.size = size;
		this.wrap = wrap;
		this.cX = x * size;
		this.cY = y * size;
		this.radius = size / 2;
		this.neighbors = new Cell[8];
		this.nullCell = new Cell();
	}

	public void init(Cell c) {
		this.world = c.world;
		this.x = c.x;
		this.y = c.y;
		this.size = c.size;
		this.age = c.age;
		this.color = c.color;
		this.neighbors = c.neighbors;
		this.wrap = c.wrap;
		this.cX = c.cX;
		this.cY = c.cY;
		this.radius = c.radius;
		this.nullCell = c.nullCell;
	}

	public int getAge() {
		return age;
	}

	public void spawn() {
		age = 0;

		int r = RANDOM.nextInt(0xFF);
		int g = RANDOM.nextInt(0xFF);
		int b = RANDOM.nextInt(0xFF);

		color = Color.rgb(r, g, b);
	}

	public void spawn(int color) {
		age = 0;
		this.color = color;
	}

	public void die() {
		age = -1;
	}

	private int getColor() {
		return color;
	}

	public void draw(Canvas canvas) {
		if (age == -1) {
			return;
		}
		CIRCLE_PAINT.setColor(color);
		canvas.drawCircle(cX, cY, radius, CIRCLE_PAINT);
	}

	public void generate() {
		if (age != -1) {
			age++;
		}

		int count = living();

		if (age != -1) {
			boolean survive = false;
			for (int k = 0; k < world.surviveNeighbors.length; k++) {
				if (count == world.surviveNeighbors[k]) {
					survive = true;
					break;
				}
			}
			if (!survive) {
				die();
			}
		} else {
			int bc;
			for (int k = 0; k < world.birthNeighbors.length; k++) {
				if (count == world.birthNeighbors[k]) {
					bc = birthColor(count);
					spawn(bc);
					break;
				}
			}
		}

	}

	public void getNeighbors() {
		int xm1 = (x == 0) ? world.previous.length - 1 : x - 1;
		int xp1 = (x == world.previous.length - 1) ? 0 : x + 1;
		int ym1 = (y == 0) ? world.previous[0].length - 1 : y - 1;
		int yp1 = (y == world.previous[0].length - 1) ? 0 : y + 1;

		neighbors[0] = world.previous[xm1][ym1];
		neighbors[1] = world.previous[xm1][y];
		neighbors[2] = world.previous[xm1][yp1];

		neighbors[3] = world.previous[x][ym1];
		neighbors[4] = world.previous[x][yp1];

		neighbors[5] = world.previous[xp1][ym1];
		neighbors[6] = world.previous[xp1][y];
		neighbors[7] = world.previous[xp1][yp1];

		if (!wrap) {
			if (x == 0) {
				neighbors[0] = nullCell;
				neighbors[1] = nullCell;
				neighbors[2] = nullCell;
			} else if (x == world.previous.length - 1) {
				neighbors[5] = nullCell;
				neighbors[6] = nullCell;
				neighbors[7] = nullCell;				
			}
			
			if (y == 0) {
				neighbors[0] = nullCell;
				neighbors[3] = nullCell;
				neighbors[5] = nullCell;				
			} else if (y == world.previous[0].length - 1) {
				neighbors[2] = nullCell;
				neighbors[4] = nullCell;
				neighbors[7] = nullCell;								
			}
		}
	}

	public boolean isLiving() {
		return age != -1;
	}
	
	private int living() {
		int count = 0;

		for (int i = 0, l = neighbors.length; i < l; i++) {
			if (neighbors[i].age != -1) {
				count++;
			}
		}

		return count;
	}

	private int birthColor(int count) {
		int rSum = 0, gSum = 0, bSum = 0;

		int c, r, g, b;

		for (int i = 0; i < neighbors.length; i++) {
			if (neighbors[i].age == -1) {
				continue;
			}
			c = neighbors[i].getColor();
			r = Color.red(c);
			g = Color.green(c);
			b = Color.blue(c);

			rSum += r / count;
			gSum += g / count;
			bSum += b / count;
		}

		int fr = rSum;
		int fg = gSum;
		int fb = bSum;

		if (rSum > gSum) {
			fr *= COLOR_FACTOR;
			fg /= COLOR_FACTOR;
		}
		if (rSum > bSum) {
			fr *= COLOR_FACTOR;
			fb /= COLOR_FACTOR;
		}
		if (gSum > rSum) {
			fg *= COLOR_FACTOR;
			fr /= COLOR_FACTOR;
		}
		if (gSum > bSum) {
			fg *= COLOR_FACTOR;
			fb /= COLOR_FACTOR;
		}
		if (bSum > rSum) {
			fb *= COLOR_FACTOR;
			fr /= COLOR_FACTOR;
		}
		if (bSum > gSum) {
			fb *= COLOR_FACTOR;
			fg /= COLOR_FACTOR;
		}

		fr = Math.min(0xff, fr);
		fg = Math.min(0xff, fg);
		fb = Math.min(0xff, fb);

		return Color.rgb(fr, fg, fb);
	}
}

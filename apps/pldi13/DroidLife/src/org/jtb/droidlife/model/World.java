package org.jtb.droidlife.model;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import android.graphics.Canvas;
import android.util.Log;

public class World {
	private static final Pattern RULE1_PATTERN = Pattern
			.compile("[bB](\\d+)/[sS](\\d+)");
	private static final Pattern RULE2_PATTERN = Pattern
			.compile("(\\d+)/(\\d+)");

	public Cell[][] current;

	Cell[][] previous;
	int[] birthNeighbors;
	int[] surviveNeighbors;

	private int generation = 0;
	private int population = 0;
	private int cellSize;
	private boolean wrap;

	public void clear() {
		for (int i = 0; i < current.length; i++) {
			for (int j = 0; j < current[i].length; j++) {
				current[i][j].die();
			}
		}
	}

	private void init() {
		for (int i = 0; i < current.length; i++) {
			for (int j = 0; j < current[i].length; j++) {
				current[i][j] = new Cell(this, i, j, cellSize, wrap);
				previous[i][j] = new Cell(this, i, j, cellSize, wrap);
			}
		}
		for (int i = 0; i < current.length; i++) {
			for (int j = 0; j < current[i].length; j++) {
				current[i][j].getNeighbors();
				previous[i][j].getNeighbors();
			}
		}
	}

	public int getGeneration() {
		return generation;
	}

	public int getPopulation() {
		return population;
	}

	public World(int xMax, int yMax, int cellSize, int[] birthNeighbors,
			int[] surviveNeighbors, boolean wrap) {
		this.cellSize = cellSize;

		current = new Cell[xMax][yMax];
		previous = new Cell[xMax][yMax];

		this.birthNeighbors = birthNeighbors;
		this.surviveNeighbors = surviveNeighbors;
		this.wrap = wrap;

		init();
	}

	public void draw(Canvas canvas) {
		for (int i = 0, li = current.length; i < li; i++) {
			for (int j = 0, lj = current[i].length; j < lj; j++) {
				current[i][j].draw(canvas);
			}
		}
	}

	public void generate() {
		copy(current, previous);

		population = 0;

		for (int i = 0, li = current.length; i < li; i++) {
			Cell cell;
			for (int j = 0, lj = current[i].length; j < lj; j++) {
				cell = current[i][j];
				cell.generate();
				if (cell.age != -1) {
					population++;
				}
			}
		}

		generation++;
	}

	private void copy(Cell[][] src, Cell[][] dest) {
		for (int i = 0, li = src.length; i < li; i++) {
			for (int j = 0, lj = src[0].length; j < lj; j++) {
				dest[i][j].init(src[i][j]);
			}
		}
	}

	public String getRule() {
		StringBuilder sb = new StringBuilder();
		sb.append('b');
		for (int i = 0; i < birthNeighbors.length; i++) {
			sb.append(birthNeighbors[i]);
		}
		sb.append('s');
		for (int i = 0; i < surviveNeighbors.length; i++) {
			sb.append(surviveNeighbors[i]);
		}

		return sb.toString();
	}

	public void setRule(String rule) {
		if (rule == null || rule.length() == 0) {
			return;
		}

		Matcher m1 = RULE1_PATTERN.matcher(rule);
		Matcher m2 = RULE2_PATTERN.matcher(rule);

		if (m1.matches()) {
			birthNeighbors = toIntArray(m1.group(1));
			surviveNeighbors = toIntArray(m1.group(2));
		} else if (m2.matches()) {
			surviveNeighbors = toIntArray(m2.group(1));
			birthNeighbors = toIntArray(m2.group(2));
		} else {
			Log.e(getClass().getSimpleName(), "could not parse rule: " + rule);
		}
	}

	private int[] toIntArray(String s) {
		int[] ia = new int[s.length()];
		for (int i = 0; i < s.length(); i++) {
			ia[i] = s.charAt(i) - '0';
		}
		return ia;
	}
}

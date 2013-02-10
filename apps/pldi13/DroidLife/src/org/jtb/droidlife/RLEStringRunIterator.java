package org.jtb.droidlife;

public class RLEStringRunIterator {
	private String line = null;
	private int position = 0;

	public RLEStringRunIterator(String line) {
		this.line = line;
	}

	public RLERun next() {
		if (!hasNext()) {
			return null;
		}

		RLERun run = new RLERun();
		String n = "";
		while (line.charAt(position) >= '0' && line.charAt(position) <= '9') {
			n += line.charAt(position++);
		}
		if (n.length() > 0) {
			run.length = Integer.parseInt(n);
		} else {
			run.length = 1;
		}
		if (line.charAt(position) == 'b') {
			run.type = RLERun.Type.DEAD;
		} else if (line.charAt(position) == '$') {
			run.type = RLERun.Type.EOL;
		} else {
			run.type = RLERun.Type.ALIVE;
		}
		position++;

		return run;
	}

	public boolean hasNext() {
		return position < line.length() && line.charAt(position) != '!';
	}
}

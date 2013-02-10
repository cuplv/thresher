package org.jtb.droidlife;

public class RLERun {
	public enum Type {
		DEAD, ALIVE, EOL
	}

	public int length = 0;
	public Type type = null;

	@Override
	public String toString() {
		switch (type) {
		case ALIVE:
			return ((length == 1) ? "" : Integer.toString(length)) + 'o';
		case DEAD:
			return ((length == 1) ? "" : Integer.toString(length)) + 'b';
		case EOL:
			return ((length == 1) ? "" : Integer.toString(length)) + '$';
		default:
			throw new AssertionError("unknown type: " + type);
		}
	}
	
	public boolean isLiving() {
		if (type == Type.ALIVE) {
			return true;
		}
		
		return false;
	}
}

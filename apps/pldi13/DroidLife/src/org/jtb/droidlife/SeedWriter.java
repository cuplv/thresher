package org.jtb.droidlife;

import java.io.IOException;
import java.io.Writer;
import java.text.DateFormat;
import java.text.SimpleDateFormat;

import org.jtb.droidlife.model.World;

public abstract class SeedWriter {
	protected static final DateFormat DATE_FORMAT = new SimpleDateFormat("d MMMM yyyy HH:mm:ss Z");

	public abstract void write(World world, String name, Writer os) throws IOException;
}

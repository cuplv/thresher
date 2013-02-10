package org.jtb.droidlife;

import java.sql.Date;
import java.text.SimpleDateFormat;

public class SeedNameQualifier {
	private static final String DATE_PATTERN = "yyyy-MM-dd-HH-mm-ss";
	private static final SimpleDateFormat DATE_FORMAT = new SimpleDateFormat(DATE_PATTERN);
	
	private String qName;
	
	public SeedNameQualifier(String name) {
		qName = name + " " + DATE_FORMAT.format(new Date(System.currentTimeMillis()));
	}
	
	@Override
	public String toString() {
		return qName;
	}
}

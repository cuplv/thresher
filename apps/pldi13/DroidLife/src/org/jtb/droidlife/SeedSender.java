package org.jtb.droidlife;

import android.content.Context;
import android.content.Intent;

public class SeedSender {
	private Context context;
	
	public SeedSender(Context context) {
		this.context = context;
	}
	
	public void send(String name, FileSeedSource fss) {
		Intent emailIntent = new Intent(android.content.Intent.ACTION_SEND);
		emailIntent.setType("plain/text");
		//emailIntent.putExtra(android.content.Intent.EXTRA_EMAIL, "");
		emailIntent.putExtra(android.content.Intent.EXTRA_SUBJECT, fss.getFileName(name));
		emailIntent.putExtra(android.content.Intent.EXTRA_TEXT, fss.getFileContent(name));
		context.startActivity(Intent.createChooser(emailIntent, "Send seed ..."));
	}
}

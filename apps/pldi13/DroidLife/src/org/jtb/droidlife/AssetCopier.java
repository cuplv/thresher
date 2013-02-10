package org.jtb.droidlife;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import android.content.Context;
import android.content.pm.PackageInfo;
import android.content.pm.PackageManager;
import android.content.pm.PackageManager.NameNotFoundException;
import android.os.Environment;
import android.util.Log;

public class AssetCopier {
	private Context mContext;

	public AssetCopier(Context context) {
		mContext = context;
	}

	public void copy() {
		String[] assetDirs = new String[] { "life106", "rle" };
		String[] sdCardDirs = new String[] {
				Environment.getExternalStorageDirectory()
						+ "/droidlife/life106",
				Environment.getExternalStorageDirectory() + "/droidlife/rle" };

		for (int i = 0; i < assetDirs.length; i++) {
			String[] fileNames;
			try {
				fileNames = mContext.getAssets().list(assetDirs[i]);
			} catch (IOException e) {
				Log.e(getClass().getSimpleName(), "error copying assets", e);
				continue;
			}
			for (int j = 0; j < fileNames.length; j++) {
				File destDir = new File(sdCardDirs[i]);
				destDir.mkdirs();
				copy(assetDirs[i], sdCardDirs[i], fileNames[j]);
			}
		}
	}

	private void copy(String assetDir, String sdCardDir, String fileName) {
		File destFile = new File(sdCardDir + File.separator + fileName);

		if (destFile.exists()) {
			return;
		}

		InputStream is = null;
		OutputStream os = null;

		try {
			is = mContext.getAssets()
					.open(assetDir + File.separator + fileName);
			os = new FileOutputStream(destFile);

			int b;
			while ((b = is.read()) != -1) {
				os.write(b);
			}
		} catch (IOException e) {
			Log.e(getClass().getSimpleName(), "error copying assets", e);
			return;
		} finally {
			try {
				if (is != null) {
					is.close();
				}
				if (os != null) {
					os.close();
				}
			} catch (IOException e) {
				Log.e(getClass().getSimpleName(), "error closing stream", e);
			}
		}
	}
}

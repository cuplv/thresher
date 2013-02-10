package org.jtb.droidlife;

import org.jtb.droidlife.model.World;

import android.content.Context;
import android.graphics.Color;

public class RandomSeeder extends GeneratedSeeder {
	private int load = 5;

	public int getLoad() {
		return load;
	}

	public void setLoad(int load) {
		this.load = load;
	}

	public RandomSeeder(SeedSource seedSource) {
		super(seedSource, "Random");
	}

	public void seed(World world, boolean colored) {
		for (int i = 1; i < world.current.length - 1; i++) {
			for (int j = 1; j < world.current[0].length - 1; j++) {
				if (RANDOM.nextInt(load) == 0) {
					if (colored) {
						world.current[i][j].spawn();
					} else {
						world.current[i][j].spawn(Color.WHITE);
					}
				}
			}
		}
	}

	@Override
	public SeederDialog.Builder getSeederDialogBuilder(Context context,
			int position, Class activityClass) {
		RandomSeederDialog.Builder builder = new RandomSeederDialog.Builder(
				context, position, activityClass);
		return builder;
	}
}

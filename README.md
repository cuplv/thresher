Installation
============
(1a) You can download and build all dependencies with installation scripts (only tested on Linuex). Do 'make install-deps && make deps' and go to step (4) if this works. Otherwise, go to step (1b).

(1b) Download WALA (git clone https://github.com/wala/WALA.git), move it to /lib and follow setup/build instructions. 

(2) Download Z3 (git clone https://git01.codeplex.com/z3), move it to /lib and follow setup/build instructions.

(3) Download ScalaZ3 (git clone https://github.com/psuter/ScalaZ3.git) and move it to /lib. 

(4) Integrate Z3 with ScalaZ3. Once you have built Z3, create lib/ScalaZ3/z3/[z3version]/include and lib/ScalaZ3/z3/[z3version]/lib. From lib/ScalaZ3/z3/[z3version], do:

    cp <z3_dir>/build/libz3.so lib/
    cp <z3_dir>/src/api/*.h include/

If you are using a version of Scala other than 2.9.2 or a version of Z3 other than 4.3, you will need to update the SCALA_VERSION and Z3_VERSION variables in the top-level Makefile and thresher.sh.

(5) Build ScalaZ3. You'll need to download sbt version 0.10 or less. From lib/ScalaZ3, do 'sbt update; sbt package' in the lib/ScalaZ3 directory.

(6) Once all dependencies have been installed successfully, return to the top-level Thresher directory and type "make" to build the project.

Running Thresher on an Android app
-----------------------------------

Run ./thresher.sh -app <path_to_bin_dir_for_your_app>. It will compute a points-to graph for your app, find all heap paths from static fields to object instances of subtype Activity, and attempt to use symbolic execution to refute some of these paths. It will print all heap paths that might correspond to memory leaks between <Err Path> tags (better visualization coming soon!).

Using a different version of Android
------------------------------------
By default, Thresher analyzes apps using the Android 2.3 (Gingerbread) source code. To use a different Android version, you can use the -useAndroidJar <path_to_jar> flag. The Soot project has JAR files for most Android versions at https://github.com/Sable/android-platforms.


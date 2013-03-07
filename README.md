Installation
============
(1) You can download all dependencies by running:

     make install-deps

Go to step (4) if this works. Otherwise, go to step (2).

(2) Download WALA (git clone https://github.com/wala/WALA.git) and move it to /lib.

(3) Download Z3 (git clone https://git01.codeplex.com/z3) and move it to /lib. If cloning the repository does not work, go to z3.codeplex.com and follow the instructions for downloading manually (place it in /lib/z3).

(3) Download ScalaZ3 (git clone https://github.com/psuter/ScalaZ3.git) and move it to /lib.

(4) Installation scripts *should* build everything, but have only been tested on Linux. You will need Scala and sbt to be installed on your system. Run:

    make deps

If you are using a version of Scala other than 2.9.2 or a version of Z3 other than 4.3, you will need to update the SCALA_VERSION and Z3_VERSION variables in the top-level Makefile, ScalaZ3 Makefile, and thresher.sh.

(5) Once all dependencies have been installed successfully, return to the top-level Thresher directory and run
  
    make
    make tests

to build Thresher and its regression tests. 

Running Thresher on an Android app
-----------------------------------

Run: 
    
    ./thresher.sh -app <path_to_bin_dir_for_your_app>. 

It will compute a points-to graph for your app, find all heap paths from static fields to object instances of subtype Activity, and attempt to use symbolic execution to refute some of these paths. It will print all heap paths that might correspond to memory leaks between \<Err Path\> tags (better visualization coming soon!).

Using a different version of Android
------------------------------------
By default, Thresher analyzes apps using the Android 2.3 (Gingerbread) source code (included in /android/android-2.3.jar). To use a different Android version, you can use the -android_jar \<path_to_jar\> flag. The Soot project has JAR files for most Android versions at https://github.com/Sable/android-platforms.

WALA exclusions
---------------
By default, Thresher ignores any code prefixed with org.apache.*, java.nio.charset.*, or java.util.concurrent.*. You can change this behavior by editing the config/exclusions.txt file (full information on the file format at wala.sf.net).



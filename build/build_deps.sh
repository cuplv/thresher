#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)
Z3_VERSION=4.3

# build WALA
cp build/Makefile_wala lib/WALA/Makefile
# build process sometimes fails to copy natives.xml file
cd lib/WALA/ && make && cp com.ibm.wala.core/dat/natives.xml com.ibm.wala.core/bin/natives.xml

# build z3 
cd $BASE/lib/z3 && python scripts/mk_make.py && cd build && make

# build ScalaZ3
cd $BASE
cp build/Makefile_scalaz3 $BASE/lib/ScalaZ3/Makefile
# move z3 components where ScalaZ3 wants them
cd $BASE/lib/ScalaZ3/z3/x64/ && mkdir $Z3_VERSION && cd $Z3_VERSION
mkdir lib
mkdir include
cp $BASE/lib/z3/build/libz3.so lib/
cp $BASE/lib/z3/src/api/*.h include/
# build ScalaZ3 (requires sbt version .10 or less)
cd $BASE/lib/ScalaZ3 && make
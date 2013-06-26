#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)
Z3_VERSION=4.3

# build WALA
cp build/Makefile_wala lib/WALA/Makefile
# build process sometimes fails to copy natives.xml file
cd lib/WALA/ && make && cp com.ibm.wala.core/dat/natives.xml com.ibm.wala.core/bin/natives.xml

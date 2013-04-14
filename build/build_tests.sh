#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)

cd $BASE/apps/tests/
for testDir in $( ls -d */);
do
    cd $BASE/apps/tests/$testDir
    echo 'Building' $testDir 'tests'
    for dir in $( ls -d */);
    do
	echo 'Building' $dir
	cd $dir 
	mkdir -p bin
	make
	cd $BASE/apps/tests/$testDir
    done
done


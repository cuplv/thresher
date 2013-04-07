#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)

cd $BASE/apps/tests/regression
for dir in $( ls -d */);
do
    echo 'Building' $dir
    cd $dir 
    if [ ! -d "bin" ]; then
	mkdir bin
    fi
    make
    cd $BASE/apps/tests/regression
done

cd $BASE/apps/tests/immutability
for dir in $( ls -d */);
do
    echo 'Building' $dir
    cd $dir 
    if [ ! -d "bin" ]; then
	mkdir bin
    fi
    make
    cd $BASE/apps/tests/immutability
done

cd $BASE/apps/tests/synthesis
for dir in $( ls -d */);
do
    echo 'Building' $dir
    cd $dir 
    if [ ! -d "bin" ]; then
	mkdir bin
    fi
    make
    cd $BASE/apps/tests/synthesis
done

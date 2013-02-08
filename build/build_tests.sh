#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)

cd $BASE/apps/tests/regression
for dir in $( ls -d */);
do
    echo 'Building' $dir
    cd $dir && make
    cd $BASE/apps/tests/regression
done

#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)
Z3_VERSION=4.3

cd $BASE/lib/WALA && git pull
cd $BASE/lib/z3 && git pull
cd $BASE/lib/ScalaZ3 && git pull

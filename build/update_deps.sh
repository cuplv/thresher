#!/bin/bash

# should be run only from Makefile in Thresher root directory

BASE=$(pwd)

cd $BASE/lib/WALA && git pull

#!/bin/bash

# should be run only from Makefile in Thresher root directory

# get WALA
git clone https://github.com/wala/WALA.git && mv WALA lib
# get z3
git clone https://git01.codeplex.com/z3 && mv z3 lib
# get ScalaZ3
git clone https://github.com/psuter/ScalaZ3.git && mv ScalaZ3 lib


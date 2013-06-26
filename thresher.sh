#!/bin/bash
THRESHER_HOME=$(pwd)
SCALA_VERSION=2.9.2
Z3_VERSION=x64/4.3

LD_LIBRARY_PATH=$THRESHER_HOME/lib/z3/ java -cp .:bin:$THRESHER_HOME/lib/WALA/com.ibm.wala.core/bin:$THRESHER_HOME/lib/WALA/com.ibm.wala.util/bin/:$THRESHER_HOME/lib/WALA/com.ibm.wala.ide/bin/:$THRESHER_HOME/lib/WALA/com.ibm.wala.shrike/bin/:$THRESHER_HOME/lib/z3/com.microsoft.z3.jar edu/colorado/thresher/core/Main $@
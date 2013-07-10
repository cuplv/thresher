#!/bin/bash
THRESHER_HOME=$(pwd)

LD_LIBRARY_PATH=$THRESHER_HOME/lib/z3/ java -cp .:bin:$THRESHER_HOME/lib/WALA/com.ibm.wala.core/bin:$THRESHER_HOME/lib/WALA/com.ibm.wala.util/bin/:$THRESHER_HOME/lib/WALA/com.ibm.wala.ide/bin/:$THRESHER_HOME/lib/WALA/com.ibm.wala.shrike/bin/:$THRESHER_HOME/lib/z3/com.microsoft.z3.jar edu/colorado/thresher/core/Main $@
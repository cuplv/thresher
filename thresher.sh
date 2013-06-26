#!/bin/bash
THRESHER_HOME=$(pwd)
SCALA_VERSION=2.9.2
Z3_VERSION=x64/4.3

LD_LIBRARY_PATH=$THRESHER_HOME/lib/ScalaZ3/z3/$Z3_VERSION/lib/ java -cp .:bin:$THRESHER_HOME/lib/WALA/com.ibm.wala.core/bin:$THRESHER_HOME/lib/WALA/com.ibm.wala.util/bin/:$THRESHER_HOME/lib/ScalaZ3/target/scala_$SCALA_VERSION/classes/:$THRESHER_HOME/lib/WALA/com.ibm.wala.ide/bin/:$THRESHER_HOME/lib/WALA/com.ibm.wala.shrike/bin/ edu/colorado/thresher/core/Main $@
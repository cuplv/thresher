#!/bin/bash

# should be run only from Makefile in Thresher root directory

# get WALA
git clone https://github.com/wala/WALA.git && mv WALA lib && sed -i 's/private/protected/g' lib/WALA/com.ibm.wala.util/src/com/ibm/wala/fixpoint/IntSetVariable.java
# last command is a bad hack to prevent compilation problems on older jvms



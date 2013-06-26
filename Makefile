SCALA_VERSION = 2.9.2

all:
	mkdir -p bin
	javac -d bin -cp .:lib/WALA/com.ibm.wala.core/bin:lib/WALA/com.ibm.wala.util/bin/:lib/WALA/com.ibm.wala.ide/bin/:lib/WALA/com.ibm.wala.shrike/bin/:lib/z3/com.microsoft.z3.jar src/edu/colorado/thresher/core/*.java src/edu/colorado/thresher/external/*.java

install-deps:
	./build/install_deps.sh

deps:
	./build/build_deps.sh

update-deps:
	./build/update_deps.sh

tests:
	./build/build_tests.sh


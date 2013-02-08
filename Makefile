SCALA_VERSION = 2.9.2

all:
	javac -d bin -cp .:lib/WALA/com.ibm.wala.core/bin:lib/WALA/com.ibm.wala.util/bin/:lib/ScalaZ3/target/scala_$(SCALA_VERSION)/classes/:lib/WALA/com.ibm.wala.ide/bin/:lib/WALA/com.ibm.wala.shrike/bin/ src/edu/colorado/thresher/*.java

install-deps:
	./build/install_deps.sh

deps:
	./build/build_deps.sh



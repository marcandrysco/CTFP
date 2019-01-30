CXX = g++
LD  = g++
CXXFLAGS = -g -Wall -Werror -O2 -std=gnu++17 -fpic
LDFLAGS = -lm

IVAL = ival/inc.hpp \
       ival/fp.hpp \
       ival/ival.hpp \
       ival/range.hpp \
       ival/pass.hpp \

all: ctfp-fast.so

ctfp-fast.so: src/llvm.o Makefile
	$(LD) -shared $(LDFLAGS) src/llvm.o -o $@ `llvm-config --ldflags --libs`

src/llvm.o: src/llvm.cpp $(IVAL) Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@

run: all
	clang test.c -O2 -o test.fast.ll -S -emit-llvm -fplugin=./ctfp-fast.so
	clang check.c test.fast.ll -o check
	./check

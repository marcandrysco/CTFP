CC = g
CXX = g++
LD = g++
CFLAGS = -O2 -fpic -Wall
CXXFLAGS = -g -O2 -fpic -Wall -Werror -std=gnu++17 -I/usr/lib/llvm-6.0/include
LDFLAGS = -lm
OBJ = opt.o   fp.o   ivali64.o   ivalf64.o   rangei64.o   rangef64.o   range.o
INC = opt.hpp fp.hpp ivali64.hpp ivalf64.hpp rangei64.hpp rangef64.hpp range.hpp inc.hpp defs.h


### Build Rules

all: opt.so


## LLVM Header

llvm.hpp.gch: llvm.hpp Makefile
	$(CXX) $(CXXFLAGS) $< -o $@

## Optimizer

opt.so: $(OBJ)
	$(LD) -shared $^ -o $@ `llvm-config --ldflags --libs`

opt.o: opt.cpp $(INC) Makefile llvm.hpp.gch
	$(CXX) -c $(CXXFLAGS) $< -o $@ -include llvm.hpp

%.o: %.cpp $(INC) Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@


run: 
	opt mul.ll -o mul.opt.ll -load ./opt.so -ctfp-opt -S
	opt mul.opt.ll -o mul.opt.dce.ll -dce -S
	clang mul.opt.ll -o mul.opt.s -S
	clang mul.opt.dce.ll -o mul.opt.dce.s -S

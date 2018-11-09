CC = g
CXX = g++
LD = g++
CFLAGS = -O2 -fpic -Wall
CXXFLAGS = -g -O2 -fpic -Wall -Werror -std=gnu++17 -I/usr/lib/llvm-6.0/include
LDFLAGS = -lm
OBJ = fact.o   range.o   ival.o   main.o
INC = fact.hpp range.hpp ival.hpp inc.hpp

### Build Rules

all: prove


## LLVM Header

llvm.hpp.gch: llvm.hpp Makefile
	$(CXX) $(CXXFLAGS) $< -o $@


## Prover

prove: $(OBJ)
	$(LD) $^ -o $@ `llvm-config --ldflags --libs`

main.o: main.cpp $(INC) Makefile llvm.hpp.gch
	$(CXX) -c $(CXXFLAGS) $< -o $@ -include llvm.hpp

ival.o: ival.cpp $(INC) Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@

range.o: range.cpp $(INC) Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@

fact.o: fact.cpp $(INC) Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@


run: all
	./prove

debug : all
	gdb ./prove -ex run

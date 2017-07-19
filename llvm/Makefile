CC = gcc
CXX = g++
LD = gcc
CFLAGS = -O2 -fpic
CXXFLAGS = -O2 -I/usr/lib/llvm-4.0/include -fpic
LDFLAGS = -lm
OBJ = main.o


all: ctfp.so

ctfp.so: $(OBJ)
	$(LD) -shared $(LDFLAGS) $^ -o $@

%.o: %.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

%.o: %.cpp Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@


run: all
	@#./mycc -c test.c -o test.o && clang test.o -o test && ./test
	#clang -c -S -O2 test.c -o test.ll -fplugin=./ctfp.so -emit-llvm
	clang -O2 test.c -o test -fplugin=./ctfp.so ../lib/ctfp.o && ./test

CC = clang
CXX = clang++
LD = clang
CFLAGS = -g -O2 -fpic -std=c11
CXXFLAGS = -g -O2 -I/usr/lib/llvm-4.0/include -fpic -std=c++11
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
	@#llc -filetype=obj test.ll -o test.o
	@#clang test.o -o test
	@#./test
	@#clang -g -c -S -O2 test.c -o test.ll -emit-llvm -fplugin=./ctfp.so
	@#clang -c -S -O2 test.c -o test.ll -emit-llvm
	@#opt test.ll -o test.ll.2 -S -load=./ctfp.so -ctfp
	@#cat test.ll
	clang -S -emit-llvm -O2 test.c -o test.ll -fplugin=./ctfp.so
	clang -O2 test.c -o test -fplugin=./ctfp.so -lm
	./test

debug: all
	gdb ./test -ex 'run'

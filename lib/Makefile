CC = gcc
LD = gcc
CFLAGS = -O2 -Wall -march=native -fpic
LDFLAGS = -lm -mavx2


all: ctfp.o ctfp.ll test

test: test.o ctfp.o
	$(LD) $(LDFLAGS) $^ -o $@

test.o: test.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

ctfp.o: ctfp.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

ctfp.ll: ctfp.c Makefile
	clang -c -O2 $< -o $@ -emit-llvm
	clang -c -O2 $< -o ctfp.ll.s -S -emit-llvm -fpic


run: all test
	./test

CC = gcc
LD = gcc
CFLAGS = -g -O2 -Wall -mavx2 -march=native
LDFLAGS = -lm -mavx2


all: ctfp.o ctfp.ll test

test: test.o ctfp.o
	$(LD) $(LDFLAGS) $^ -o $@

test.o: test.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

ctfp.o: ctfp.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

ctfp.ll: ctfp.c Makefile
	clang -c $(CFLAGS) -O2 $< -o $@ -emit-llvm


run: test
	./test

CC = gcc
LD = gcc
CFLAGS = -g -O2 -Wall -march=native
LDFLAGS = -lm


all: ctfp.o ctfp.ll test

test: test.o ctfp.o
	$(LD) $(LDFLAGS) $^ -o $@

test.o: test.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

ctfp.o: ctfp.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

ctfp.ll: ctfp.c Makefile
	clang -c -O2 $< -o $@ -emit-llvm


run: test
	./test

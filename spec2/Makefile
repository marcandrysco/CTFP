all: ctfp.o ctfp.ll ctfp.bc ctfp-llvm.so

ctfp.o: ctfp.bc Makefile
	llc -O3 -mcpu=broadwell ctfp.bc -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s

ctfp.bc: ctfp.ll Makefile
	opt ctfp.ll -o ctfp.bc

ctfp.ll: gen.py add.spec Makefile
	./gen.py

ctfp-llvm.so: llvm.cpp Makefile ctfp.bc
	#clang -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11


test: ctfp-test

ctfp-test: test.c ctfp.bc Makefile
	clang test.c ctfp.bc -o ctfp-test -O2 -lm -mcpu=broadwell -std=gnu11


run: all test
	./ctfp-test


.PHONY: all test run

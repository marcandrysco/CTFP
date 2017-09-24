all: ctfp.o ctfp.ll ctfp.bc ctfp-llvm.so

ctfp.o: ctfp.bc Makefile
	llc -O3 -mcpu=broadwell ctfp.bc -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s

ctfp.bc: ctfp.ll Makefile
	opt ctfp.ll -O2 -o ctfp.bc

ctfp.ll: gen.py add.spec Makefile
	./gen.py

ctfp-llvm.so: llvm.cpp Makefile ctfp.bc
	clang -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11


run: all

MATH = math/__cos.c \
       math/__cosdf.c \
       math/exp.c \
       math/expf.c \
       math/scalb.c \
       math/scalbn.c \

all: ctfp.bc ctfp-llvm.so ctfp-math.so

ctfp.bc: ctfp.c Makefile
	clang -c -O2 $< -o $@ -emit-llvm -fpic

ctfp-llvm.so: llvm.cpp Makefile ctfp.bc
	clang -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11

ctfp-math.so: $(MATH) Makefile ctfp-llvm.so math/libm.h
	clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-llvm.so -nostdlib

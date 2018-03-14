CPU=ivybridge
#CPU=skylake
#CPU=barcelona

all: ctfp.ll

ctfp.ll: gen.hs Makefile
	@#runghc $<
	runghc $< > ctfp.ll
	@##opt ctfp.ll > ctfp.bc
	opt -early-cse ctfp.ll -S > ctfp.bc
	llc -O3 -mcpu=$(CPU) ctfp.bc -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s


run: all
	clang test.c ctfp.bc -o test -Werror -Wall
	./test


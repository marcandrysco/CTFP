CPU=ivybridge
#CPU=skylake
#CPU=barcelona

all: run

run: gen.hs Makefile
	runghc $< | tee ctfp.ll
	llc -O3 -mcpu=$(CPU) ctfp.ll -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s

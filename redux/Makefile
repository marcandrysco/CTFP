CPU=ivybridge
#CPU=skylake
#CPU=barcelona

all: ctfp.bc ctfp-llvm.so
#all: ctfp.z3

ctfp.z3: gen.hs Makefile
	runghc $< z3

ctfp.bc: gen.hs Makefile
	@#runghc $<
	runghc $< > ctfp.ll
	@##opt ctfp.ll > ctfp.bc
	opt -S -early-cse ctfp.ll > ctfp.2.ll
	opt -early-cse -always-inline ctfp.ll > ctfp.bc
	llc -O3 -mcpu=$(CPU) ctfp.bc -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s


## LLVM Tool

ctfp-llvm.so: llvm.cpp Makefile
	clang++ -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11


## Test Tool

test: test.o ctfp.bc
	clang $^ -o $@

test.o: test.c Makefile
	clang -c -O2 $< -o $@ -Werror -Wall


## Performance Tool

perf: perf.o bench_ref.o bench_restrict.o bench_full.o
	clang $^ -o $@ -lm

perf.o: perf.c Makefile
	clang -c -O2 $< -o $@ -Werror -Wall

bench_ref.o: bench.c Makefile
	clang -c -O2 $< -o $@ -Werror -Wall -D BENCH=ref -march=$(CPU)

bench_restrict.o: bench.c ctfp-llvm.so ctfp.bc Makefile
	CTFP_VER=1 CTFP_DIR=. clang -g -c -O2 $< -o $@ -Werror -Wall -D BENCH=ctfp1 -march=$(CPU) $(MATH) -fplugin=./ctfp-llvm.so

bench_full.o: bench.c ctfp-llvm.so ctfp.bc Makefile
	CTFP_VER=2 CTFP_DIR=. clang -g -c -O2 $< -o $@ -Werror -Wall -D BENCH=ctfp2 -march=$(CPU) $(MATH) -fplugin=./ctfp-llvm.so


## Run

run3:
	runghc gen.hs test > run.out
	opt -S -early-cse run.out > run.opt

run2: all test
	./test

run: all test perf
	./test
	./perf

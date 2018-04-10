CPU=ivybridge
#CPU=skylake
#CPU=barcelona

#all: prover
all: ctfp.bc ctfp-llvm.so ctfp-clean.so

## LLVM Generator

gen: gen.hs Makefile
	ghc $< -o $@
	touch $@


## LLVM Header

llvm.hpp.gch: llvm.hpp Makefile
	clang++ -g -O2 -Wall -fpic $< -o $@ -std=gnu++11


## Prover

prover: prover.cpp llvm.hpp.gch Makefile
	clang++ -g -Wall -Werror -fpic -include llvm.hpp -std=gnu++11 -O2 $< -o $@ `llvm-config --ldflags --libs` -lz3


## CTFP Targets

ctfp.z3: gen Makefile
	./gen z3

ctfp.ll: gen Makefile
	./gen > ctfp.ll

ctfp.cse.ll: ctfp.ll
	opt -early-cse ctfp.ll -S > ctfp.cse.ll

ctfp.bc: ctfp.cse.ll ctfp-clean.so
	opt -load ./ctfp-clean.so -always-inline -ctfp-clean ctfp.cse.ll > ctfp.bc
	llc -O3 -mcpu=$(CPU) ctfp.bc -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s

ctfp.dbg.bc: gen Makefile ctfp-clean.so
	./gen debug > ctfp.dbg.ll
	opt -early-cse -always-inline ctfp.dbg.ll > ctfp.dbg.bc


## LLVM Tool

ctfp-llvm.so: llvm.cpp Makefile
	clang++ -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11

ctfp-clean.so: clean.cpp Makefile
	clang++ -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11


## Test Tool

test: test.o ctfp.dbg.bc
	clang $^ -o $@ -lm

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

run1: prover
	./prover

run4: gen
	./gen

run3:
	runghc gen.hs test > run.out
	opt -S -early-cse run.out > run.opt

run5: all test
	./test

run: all test perf
	./test
	./perf

#CPU=ivybridge
CPU=skylake
#CPU=barcelona

#a: gen
	#./gen

#all: prover
all: ctfp.bc ctfp-llvm.so ctfp-clean.so ctfp-math-1.so ctfp-math-2.so

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
	opt -early-cse -dce ctfp.ll -S > ctfp.cse.ll

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


## Math Library

ctfp-math-1.so: $(MATH) Makefile ctfp-llvm.so math/libm.h ctfp.bc
	CTFP_VER=1 CTFP_DIR=. clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-llvm.so -nostdlib

ctfp-math-2.so: $(MATH) Makefile ctfp-llvm.so math/libm.h ctfp.bc
	CTFP_VER=2 CTFP_DIR=. clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-llvm.so -nostdlib


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
	CTFP_VER=1 CTFP_DIR=. clang -g -c -O2 $< -o $@ -Werror -Wall -D BENCH=ctfp1 -march=$(CPU) -fplugin=./ctfp-llvm.so

bench_full.o: bench.c ctfp-llvm.so ctfp.bc Makefile
	CTFP_VER=2 CTFP_DIR=. clang -g -c -O2 $< -o $@ -Werror -Wall -D BENCH=ctfp2 -march=$(CPU) -fplugin=./ctfp-llvm.so


## Run

run8: prover
	./prover

run4: gen
	./gen

run3:
	runghc gen.hs test > run.out
	opt -S -early-cse run.out > run.opt

run: test
	./test

run1: all test perf
	./test
	./perf


## Math files

MATH = \
	math/acos.c \
	math/acosf.c \
	math/acosh.c \
	math/acoshf.c \
	math/acoshl.c \
	math/acosl.c \
	math/asin.c \
	math/asinf.c \
	math/asinh.c \
	math/asinhf.c \
	math/asinhl.c \
	math/asinl.c \
	math/atan2.c \
	math/atan2f.c \
	math/atan2l.c \
	math/atan.c \
	math/atanf.c \
	math/atanh.c \
	math/atanhf.c \
	math/atanhl.c \
	math/atanl.c \
	math/cbrt.c \
	math/cbrtf.c \
	math/cbrtl.c \
	math/ceil.c \
	math/ceilf.c \
	math/ceill.c \
	math/copysign.c \
	math/copysignf.c \
	math/copysignl.c \
	math/__cos.c \
	math/cos.c \
	math/__cosdf.c \
	math/cosf.c \
	math/cosh.c \
	math/coshf.c \
	math/coshl.c \
	math/__cosl.c \
	math/cosl.c \
	math/erf.c \
	math/erff.c \
	math/erfl.c \
	math/exp10.c \
	math/exp10f.c \
	math/exp10l.c \
	math/exp2.c \
	math/exp2f.c \
	math/exp2l.c \
	math/exp.c \
	math/expf.c \
	math/expl.c \
	math/expm1.c \
	math/expm1f.c \
	math/expm1l.c \
	math/__expo2.c \
	math/__expo2f.c \
	math/fabs.c \
	math/fabsf.c \
	math/fabsl.c \
	math/fdim.c \
	math/fdimf.c \
	math/fdiml.c \
	math/finite.c \
	math/finitef.c \
	math/floor.c \
	math/floorf.c \
	math/floorl.c \
	math/fma.c \
	math/fmaf.c \
	math/fmal.c \
	math/fmax.c \
	math/fmaxf.c \
	math/fmaxl.c \
	math/fmin.c \
	math/fminf.c \
	math/fminl.c \
	math/fmod.c \
	math/fmodf.c \
	math/fmodl.c \
	math/__fpclassify.c \
	math/__fpclassifyf.c \
	math/__fpclassifyl.c \
	math/frexp.c \
	math/frexpf.c \
	math/frexpl.c \
	math/hypot.c \
	math/hypotf.c \
	math/hypotl.c \
	math/ilogb.c \
	math/ilogbf.c \
	math/ilogbl.c \
	math/__invtrigl.c \
	math/j0.c \
	math/j0f.c \
	math/j1.c \
	math/j1f.c \
	math/jn.c \
	math/jnf.c \
	math/ldexp.c \
	math/ldexpf.c \
	math/ldexpl.c \
	math/lgamma.c \
	math/lgammaf.c \
	math/lgammaf_r.c \
	math/lgammal.c \
	math/lgamma_r.c \
	math/llrint.c \
	math/llrintf.c \
	math/llrintl.c \
	math/llround.c \
	math/llroundf.c \
	math/llroundl.c \
	math/log10.c \
	math/log10f.c \
	math/log10l.c \
	math/log1p.c \
	math/log1pf.c \
	math/log1pl.c \
	math/log2.c \
	math/log2f.c \
	math/log2l.c \
	math/logb.c \
	math/logbf.c \
	math/logbl.c \
	math/log.c \
	math/logf.c \
	math/logl.c \
	math/lrint.c \
	math/lrintf.c \
	math/lrintl.c \
	math/lround.c \
	math/lroundf.c \
	math/lroundl.c \
	math/modf.c \
	math/modff.c \
	math/modfl.c \
	math/nan.c \
	math/nanf.c \
	math/nanl.c \
	math/nearbyint.c \
	math/nearbyintf.c \
	math/nearbyintl.c \
	math/nextafter.c \
	math/nextafterf.c \
	math/nextafterl.c \
	math/nexttoward.c \
	math/nexttowardf.c \
	math/nexttowardl.c \
	math/__polevll.c \
	math/pow.c \
	math/powf.c \
	math/powl.c \
	math/remainder.c \
	math/remainderf.c \
	math/remainderl.c \
	math/__rem_pio2.c \
	math/__rem_pio2f.c \
	math/__rem_pio2_large.c \
	math/__rem_pio2l.c \
	math/remquo.c \
	math/remquof.c \
	math/remquol.c \
	math/rint.c \
	math/rintf.c \
	math/rintl.c \
	math/round.c \
	math/roundf.c \
	math/roundl.c \
	math/scalb.c \
	math/scalbf.c \
	math/scalbln.c \
	math/scalblnf.c \
	math/scalblnl.c \
	math/scalbn.c \
	math/scalbnf.c \
	math/scalbnl.c \
	math/__signbit.c \
	math/__signbitf.c \
	math/__signbitl.c \
	math/signgam.c \
	math/significand.c \
	math/significandf.c \
	math/__sin.c \
	math/sin.c \
	math/sincos.c \
	math/sincosf.c \
	math/sincosl.c \
	math/__sindf.c \
	math/sinf.c \
	math/sinh.c \
	math/sinhf.c \
	math/sinhl.c \
	math/__sinl.c \
	math/sinl.c \
	math/__tan.c \
	math/tan.c \
	math/__tandf.c \
	math/tanf.c \
	math/tanh.c \
	math/tanhf.c \
	math/tanhl.c \
	math/__tanl.c \
	math/tanl.c \
	math/tgamma.c \
	math/tgammaf.c \
	math/tgammal.c \
	math/trunc.c \
	math/truncf.c \
	math/truncl.c \


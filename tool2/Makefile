all: ctfp.o ctfp.ll ctfp.bc ctfp-llvm.so # ctfp-math-1.so ctfp-math-3.so

ctfp.o: ctfp.bc Makefile
	llc -O3 -mcpu=broadwell ctfp.bc -o ctfp.o -filetype=obj
	objdump -d ctfp.o -M intel > ctfp.s

ctfp.bc: ctfp.ll Makefile
	opt ctfp.ll -always-inline -o ctfp.bc

ctfp.ll: gen.py tpl.ll Makefile
	./gen.py

llvm.hpp.gch: llvm.hpp Makefile
	clang++ -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11

ctfp-llvm.so: llvm.cpp Makefile ctfp.bc llvm.hpp.gch
	clang++ -include llvm.hpp -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11


test: ctfp-test ctfp-bench ctfp-count

ctfp-test: test.c ctfp.bc Makefile
	clang test.c ctfp.bc -o ctfp-test -O2 -lm -mcpu=broadwell -std=gnu11

ctfp-math-1.so: $(MATH) Makefile ctfp-llvm.so math/libm.h
	CTFP_VER=1 CTFP_DIR=. clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-llvm.so -nostdlib

ctfp-math-3.so: $(MATH) Makefile ctfp-llvm.so math/libm.h
	CTFP_VER=3 CTFP_DIR=. clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-llvm.so -nostdlib


ctfp-bench: bench.o bench_ref.o bench_ctfp1.o bench_ctfp3.o
	clang $^ -o $@ -lm

bench.o: bench.c bench.h Makefile
	clang -c -g -O2 $< -o $@

bench_ref.o: bench_tpl.c bench.h Makefile
	clang -D BENCH=run_ref -O2 -g -O2 -c $< -o $@ -march=native -fno-fast-math

bench_ctfp1.o: bench_tpl.c ctfp-llvm.so bench.h Makefile
	CTFP_VER=1 CTFP_DIR=. clang -D BENCH=run_ctfp1 -fplugin=./ctfp-llvm.so -O2 -g -O2 -c $< -o $@ -march=native -fno-fast-math

bench_ctfp3.o: bench_tpl.c ctfp-llvm.so bench.h Makefile
	CTFP_VER=3 CTFP_DIR=. clang -D BENCH=run_ctfp3 -fplugin=./ctfp-llvm.so -O2 -g -O2 -c $< -o $@ -march=native -fno-fast-math


ctfp-count: ctfp.s Makefile
	cat $< | sed -n 's/^\s*[0-9a-f]*:\s*\([0-9a-f][0-9a-f] \)*\s*\([a-z]*\)\s.*/\2/p' | sort | uniq -c > $@


run: all test
	./ctfp-test
	./ctfp-bench
	@#./ctfp-test
	@#clang -shared -O2 -Wall -march=native -fpic math/exp.c -o /dev/null -fplugin=./ctfp-llvm.so -nostdlib
	@#opt test.ll -load=./ctfp-llvm.so -ctfp -S -o=/dev/null


.PHONY: all test run


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


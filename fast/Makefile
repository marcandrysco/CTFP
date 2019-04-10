CXX = g++
LD  = g++
CXXFLAGS = -g -Wall -Werror -O2 -std=gnu++17 -fpic
LDFLAGS = -lm

#CPU=ivybridge
CPU=skylake
#CPU=barcelona


IVAL = ival/inc.hpp \
       ival/fp.hpp \
       ival/ival.hpp \
       ival/range.hpp \
       ival/pass.hpp \

# All Targets

all: ctfp.bc \
     ctfp-basic.so \
     ctfp-rest.so \
     ctfp-full.so \
     ctfp-fast.so \
     ctfp-flags.so \
     ctfp-stats.so \
     ctfp-stats-runtime.o \
     ctfp-basic-math.so \
     ctfp-rest-math.so \
     ctfp-full-math.so \
     ctfp-fast-math.so \
     ctfp-flags-math.so \


## LLVM Generator

gen: gen.hs Makefile
	ghc $< -o $@
	touch $@


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

ctfp.bc.c: ctfp.bc
	xxd -i ctfp.bc > ctfp.bc.c

ctfp.dbg.ll: gen Makefile ctfp-clean.so
	./gen debug > ctfp.dbg.ll

ctfp.dbg.bc: ctfp.dbg.ll Makefile
	opt -early-cse -always-inline ctfp.dbg.ll > ctfp.dbg.bc


## Cleaning Pass

ctfp-clean.so: src/clean.cpp Makefile
	clang++ -shared -O2 -Wall -march=native -fpic $< -o $@ -std=gnu++11


## CTFP Modules

ctfp-basic.so: src/llvm-basic.o Makefile
	$(LD) -shared $(LDFLAGS) $< -o $@ `llvm-config --ldflags --libs`

ctfp-rest.so: src/llvm-rest.o Makefile
	$(LD) -shared $(LDFLAGS) $< -o $@ `llvm-config --ldflags --libs`

ctfp-full.so: src/llvm-full.o Makefile
	$(LD) -shared $(LDFLAGS) $< -o $@ `llvm-config --ldflags --libs`

ctfp-fast.so: src/llvm-fast.o Makefile
	$(LD) -shared $(LDFLAGS) $< -o $@ `llvm-config --ldflags --libs`

ctfp-flags.so: src/llvm-flags.o Makefile
	$(LD) -shared $(LDFLAGS) $< -o $@ `llvm-config --ldflags --libs`

ctfp-stats.so: src/llvm-stats.o Makefile
	$(LD) -shared $(LDFLAGS) $< -o $@ `llvm-config --ldflags --libs`

ctfp-stats-runtime.o: src/stats.c Makefile
	gcc -c -O2 -Wall -march=native -Wno-psabi -fPIC $< -o $@ -lm -lpthread

ctfp-basic-math.so: $(MATH) Makefile ctfp-basic.so
	clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-basic.so -nostdlib

ctfp-rest-math.so: $(MATH) Makefile ctfp-rest.so
	clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-rest.so -nostdlib

ctfp-full-math.so: $(MATH) Makefile ctfp-full.so
	clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-full.so -nostdlib

ctfp-fast-math.so: $(MATH) Makefile ctfp-fast.so
	clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-fast.so -nostdlib

ctfp-flags-math.so: $(MATH) Makefile ctfp-flags.so
	clang -shared -O2 -Wall -march=native -fpic $(MATH) -o $@ -fplugin=./ctfp-flags.so -nostdlib

src/llvm-basic.o: src/llvm.cpp $(IVAL) ctfp.bc.c Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@ -DCTFP_MODE=\"BASIC\"

src/llvm-rest.o: src/llvm.cpp $(IVAL) ctfp.bc.c Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@ -DCTFP_MODE=\"REST\"

src/llvm-full.o: src/llvm.cpp $(IVAL) ctfp.bc.c Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@ -DCTFP_MODE=\"FULL\"

src/llvm-fast.o: src/llvm.cpp $(IVAL) ctfp.bc.c Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@ -DCTFP_MODE=\"FAST\"

src/llvm-flags.o: src/llvm.cpp $(IVAL) ctfp.bc.c Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@ -DCTFP_MODE=\"FLAGS\"

src/llvm-stats.o: src/llvm.cpp $(IVAL) ctfp.bc.c Makefile
	$(CXX) $(CXXFLAGS) $< -c -o $@ -DCTFP_MODE=\"STATS\"


## Clean Rules

clean:
	rm -f ctfp.bc ctfp-*.so src/*.o


run: all
	clang test.c -O2 -o test.ll -S -emit-llvm -fplugin=./ctfp-flags.so
	#clang test.ll ctfp-stats-runtime.o -lm -o test.bin
	#./test.bin


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

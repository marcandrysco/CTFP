CC = clang
LD = clang
CFLAGS = -fno-fast-math -O2 -g -march=native
LDFLAGS = -fno-fast-math -lm
DEPS = Makefile common.h

all: ctfp-test

ctfp-test: main.o bench_ref.o bench_ctfp.o ../tool/ctfp-math.so
	$(LD) $(LDFLAGS) $^ -o $@

main.o: main.c $(DEPS)
	$(CC) -c $(CFLAGS) $< -o $@

bench_ref.o: bench.c $(DEPS)
	$(CC) -D BENCH=run_ref -c $(CFLAGS) $< -o $@

bench_ctfp.o: bench.c $(DEPS)
	#$(CC) -D BENCH=run_ctfp -D CTFP -c $(CFLAGS) $< -o $@
	$(CC) -D BENCH=run_ctfp -D CTFP -c -fplugin=../spec2/ctfp-llvm.so $(CFLAGS) $< -o $@

run: all
	./ctfp-test

debug: all
	gdb ./ctfp-test -ex 'run'

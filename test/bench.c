#include "common.h"
#include <float.h>
#include <emmintrin.h>
#include <math.h>


/*
 * sources and sinks
 */
volatile double sink, src1, src2;


/**
 * Base benchmark of a fenced store.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t base(void)
{
	double in, out;
	uint32_t begin, end;

	src1 = 0.0;
	asm volatile("");
	in = src1;

	asm volatile("" :: "x"(in), "x"(out));
	begin = perf_begin();

	//out = in;
	//asm volatile("movq %0,%%r15" :: "x"(out) : "r15");
	//sink = out;
	//_mm_mfence();

	end = perf_end();
	asm volatile("" :: "x"(in), "x"(out));

	return end - begin;
}

/**
 * Add doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t add_dbl(void)
{
	double in1, in2, in3, in4, in5, in6, in7, in8, out;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	in3 = src1;
	in4 = src2;
	in5 = src1;
	in6 = src2;
	in7 = src1;
	in8 = src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(in3), "x"(in4), "x"(in5), "x"(in6), "x"(in7), "x"(in8), "x"(out));
	begin = perf_begin();

	out = in1 + in2 + in3 + in4 + in5 + in6 + in7 + in8;
	asm volatile("movq %0,%%r15" :: "x"(out) : "r15");
	asm volatile("add %%r15,%%r15" ::: "r15");
	//sink = out;
	//_mm_mfence();

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(in3), "x"(in4), "x"(in5), "x"(in6), "x"(in7), "x"(in8), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Multiply doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t mul_dbl(void)
{
	double in1, in2, in3, in4, in5, in6, in7, in8, out;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	in3 = src1;
	in4 = src2;
	in5 = src1;
	in6 = src2;
	in7 = src1;
	in8 = src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(in3), "x"(in4), "x"(in5), "x"(in6), "x"(in7), "x"(in8), "x"(out));
	begin = perf_begin();

	out = in1 * in2 * in3 * in4 * in5 * in6 * in7 * in8;
	asm volatile("movq %0,%%r15" :: "x"(out) : "r15");
	asm volatile("add %%r15,%%r15" ::: "r15");
	//sink = out;
	//_mm_mfence();

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(in3), "x"(in4), "x"(in5), "x"(in6), "x"(in7), "x"(in8), "x"(out));

	sink = out;

	return end - begin;
}


/**
 * Add double normal*normal=normal benchmark.
 *   &returns: The execution time.
 */
static uint32_t adnnn(void)
{
	src1 = 1.6; src2 = 2.3;

	return add_dbl();
}

/**
 * Add double subnormal*subnormal=subnormal benchmark.
 *   &returns: The execution time.
 */
static uint32_t adsss(void)
{
	src1 = 1.6e-312; src2 = 2.3e-314;

	return add_dbl();
}


/**
 * Multiply double normal*normal=normal double benchmark.
 *   &returns: The execution time.
 */
static uint32_t mul_dnnn(void)
{
	src1 = 1.6; src2 = 2.3;

	return mul_dbl();
}

/**
 * Multiply double subnormal*normal=subnormal double benchmark.
 *   &returns: The execution time.
 */
static uint32_t mdsns(void)
{
	src1 = 1.6e-312; src2 = 2.3;

	return mul_dbl();
}

static uint32_t mul_dssz(void)
{
	src1 = 1.6e-312; src2 = 2.3e-312;

	return mul_dbl();
}

/**
 * Multiply double normal*inf=inf double benchmark.
 *   &returns: The execution time.
 */
static uint32_t mdnii(void)
{
	src1 = 1.6; src2 = INFINITY;

	return mul_dbl();
}

bench_f BENCH[bench_n] = {
	base,
	adnnn,
	adsss,
	mul_dnnn,
	mdsns,
	mul_dssz,
	mdnii,
};

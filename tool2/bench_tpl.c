#include "bench.h"
#include <float.h>
#include <emmintrin.h>
#include <math.h>
#include <string.h>


#define DO_32(thing)  thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing \
                      thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing


/**
 * Base benchmark of a fenced store.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t base(void)
{
	double in, out, res;
	uint32_t begin, end;

	src1 = 0.0;
	in = src1;
	res = src1;

	asm volatile("" :: "x"(in), "x"(out));
	begin = perf_begin();

	DO_32(
		out = in;
		in = m_xor_d(m_xor_d(out, res), in);
	)

	end = perf_end();
	asm volatile("" :: "x"(in), "x"(out));

	return end - begin;
}

/**
 * Add floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t add_flt(void)
{
	uint32_t idx;
	double in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	res = src1 + src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out), "x"(res));
	begin = perf_begin();

	DO_32(
		out = in1 + in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out), "x"(res));

	sink = out;

	return end - begin;
}

/**
 * Add doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t add_dbl(void)
{
	uint32_t idx;
	double in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	res = src1 + src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out), "x"(res));
	begin = perf_begin();

	DO_32(
		out = in1 + in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out), "x"(res));

	sink = out;

	return end - begin;
}

/**
 * Multiply floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t mul_flt(void)
{
	float in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1f;
	in2 = src2f;
	res = src1f * src2f;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();

	DO_32(
		out = in1 * in2;
		in1 = m_xor_f(m_xor_f(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sinkf = out;

	return end - begin;
}

/**
 * Multiply floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t mul_dbl(void)
{
	float in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	res = src1 * src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();

	DO_32(
		out = in1 * in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Divide floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t div_flt(void)
{
	float in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1f;
	in2 = src2f;
	res = src1f / src2f;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();

	DO_32(
		out = in1 / in2;
		in1 = m_xor_f(m_xor_f(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sinkf = out;

	return end - begin;
}

/**
 * Divide doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t div_dbl(void)
{
	double in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	res = src1 / src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();

	DO_32(
		out = in1 / in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Square root floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t sqrt_flt(void)
{
	float in1, out, res;
	uint32_t begin, end;

	in1 = src1f;
	res = sqrtf(src1f);

	asm volatile("" :: "x"(in1), "x"(out));
	begin = perf_begin();

	DO_32(
		out = sqrtf(in1);
		in1 = m_xor_f(m_xor_f(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(out));

	sinkf = out;

	return end - begin;
}

/**
 * Square root doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t sqrt_dbl(void)
{
	double in1, out, res;
	uint32_t begin, end;

	in1 = src1f;
	res = sqrt(src1f);

	asm volatile("" :: "x"(in1), "x"(out));
	begin = perf_begin();

	DO_32(
		out = sqrt(in1);
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(out));

	sinkf = out;

	return end - begin;
}


bench_f BENCH[op_n] = {
	base,
	add_flt,
	NULL,
	mul_flt,
	div_flt,
	sqrt_flt,
	add_dbl,
	NULL,
	mul_dbl,
	div_dbl,
	sqrt_dbl
};

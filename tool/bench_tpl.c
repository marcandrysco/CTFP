#include "bench.h"
#include <float.h>
#include <emmintrin.h>
#include <math.h>
#include <string.h>


static inline float do_dumb_thing_f(uint32_t i, float f)
{
	uint32_t t;
	static volatile uint32_t dumb_i;

	dumb_i = i;
	i ^= dumb_i;
	memcpy(&t, &f, 4);
	t ^= i;
	memcpy(&f, &t, 4);

	return t;
}

static inline double do_dumb_thing_d(uint64_t i, double f)
{
	uint64_t t;
	static volatile uint64_t dumb_i;

	dumb_i = i;
	i ^= dumb_i;
	memcpy(&t, &f, 8);
	t ^= i;
	memcpy(&f, &t, 8);

	return t;
}


/**
 * Base benchmark of a fenced store.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t base(void)
{
	double in1, in2, out, res;
	uint32_t begin, end;

	src1 = 0.0;
	in1 = src1;
	in2 = src2;
	res = src1;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		out = in1;
		in1 = m_xor_d(m_xor_d(out, res), in1);
		in2 = m_xor_d(m_xor_d(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	return end - begin;
}

/**
 * Add floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t add_flt(void)
{
	uint32_t idx;
	float in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1f;
	in2 = src2f;
	res = src1f + src2f;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 + in2;
		in1 = m_xor_f(m_xor_f(out, res), in1);
		in2 = m_xor_f(m_xor_f(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Add 4-floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t add_flt4(void)
{
	uint32_t idx;
	v4f in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = in1[2] = in1[3] = src1f;
	in2[0] = in2[1] = in2[2] = in2[3] = src2f;
	res[0] = res[1] = res[2] = res[3] = src1f + src2f;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 + in2;
		in1 = m_xor_4f(m_xor_4f(out, res), in1);
		in2 = m_xor_4f(m_xor_4f(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out[0];
	sink = out[1];
	sink = out[2];
	sink = out[3];

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

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 + in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
		in2 = m_xor_d(m_xor_d(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Add 2-doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t add_dbl2(void)
{
	uint32_t idx;
	v2d in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = src1;
	in2[0] = in2[1] = src2;
	res[0] = res[1] = src1 + src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 + in2;
		in1 = m_xor_2d(m_xor_2d(out, res), in1);
		in2 = m_xor_2d(m_xor_2d(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out[0];
	sink = out[1];

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
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 * in2;
		in1 = m_xor_f(m_xor_f(out, res), in1);
		in2 = m_xor_f(m_xor_f(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sinkf = out;

	return end - begin;
}

/**
 * Multiply 4-floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t mul_flt4(void)
{
	uint32_t idx;
	v4f in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = in1[2] = in1[3] = src1f;
	in2[0] = in2[1] = in2[2] = in2[3] = src2f;
	res[0] = res[1] = res[2] = res[3] = src1f * src2f;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 * in2;
		in1 = m_xor_4f(m_xor_4f(out, res), in1);
		in2 = m_xor_4f(m_xor_4f(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out[0];
	sink = out[1];
	sink = out[2];
	sink = out[3];

	return end - begin;
}

/**
 * Multiply floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t mul_dbl(void)
{
	double in1, in2, out, res;
	uint32_t begin, end;

	in1 = src1;
	in2 = src2;
	res = src1 * src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 * in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
		in2 = m_xor_d(m_xor_d(out, res), in2);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Multiply 2-doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t mul_dbl2(void)
{
	uint32_t idx;
	v2d in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = src1;
	in2[0] = in2[1] = src2;
	res[0] = res[1] = src1 * src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 * in2;
		in1 = m_xor_2d(m_xor_2d(out, res), in1);
		in2 = m_xor_2d(m_xor_2d(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out[0];
	sink = out[1];

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
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 / in2;
		in1 = m_xor_f(m_xor_f(out, res), in1);
		in2 = m_xor_f(m_xor_f(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	sinkf = out;

	return end - begin;
}

/**
 * Add floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t div_flt4(void)
{
	uint32_t idx;
	v4f in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = in1[2] = in1[3] = src1f;
	in2[0] = in2[1] = in2[2] = in2[3] = src2f;
	res[0] = res[1] = res[2] = res[3] = src1f / src2f;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 / in2;
		in1 = m_xor_4f(m_xor_4f(out, res), in1);
		in2 = m_xor_4f(m_xor_4f(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out[0];
	sink = out[1];
	sink = out[2];
	sink = out[3];

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
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 / in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
		in2 = m_xor_d(m_xor_d(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

	return end - begin;
}

/**
 * Divide 2-doubles.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t div_dbl2(void)
{
	uint32_t idx;
	v2d in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = src1;
	in2[0] = in2[1] = src2;
	res[0] = res[1] = src1 / src2;

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
		out = in1 / in2;
		in1 = m_xor_2d(m_xor_2d(out, res), in1);
		in2 = m_xor_2d(m_xor_2d(out, res), in2);
	)

	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out[0];
	sink = out[1];

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
	asm volatile("" :: "x"(in1), "x"(out));

	DO_32(
		asm volatile("" :: "x"(in1), "x"(out));
		out = sqrtf(in1);
		in1 = m_xor_f(m_xor_f(out, res), in1);
	)

	asm volatile("" :: "x"(in1), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(out));

	sinkf = out;

	return end - begin;
}

static inline v4f sqrt4f(v4f v)
{
	__m128 *i = (__m128 *)&v;
	*i = _mm_sqrt_ps(*i);

	return v;
}
/**
 * Square root 4-floats.
 *   &returns: The execution time.
 */
__attribute__((noinline)) static uint32_t sqrt_flt4(void)
{
	uint32_t idx;
	v4f in1, in2, out, res;
	uint32_t begin, end;

	in1[0] = in1[1] = in1[2] = in1[3] = src1f;
	res[0] = res[1] = res[2] = res[3] = sqrt(src1f);

	asm volatile("" :: "x"(in1), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(out));

	DO_32(
		out = sqrt4f(in1);
		in1 = m_xor_4f(m_xor_4f(out, res), in1);
	)

	asm volatile("" :: "x"(in1), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(out));

	sink = out[0];
	sink = out[1];
	sink = out[2];
	sink = out[3];

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

	in1 = src1;
	res = sqrt(src1);

	asm volatile("" :: "x"(in1), "x"(out));
	begin = perf_begin();
	asm volatile("" :: "x"(in1), "x"(out));

	DO_32(
		out = sqrt(in1);
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	asm volatile("" :: "x"(in1), "x"(out));
	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(out));

	sink = out;

	return end - begin;
}

bench_f BENCH[op_n] = {
	base,
	add_flt,  add_flt4,
	mul_flt,  mul_flt4,
	div_flt,  div_flt4,
	sqrt_flt, sqrt_flt4,
	add_dbl,  add_dbl2,
	mul_dbl,  mul_dbl2,
	div_dbl,  div_dbl2,
	sqrt_dbl
};

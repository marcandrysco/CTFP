#include "bench.h"
#include <float.h>
#include <emmintrin.h>
#include <math.h>
#include <string.h>


/*
 * sources and sinks
 */
volatile double sink, src1, src2;
volatile float sinkf, src1f, src2f;

static inline double m_xor_d(double left, double right)
{
	double out;
	uint64_t v1, v2, v3;

	memcpy(&v1, &left, 8);
	memcpy(&v2, &right, 8);

	v3 = v1 ^ v2;

	memcpy(&out, &v3, 8);

	return out;
}

static inline float m_xor_f(float left, float right)
{
	float out;
	uint32_t v1, v2, v3;

	memcpy(&v1, &left, 4);
	memcpy(&v2, &right, 4);

	v3 = v1 ^ v2;

	memcpy(&out, &v3, 4);

	return out;
}

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

uint32_t f32_add(uint32_t, uint32_t);

static inline float f32_add_i(float f1, float f2)
{
	float f3;
	uint32_t u1, u2, u3;

	memcpy(&u1, &f1, 4);
	memcpy(&u2, &f2, 4);
	f3 = f32_add(u1, u2);
	memcpy(&f3, &u3, 4);

	return f3;
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
 * Multiply doubles.
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
		out = in1 * in2;
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(in2), "x"(out));

	sink = out;

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

static uint32_t mdssz(void)
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

/**
 * Divide double normal/normal=normal benchmark.
 *   &returns: The execution time.
 */
static uint32_t ddnnn(void)
{
	src1 = 1.6; src2 = 2.4;

	return div_dbl();
}

/**
 * Divide double subnormal/normal=subnormal benchmark.
 *   &returns: The execution time.
 */
static uint32_t ddsns(void)
{
	src1 = 1.6e-312; src2 = 2.4;

	return div_dbl();
}

/**
 * Divide double zero/normal=zero benchmark.
 *   &returns: The execution time.
 */
static uint32_t ddznz(void)
{
	src1 = 0.0; src2 = 2.4;

	return div_dbl();
}


/**
 * Divide single normal/normal=normal benchmark.
 *   &returns: The execution time.
 */
static uint32_t dsnnn(void)
{
	src1f = 1.6; src2f = 2.4;

	return div_flt();
}

/**
 * Divide ones.
 *   &returns: The execution time.
 */
static uint32_t ds111(void)
{
	src1f = 0.25; src2f = 256.0;

	return div_flt();
}

/**
 * Divide single subnormal/normal=subnormal benchmark.
 *   &returns: The execution time.
 */
static uint32_t dssns(void)
{
	src1f = 1.6e-42; src2f = 2.4;

	return div_flt();
}

/**
 * Divide single zero/normal=zero benchmark.
 *   &returns: The execution time.
 */
static uint32_t dsznz(void)
{
	src1f = 0.0; src2f = 2.4;

	return div_flt();
}

static uint32_t dsnni(void)
{
	src1f = FLT_MAX * 0.73; src2f = 0.1;

	return div_flt();
}

static uint32_t dsiix(void)
{
	src1f = INFINITY; src2f = INFINITY;

	return div_flt();
}

bench_f BENCH[bench_n] = {
	base,
	adnnn,
	adsss,
	mul_dnnn,
	mdsns,
	mdssz,
	mdnii,
	ddnnn,
	ddsns,
	ddznz,
	dsnnn,
	ds111,
	dssns,
	dsznz,
	dsnni,
	dsiix
};

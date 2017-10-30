#include <stdint.h>
#include "bench.h"
#include <float.h>
#include <emmintrin.h>
#include <math.h>
#include <string.h>



#define DO_32(thing)  thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing \
                      thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing


float drag_sqrt_sp(float x);
double drag_sqrt_dp(double x);

float drag_add_sp(float x, float y);
double drag_add_dp(double x, double y);

float drag_sub_sp(float x, float y);
double drag_sub_dp(double x, double y);

float drag_mul_sp(float x, float y);
double drag_mul_dp(double x, double y);

float drag_div_sp(float x, float y);
double drag_div_dp(double x, double y);

double drag_ext(float x);


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
		out = drag_add_sp(in1, in2);
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
		out = drag_add_dp(in1, in2);
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
		out = drag_mul_sp(in1, in2);
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
		out = drag_mul_dp(in1, in2);
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
		out = drag_div_sp(in1, in2);
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
		out = drag_div_dp(in1, in2);
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
		out = drag_sqrt_sp(in1);
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
		out = drag_sqrt_dp(in1);
		in1 = m_xor_d(m_xor_d(out, res), in1);
	)

	end = perf_end();
	asm volatile("" :: "x"(in1), "x"(out));

	sinkf = out;

	return end - begin;
}

bench_f run_escort[op_n] = {
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



const float k_normal_sp = 1.4f, k_subnormal_sp = 1.4e-40f;
const double k_normal_dp = 1.4, k_subnormal_dp = 2.225e-322;

const double k_ref_dp[2] = { -4.9e-324, 1.7e308 };

__attribute__((always_inline))
double drag_sub_dp(double x, double y) {
    double result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pslldq     $8, %1\n\t"
            "pslldq     $8, %2\n\t"
            "por        %3, %1\n\t"     // %2: { x | k_subnormal }.
            "por        %4, %2\n\t"     // %3: { y | k_normal }.
            "movdqa     %1, %0\n\t"
            "subpd      %2, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_dp), "x" (k_normal_dp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

__attribute__((always_inline))
float drag_sub_sp(float x, float y) {
    float result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pshufd     $0x0f, %1, %1\n\t"
            "pshufd     $0x0f, %2, %2\n\t"
            "pshufd     $0xf0, %3, %%xmm13\n\t"
            "pshufd     $0xf0, %4, %%xmm12\n\t"
            "por        %%xmm13, %1\n\t"
            "por        %%xmm12, %2\n\t"
            "movdqa     %1, %0\n\t"
            "subps      %2, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_sp), "x" (k_normal_sp), "x" (k_ref_dp)
            : "xmm15", "xmm14", "xmm13", "xmm12"
            );

    return result;
}

__attribute__((always_inline))
double drag_add_dp(double x, double y) {
    double result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pslldq     $8, %1\n\t"
            "pslldq     $8, %2\n\t"
            "por        %3, %1\n\t"     // %2: { x | k_subnormal }.
            "por        %4, %2\n\t"     // %3: { y | k_normal }.
            "movdqa     %2, %0\n\t"
            "addpd      %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_dp), "x" (k_normal_dp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

__attribute__((always_inline))
float drag_add_sp(float x, float y) {
    float result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pshufd     $0x0f, %1, %1\n\t"
            "pshufd     $0x0f, %2, %2\n\t"
            "pshufd     $0xf0, %3, %%xmm13\n\t"
            "pshufd     $0xf0, %4, %%xmm12\n\t"
            "por        %%xmm13, %1\n\t"
            "por        %%xmm12, %2\n\t"
            "movdqa     %2, %0\n\t"
            "addps      %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_sp), "x" (k_normal_sp), "x" (k_ref_dp)
            : "xmm15", "xmm14", "xmm13", "xmm12"
            );

    return result;
}

__attribute__((always_inline))
double drag_mul_dp(double x, double y) {
    double result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pslldq     $8, %1\n\t"
            "pslldq     $8, %2\n\t"
            "por        %3, %1\n\t"     // %2: { x | k_subnormal }.
            "por        %4, %2\n\t"     // %3: { y | k_normal }.
            "movdqa     %2, %0\n\t"
            "mulpd      %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_dp), "x" (k_normal_dp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

__attribute__((always_inline))
float drag_mul_sp(float x, float y) {
    float result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pshufd     $0x0f, %1, %1\n\t"
            "pshufd     $0x0f, %2, %2\n\t"
            "pshufd     $0xf0, %3, %%xmm13\n\t"
            "pshufd     $0xf0, %4, %%xmm12\n\t"
            "por        %%xmm13, %1\n\t"
            "por        %%xmm12, %2\n\t"
            "movdqa     %2, %0\n\t"
            "mulps      %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_sp), "x" (k_normal_sp), "x" (k_ref_dp)
            : "xmm15", "xmm14", "xmm13", "xmm12"
            );

    return result;
}

__attribute__((always_inline))
double drag_div_dp(double x, double y) {
    double result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pslldq     $8, %1\n\t"
            "pslldq     $8, %2\n\t"
            "por        %3, %1\n\t"     // %2: { x | k_subnormal }.
            "por        %4, %2\n\t"     // %3: { y | k_normal }.
            "movdqa     %1, %0\n\t"
            "divpd      %2, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_dp), "x" (k_normal_dp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

__attribute__((always_inline))
float drag_sqrt_sp(float x) {
    float result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "pshufd     $0x0f, %1, %1\n\t"
            "pshufd     $0xf0, %2, %%xmm15\n\t"
            "por        %%xmm15, %1\n\t"
            "sqrtps     %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"

            : "=x" (result), "+x" (x)
            : "x" (k_subnormal_sp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

__attribute__((always_inline))
double drag_sqrt_dp(double x) {
    double result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "pslldq     $8, %1\n\t"
            "por        %2, %1\n\t"
            "sqrtpd     %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"

            : "=x" (result), "+x" (x)
            : "x" (k_subnormal_dp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

__attribute__((always_inline))
float drag_div_sp(float x, float y) {
    float result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "movdqa     %2, %%xmm15\n\t"
            "pshufd     $0x0f, %1, %1\n\t"
            "pshufd     $0x0f, %2, %2\n\t"
            "pshufd     $0xf0, %3, %%xmm13\n\t"
            "pshufd     $0xf0, %4, %%xmm12\n\t"
            "por        %%xmm13, %1\n\t"
            "por        %%xmm12, %2\n\t"
            "movdqa     %1, %0\n\t"
            "divps      %2, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"
            "movdqa     %%xmm15, %2\n\t"

            : "=x" (result), "+x" (x), "+x" (y)
            : "x" (k_subnormal_sp), "x" (k_normal_sp), "x" (k_ref_dp)
            : "xmm15", "xmm14", "xmm13", "xmm12"
            );

    return result;
}

__attribute__((always_inline))
double drag_ext(float x) {
    double result;

    __asm__ volatile(
            "movdqa     %1, %%xmm14\n\t"
            "pshufd     $0xf3, %1, %1\n\t"
            "por        %2, %1\n\t"
            "cvtps2pd   %1, %0\n\t"
            "psrldq     $8, %0\n\t"
            "movdqa     %%xmm14, %1\n\t"

            : "=x" (result), "+x" (x)
            : "x" (k_subnormal_sp), "x" (k_ref_dp)
            : "xmm15", "xmm14"
            );

    return result;
}

#ifndef BENCH_H
#define BENCH_H

/*
 * common headers
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>


/**
 * Operation enumerator.
 *   @base_v: Base measurement.
 *   @add_v: Addition.
 *   @sub_v: Subtraction.
 *   @mul_v: Multiplication.
 *   @div_v: Division.
 *   @sqrt_v: Square root.
 */
enum op_e {
	base_v,
	add_v,
	sub_v,
	mul_v,
	div_v,
	sqrt_v,
	op_n
};

/*
 * external declarations
 */
extern volatile double sink, src1, src2;
extern volatile float sinkf, src1f, src2f;


/**
 * Benchmark function.
 *   &returns: The time taken to execute.
 */
typedef uint32_t (*bench_f)(void);

/*
 * benchmark declarations
 */
extern bench_f run_ref[op_n];
extern bench_f run_ctfp1[op_n];
extern bench_f run_ctfp3[op_n];


/**
 * Begin performance tracking.
 *   &returns: The clock count.
 */
static inline uint32_t perf_begin(void)
{
	uint32_t eax, edx;

	asm volatile(
		"rdtsc\n"
		"mov %%eax, %0\n"
		"mov %%edx, %1\n"
		: "=r"(eax), "=r"(edx)
		:
		: "%rax", "%rbx", "%rcx", "%rdx"
	);

	return eax;
}

/**
 * End performance tracking.
 *   &returns: The clock count.
 */
static inline uint32_t perf_end(void)
{
	uint32_t eax, edx;

	asm volatile(
		"rdtsc\n"
		"mov %%eax, %0\n"
		"mov %%edx, %1\n"
		: "=r" (eax), "=r"(edx)
		:
		: "%rax", "%rbx", "%rcx", "%rdx"
	);

	return eax;
}

/**
 * Xor two doubles together.
 *   @left: The left double.
 *   @right: The right double.
 *   &returns: The xored version.
 */
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

/**
 * Xor two floats together.
 *   @left: The left float.
 *   @right: The right float.
 *   &returns: The xored version.
 */
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

#endif

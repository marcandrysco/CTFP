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
	add_f4_v,
	sub_v,
	mul_v,
	mul_f4_v,
	div_v,
	div_f4_v,
	sqrt_v,
	sqrt_f4_v,
	add_dbl_v,
	sub_dbl_v,
	mul_dbl_v,
	div_dbl_v,
	sqrt_dbl_v,
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
extern bench_f run_ctfp2[op_n];
extern bench_f run_escort[op_n];


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

typedef float v2f __attribute__((vector_size(2*sizeof(float))));
typedef float v4f __attribute__((vector_size(4*sizeof(float))));
typedef uint32_t v4i32 __attribute__((vector_size(4*sizeof(uint32_t))));

static inline v4f m_xor_4f(v4f left, v4f right)
{
	v4f out;
	v4i32 v1, v2, v3;

	memcpy(&v1, &left, sizeof(v4f));
	memcpy(&v2, &right, sizeof(v4f));

	v3 = v1 ^ v2;

	memcpy(&out, &v3, sizeof(v4f));

	return out;
}

#define DO_32(thing)  thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing \
                      thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing

#endif

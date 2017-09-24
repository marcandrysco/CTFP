#ifndef COMMON_H
#define COMMON_H

/*
 * common headers
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>


/**
 * Benchmark enumerator.
 *   @bench_base: Base test.
 *   @bench_adnnn: Add double normal*normal=normal.
 *   @bench_adnnn: Add double subnormal*subnormal=subnormal.
 *   @bench_mul_nnn: Multiply normal*normal=normal.
 *   @bench_mul_sns: Multiply subnormal*normal=subnormal.
 *   @bench_mdssz: Multiply double subnormal*subnormal=zero.
 *   @bench_mdnii: Multiply double normal*inf=inf.
 *   @bench_ddnnn: Divide double normal/normal=normal.
 *   @bench_ddsns: Divide double subnormal/normal=subnormal.
 *   @bench_ddznz: Divide double zero/normal=zero.
 *   @bench_dsnnn: Divide single normal/normal=normal.
 *   @bench_dssns: Divide single subnormal/normal=subnormal.
 *   @bench_dsznz: Divide single zero/normal=zero.
 *   @bench_n: The number of benchmarks.
 */
enum bench_e {
	bench_base,
	bench_add_dnnn,
	bench_add_dsss,
	bench_mul_nnn,
	bench_mul_sns,
	bench_mdssz,
	bench_mdnii,
	bench_ddnnn,
	bench_ddsns,
	bench_ddznz,
	bench_dsnnn,
	bench_dssns,
	bench_dsznz,
	bench_n
};

/**
 * Benchmark function.
 *   &returns: The time taken to execute.
 */
typedef uint32_t (*bench_f)(void);

/*
 * benchmark declarations
 */
extern bench_f run_ref[bench_n];
extern bench_f run_ctfp[bench_n];


/**
 * Begin performance tracking.
 *   &returns: The clock count.
 */
static inline uint32_t perf_begin(void)
{
	uint32_t eax, edx;

	asm volatile(
		"rdtscp\n"
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
		"rdtscp\n"
		"mov %%eax, %0\n"
		"mov %%edx, %1\n"
		: "=r" (eax), "=r"(edx)
		:
		: "%rax", "%rbx", "%rcx", "%rdx"
	);

	return eax;
}

/*
 * benchmark declarations
 */
const char *bench_name(enum bench_e bench);

#endif

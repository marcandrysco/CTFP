#ifndef BENCH_H
#define BENCH_H

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
 *   @bench_adsss: Add double subnormal*subnormal=subnormal.
 *   @bench_mdnnn: Multiply normal*normal=normal.
 *   @bench_mdsns: Multiply subnormal*normal=subnormal.
 *   @bench_mdssz: Multiply double subnormal*subnormal=zero.
 *   @bench_mdnii: Multiply double normal*inf=inf.
 *   @bench_ddnnn: Divide double normal/normal=normal.
 *   @bench_ddsns: Divide double subnormal/normal=subnormal.
 *   @bench_ddznz: Divide double zero/normal=zero.
 *   @bench_dsnnn: Divide single normal/normal=normal.
 *   @bench_dssns: Divide single subnormal/normal=subnormal.
 *   @bench_dsznz: Divide single zero/normal=zero.
 *   @bench_dsnni: Divide single normal/normal=infinity.
 *   @bench_n: The number of benchmarks.
 */
enum bench_e {
	bench_base,
	bench_adnnn,
	bench_adsss,
	bench_mdnnn,
	bench_mdsns,
	bench_mdssz,
	bench_mdnii,
	bench_ddnnn,
	bench_ddsns,
	bench_ddznz,
	bench_dsnnn,
	bench_ds111,
	bench_dssns,
	bench_dsznz,
	bench_dsnni,
	bench_dsiix,
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
extern bench_f run_ctfp1[bench_n];
extern bench_f run_ctfp3[bench_n];


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
enum bench_e bench_cmp(enum bench_e bench);

#endif

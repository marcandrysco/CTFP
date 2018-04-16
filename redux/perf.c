#define _GNU_SOURCE
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <float.h>
#include <time.h>
#include <stdlib.h>
#include <stdint.h>
#include <sched.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
#include <sys/resource.h>


/*
 * bench declarations
 */
typedef uint32_t (*bench_f)(void);

extern bench_f ref[2][5], ctfp1[2][5], ctfp2[2][5];

volatile float src1f32, src2f32, sinkf32;
volatile double src1f64, src2f64, sinkf64;

/*
 * ctfp declarations
 */
float ctfp_restrict_add(float, float);
float ctfp_restrict_sub(float, float);
float ctfp_restrict_mul(float, float);
float ctfp_restrict_div(float, float);
float ctfp_full_add(float, float);
float ctfp_full_sub(float, float);
float ctfp_full_mul(float, float);
float ctfp_full_div(float, float);

/*
 * local declarations
 */
static void perf_init(void);
static void perf_micro(void);
static void perf_timing(void);


/**
 * Main entry point.
 *   @argc: The argument count.
 *   @argv: The argument array.
 *   &returns: Exit status.
 */
int main(int argc, char **argv)
{
	setbuf(stdout, NULL);
	setbuf(stderr, NULL);

	perf_init();
	if(1) perf_micro();
	if(0) perf_timing();

	return 0;
}



#define BASE (0)
#define ADD  (1)
#define MUL  (2)
#define DIV  (3)
#define SQRT (4)
#define NOPS (5)

#define FLT    (0)
#define DBL    (1)
#define NSIZES (2)


static int run_cmp(const void *p1, const void *p2)
{
	uint32_t v1 = *(const uint32_t *)p1, v2 = *(const uint32_t *)p2;

	if(v1 < v2)
		return -1;
	else if(v1 > v2)
		return 1;
	else
		return 0;
}

/**
 * Create a set of runs.
 *   @len: The length.
 *   &returns: The set.
 */
uint32_t *run_new(uint32_t len)
{
	uint32_t *runs;

	runs = malloc(len * sizeof(uint32_t));

	return runs;
}

/**
 * Compute the average of a run.
 *   @run: The run.
 *   @len: The length.
 */
float run_ave(uint32_t *run, uint32_t len)
{
	unsigned int i;
	uint32_t sum = 0;

	qsort(run, len, sizeof(uint32_t), run_cmp);

	for(i = len / 4; i < (len - len / 4); i++)
		sum += run[i];

	return sum / (float)(len / 2);
}

/**
 * Delete a set of runs.
 *   @run: The set.
 */
void run_delete(uint32_t *run)
{
	free(run);
}


/**
 * Initialize the perf tool, spinning up the processor.
 */
static void perf_init(void)
{
	int ret;
	uint32_t i;
	struct sched_param param;
	static float sinkf = 0.2;

	cpu_set_t set;
	CPU_ZERO(&set);
	CPU_SET(0, &set);

	ret = setpriority(PRIO_PROCESS, getpid(), -20);
	if(ret != 0)
		fprintf(stderr, "Unable to set nice. %s.\n", strerror(errno));

	param.sched_priority = 99;
	ret = sched_setscheduler(0, SCHED_FIFO, &param);
	if(ret < 0)
		fprintf(stderr, "Unable to set scheduler. %s.\n", strerror(errno));

	ret = sched_setaffinity(0, sizeof(set), &set);
	if(ret < 0)
		fprintf(stderr, "Unable to set affinity. %s.\n", strerror(errno));

	for(i = 0; i < 10000000; i++)
		sinkf = sqrt(0.1 - sinkf);
}

float run_exec(uint32_t *run, uint32_t n, bench_f func)
{
	uint32_t i;

	for(i = 0; i < n; i++)
		run[i] = func();

	return run_ave(run, n);
}

/**
 * Microbenchmark performance.
 */
static void perf_micro(void)
{
	uint32_t k, n, *run;
	float ref32[NOPS], sub32[NOPS], rest32[NOPS], full32[NOPS];
	float ref64[NOPS], sub64[NOPS], rest64[NOPS], full64[NOPS];

	n = 100000;

	run = run_new(n);

	for(k = 0; k < NOPS; k++) {
		src1f32 = 1.0f; src2f32 = 1.2f;
		ref32[k] = run_exec(run, n, ref[0][k]);
		rest32[k] = run_exec(run, n, ctfp1[0][k]);
		full32[k] = run_exec(run, n, ctfp2[0][k]);

		src1f32 = FLT_MIN/2; src2f32 = 1.2;
		sub32[k] = run_exec(run, n, ref[0][k]);

		src1f64 = 1.0; src2f64 = 1.2;
		ref64[k] = run_exec(run, n, ref[1][k]);
		rest64[k] = run_exec(run, n, ctfp1[1][k]);
		full64[k] = run_exec(run, n, ctfp2[1][k]);

		src1f64 = DBL_MIN/2; src2f64 = 1.2;
		sub64[k] = run_exec(run, n, ref[1][k]);
	}

	for(k = 0; k < NOPS; k++) {
		printf("%d: %8.3f %8.3f  ", k, ref32[k], rest32[k]);
		printf("%5.2f   ", (rest32[k] - 30) / (ref32[k] - 30));
		printf("%9.3f  ", full32[k]);
		printf("%5.2f   ", (full32[k] - 30) / (ref32[k] - 30));
		printf("%9.3f  ", sub32[k]);
		printf("%5.2f   ", (sub32[k] - 30) / (ref32[k] - 30));
		printf("\n");
	}

	printf("\n");

	for(k = 0; k < NOPS; k++) {
		printf("%d: %8.3f %8.3f  ", k, ref64[k], rest64[k]);
		printf("%5.2f   ", (rest64[k] - 30) / (ref64[k] - 30));
		printf("%9.3f  ", full64[k]);
		printf("%5.2f   ", (full64[k] - 30) / (ref64[k] - 30));
		printf("%9.3f  ", sub64[k]);
		printf("%5.2f   ", (sub64[k] - 30) / (ref64[k] - 30));
		printf("\n");
	}

	run_delete(run);
}

float flts[] = {
	1.4f, 1.0f, 2.0f, 256.0f, 512.0f, 1.2e-18f, 1.2e-20f, 1.2e-37f, 1.2e-40f, INFINITY, NAN, 0.0f
};

#define ARRSIZE(arr) (sizeof(arr) / sizeof(arr[0]))

/**
 * Timing benchmarks.
 */
static void perf_timing(void)
{
	uint32_t i, j, k, n, *run;
	float ave, base;

	//n = 100000;
	n = 10000;

	run = run_new(n);

	base = run_ave(run, n);

	for(i = 0; i < ARRSIZE(flts); i++) {
		for(j = 0; j < ARRSIZE(flts); j++) {
			src1f32 = flts[i]; src2f32 = flts[j];
			for(k = 0; k < n; k++)
				run[k] = ref[0][2]();

			ave = run_ave(run, n);
			if((i == 0) && (j == 0))
				base = ave;

			printf("%7.2f (%7.4f) ", ave, ave / base);
		}
		printf("\n");
	}

	run_delete(run);
}

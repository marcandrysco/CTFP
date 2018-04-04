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
	perf_micro();

	return 0;
}



#define BASE (0)
#define ADD  (1)
#define MUL  (2)
#define DIV  (3)
#define SQRT (4)
#define NOPS (5)

#define REF   (0)
#define REST  (1)
#define FULL  (2)
#define NCFGS (3)

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

/**
 * Microbenchmark performance.
 */
static void perf_micro(void)
{
	uint32_t i, k, n;
	uint32_t *ref32[NOPS], *rest32[NOPS], *full32[NOPS];

	n = 100000;

	for(i = 0; i < NOPS; i++) {
		ref32[i] = run_new(n);
		rest32[i] = run_new(n);
		full32[i] = run_new(n);
	}

	for(k = 0; k < 4/*NOPS*/; k++) {
		for(i = 0; i < n; i++) {
			src1f32=1.0; src2f32=1.2;
			ref32[k][i] = ref[0][k]();
			rest32[k][i] = ctfp1[0][k]();
			full32[k][i] = ctfp2[0][k]();
		}
	}

	for(k = 0; k < 4/*NOPS*/; k++) {
		printf("%d: %8.3f %8.3f  ", k, run_ave(ref32[k], n), run_ave(rest32[k], n));
		printf("%5.2f   ", (run_ave(rest32[k], n) - 30) / (run_ave(ref32[k], n) - 30));
		printf("%9.3f  ", run_ave(full32[k], n));
		printf("%5.2f   ", (run_ave(full32[k], n) - 30) / (run_ave(ref32[k], n) - 30));
		printf("\n");
	}

	for(i = 0; i < NOPS; i++) {
		run_delete(ref32[i]);
		run_delete(rest32[i]);
		run_delete(full32[i]);
	}
	//printf("%d\n", ref[0]());
	//printf("%d\n", ref[2]());

	//printf("%d\n", ctfp1[0]());
	//printf("%d\n", ctfp1[2]());
}

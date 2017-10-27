#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <sched.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>
#include <math.h>
#include <sched.h>
#include <float.h>

#include "bench.h"
#define CNT (400000)
#define NVAL (12)


volatile double sink, src1, src2;
volatile float sinkf, src1f, src2f;


static int cmpnum(const void *p1, const void *p2)
{
	uint32_t v1 = *(const uint32_t *)p1, v2 = *(const uint32_t *)p2;

	if(v1 < v2)
		return -1;
	else if(v1 > v2)
		return 1;
	else
		return 0;
}

static float average(uint32_t *run)
{
	unsigned int i;
	uint32_t sum = 0;

	qsort(run, CNT, sizeof(uint32_t), cmpnum);

	for(i = CNT / 4; i < (CNT - CNT / 4); i++)
		sum += run[i];

	return sum / (float)(CNT / 2);
}

/*
 * local variables
 */
static float in_flt[NVAL] = {
	1.4f, 1.0f, 2.0f, 256.0f, 512.0f, 1.2e-18, 1.2e-20, 1.2e-38, 1.2e-40, INFINITY, NAN, 0.0f
};

static bench_f *run_all[3] = { run_ref, run_ctfp1, run_ctfp3 };
const char *run_name[3] = { "ref", "ctfp1", "ctfp2" };


/**
 * Run a single benchmark.
 *   @ver: The version (0 is reference).
 *   @op: The operations.
 *   @n: The number of iterations.
 *   &returns: The average time length.
 */
float run_bench(uint8_t ver, uint8_t op, unsigned int n, ...)
{
	float sum;
	uint32_t *run;
	unsigned int i;
	va_list args;

	assert((ver < 3) && (op < op_n));

	va_start(args, n);
	src1f = src1 = va_arg(args, double);
	src2f = src2 = va_arg(args, double);
	va_end(args);

	run = malloc(n * sizeof(uint32_t));

	for(i = 0; i < n; i++)
		run[i] = run_all[ver][op]();

	sum = 0.0f;
	qsort(run, n, sizeof(uint32_t), cmpnum);

	for(i = n / 4; i < (n - n / 4); i++)
		sum += run[i];

	free(run);

	return sum / (float)(n / 2);
}


/**
 * Report a test of ratios.
 *   @name: The test name.
 *   @ratio: The ratio compared to the reference.
 */
void report_ratio(const char *name, float ratio)
{
	printf("%s %s %.2f\n", name, ((ratio > 1.1) || (ratio < 0.9)) ? "Y" : "N", ratio);
}

void report_time(float run, float ref)
{
	printf("%.3f ", run / ref);
}


/**
 * Main entry point.
 *   @argc: The number of arguments.
 *   @argv: The argument array.
 *   &returns: The exit status.
 */
int main(int argc, char **argv)
{
	int ret;
	bool bad;
	uint32_t *run;
	float base, ref, ave;
	unsigned int i, n, x, y;

	//setvbuf(stdout, NULL, _IOLBF, BUFSIZ);
	setbuf(stdout, NULL);

	struct sched_param param;

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

	{
		sinkf = 0.2;

		for(i = 0; i < 10000000; i++)
			sinkf = sqrt(0.1 - sinkf);
	}

	base = run_bench(0, base_v, 100000, 1.4, 2.2);
	printf("base    %.4f\n", base);

	if(0) {
	ref = run_bench(0, add_v, 100000, 1.4, 2.2) - base;
	report_ratio("add  flt sub ", (run_bench(0, add_v, 100000, 1.4, 2.3e-40) - base) / ref);
	report_ratio("add  flt inf ", (run_bench(0, add_v, 100000, 1.4, INFINITY) - base) / ref);
	report_ratio("add  flt zero", (run_bench(0, add_v, 100000, 1.4, 0.0) - base) / ref);

	ref = run_bench(0, mul_v, 100000, 1.4, 2.2) - base;
	report_ratio("mul  flt sub ", (run_bench(0, mul_v, 100000, 1.4, 2.3e-40) - base) / ref);
	report_ratio("mul  flt inf ", (run_bench(0, mul_v, 100000, 1.4, INFINITY) - base) / ref);
	report_ratio("mul  flt zero", (run_bench(0, mul_v, 100000, 1.4, 0.0) - base) / ref);

	ref = run_bench(0, div_v, 100000, 1.4, 2.2) - base;
	report_ratio("div  flt sub ", (run_bench(0, div_v, 100000, 1.4, 2.3e-40) - base) / ref);
	report_ratio("div  flt inf ", (run_bench(0, div_v, 100000, 1.4, INFINITY) - base) / ref);
	report_ratio("div  flt zero", (run_bench(0, div_v, 100000, 1.4, 0.0) - base) / ref);
	report_ratio("div  flt pow2", (run_bench(0, div_v, 100000, 1.4, 128.0) - base) / ref);
	report_ratio("div  flt pow4", (run_bench(0, div_v, 100000, 1.4, 256.0) - base) / ref);

	ref = run_bench(0, sqrt_v, 100000, 1.4) - base;
	report_ratio("sqrt flt sub ", (run_bench(0, sqrt_v, 100000, 2.3e-40) - base) / ref);
	report_ratio("sqrt flt inf ", (run_bench(0, sqrt_v, 100000, INFINITY) - base) / ref);
	report_ratio("sqrt flt zero", (run_bench(0, sqrt_v, 100000, 0.0) - base) / ref);
	report_ratio("sqrt flt pow2", (run_bench(0, sqrt_v, 100000, 128.0) - base) / ref);
	report_ratio("sqrt flt pow4", (run_bench(0, sqrt_v, 100000, 256.0) - base) / ref);
	}

	printf("\n");

	for(n = 0; n < 3; n++) {
		printf("div %s\n", run_name[n]);

		ref = run_bench(n, div_v, 100000, 1.4) - base;
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++)
				report_time(run_bench(n, div_v, 100000, in_flt[x], in_flt[y]) - base, ref);

			printf("\n");
		}

		printf("\n");
	}

	for(n = 0; n < 3; n++) {
		printf("sqrt %s\n", run_name[n]);

		ref = run_bench(n, sqrt_v, 100000, 1.4) - base;
		for(x = 0; x < NVAL; x++)
			report_time(run_bench(n, sqrt_v, 100000, in_flt[x]) - base, ref);

		printf("\n\n");
	}

	return 0;

	run = malloc(CNT * sizeof(uint32_t));

	if(0) {
		src1f = in_flt[0];
		src2f = in_flt[0];
		for(i = 0; i < CNT; i++)
			run[i] = run_ctfp3[div_v]();
		ave = average(run);
		printf("%.3f  %.2e %.2e\n", ave, src1f, src2f);

		src1f = in_flt[0];
		src2f = in_flt[6];
		for(i = 0; i < CNT; i++)
			run[i] = run_ctfp3[div_v]();
		ave = average(run);
		printf("%.3f  %.2e %.2e\n", ave, src1f, src2f);

		exit(0);
	}

	for(i = 0; i < CNT; i++)
		run[i] = run_ref[base_v]();

	base = average(run);

	printf("base    %.4f\n", base);

	src1f = 1.4;
	src2f = 2.3;

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][add_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("add %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][mul_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("mul %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][div_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("div %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][sqrt_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("sqrt %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		printf("add %s\n", run_name[n]);
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++) {
				src1f = in_flt[x]; src2f = in_flt[y];

				for(i = 0; i < CNT; i++)
					run[i] = run_all[n][add_v]();

				ave = average(run) - base;
				if((x == 0) && (y == 0))
					ref = ave;

				bad = fabsf((ave - ref) / ref) > 0.05;
				printf("\x1b[%dm%6.3f  \x1b[0m", bad ? 7 : 0, ave / ref);
			}
			
			printf("\n");
		}
	}

	for(n = 0; n < 3; n++) {
		printf("mul %s\n", run_name[n]);
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++) {
				src1f = in_flt[x]; src2f = in_flt[y];

				for(i = 0; i < CNT; i++)
					run[i] = run_all[n][mul_v]();

				ave = average(run) - base;
				if((x == 0) && (y == 0))
					ref = ave;

				bad = fabsf((ave - ref) / ref) > 0.05;
				printf("\x1b[%dm%6.3f  \x1b[0m", bad ? 7 : 0, ave / ref);
			}
			
			printf("\n");
		}
	}

	for(n = 0; n < 3; n++) {
		printf("div %s\n", run_name[n]);
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++) {
				src1f = in_flt[x]; src2f = in_flt[y];

				for(i = 0; i < CNT; i++)
					run[i] = run_all[n][div_v]();

				ave = average(run) - base;
				if((x == 0) && (y == 0))
					ref = ave;

				bad = fabsf((ave - ref) / ref) > 0.05;
				printf("\x1b[%dm%6.3f  \x1b[0m", bad ? 7 : 0, ave / ref);
			}
			
			printf("\n");
		}
	}

	for(n = 0; n < 3; n++) {
		printf("sqrt %s\n", run_name[n]);
		for(x = 0; x < NVAL; x++) {
			src1f = in_flt[x];

			for(i = 0; i < CNT; i++)
				run[i] = run_all[n][sqrt_v]();

			ave = average(run) - base;
			if(x == 0)
				ref = ave;

			bad = fabsf((ave - ref) / ref) > 0.05;
			printf("\x1b[%dm%6.3f  \x1b[0m", bad ? 7 : 0, ave / ref);
		}
		printf("\n");
	}

	free(run);

	return 0;
}

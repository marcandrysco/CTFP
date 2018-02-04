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
#define CNT (1000000)
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
	1.4f, 1.0f, 2.0f, 256.0f, 512.0f, 1.2e-18f, 1.2e-20f, 1.2e-37f, 1.2e-40f, INFINITY, NAN, 0.0f
};
static float in_dbl[NVAL] = {
	1.4, 1.0, 2.0, 256.0, 512.0, 1.2e-18, 1.2e-20, 1.2e-307, 1.2e-320, INFINITY, NAN, 0.0
};

static bench_f *run_all[4] = { run_ref, run_ctfp1, run_ctfp2, run_escort };
const char *run_name[4] = { "ref", "ctfp1", "ctfp2", "escort" };


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

	assert((ver < 4) && (op < op_n));

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
	printf("%s %s %.3f\n", name, ((ratio > 1.05) || (ratio < 0.95)) ? "Y" : "N", ratio);
}

/**
 * Report performance .
 *   @name: The test name.
 *   @ratio: The ratio compared to the reference.
 */
void report_perf(const char *name, float run, float ref)
{
	printf("%s %7.3f %6.3f\n", name, run / 32.0f, run / ref);
}

void report_time(float run, float ref)
{
	printf("%7.3f ", run / ref);
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

	base = run_bench(0, base_v, CNT, 1.4, 2.2);
	printf("base    %.4f\n", base);

	//ref = run_bench(0, mul_d1_v, CNT, 1.4, 2.2) - base;
	//report_perf("ctfp1  div ", (run_bench(1, div_d1_v, CNT, 1.4, 2.2) - base), ref);
	//report_perf("ctfp2  div ", (run_bench(2, div_d1_v, CNT, 1.4, 2.2) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 1.4, 2.2) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 1.4, 0.0) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 1.4, 2.3e-310) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 2.3e-310, 2.3e-310) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 1.4, INFINITY) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 1.4, NAN) - base), ref);
	//printf("\n");

	if(1) {
	ref = run_bench(0, add_f1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  add  ", (run_bench(1, add_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp1  add4 ", (run_bench(1, add_f4_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp2  add  ", (run_bench(2, add_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp2  add4 ", (run_bench(2, add_f4_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("snorm  add  ", (run_bench(0, add_f1_v, CNT, 1.4, 2.3e-40) - base), ref);

	ref = run_bench(0, mul_f1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  mul  ", (run_bench(1, mul_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp1  mul4 ", (run_bench(1, mul_f4_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp2  mul  ", (run_bench(2, mul_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp2  mul4 ", (run_bench(2, mul_f4_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("snorm  mul  ", (run_bench(0, mul_f1_v, CNT, 1.4, 2.3e-40) - base), ref);

	ref = run_bench(0, div_f1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  div  ", (run_bench(1, div_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp1  div4 ", (run_bench(1, div_f4_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp2  div  ", (run_bench(2, div_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("ctfp2  div4 ", (run_bench(2, div_f4_v, CNT, 1.4, 2.3e-40) - base), ref);
	report_perf("snorm  div  ", (run_bench(0, div_f1_v, CNT, 1.4, 2.3e-40) - base), ref);

	ref = run_bench(0, sqrt_f1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  sqrt ", (run_bench(1, sqrt_f1_v, CNT, 2.3e-40) - base), ref);
	report_perf("ctfp1  sqrt4", (run_bench(1, sqrt_f4_v, CNT, 2.3e-40) - base), ref);
	report_perf("ctfp2  sqrt ", (run_bench(2, sqrt_f1_v, CNT, 2.3e-40) - base), ref);
	report_perf("ctfp2  sqrt4", (run_bench(2, sqrt_f4_v, CNT, 2.3e-40) - base), ref);
	report_perf("snorm  sqrt ", (run_bench(0, sqrt_f1_v, CNT, 2.3e-40) - base), ref);

	ref = run_bench(0, add_d1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  add  ", (run_bench(1, add_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp1  add2 ", (run_bench(1, add_d2_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp2  add  ", (run_bench(2, add_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp2  add2 ", (run_bench(2, add_d2_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("snorm  add  ", (run_bench(0, add_d1_v, CNT, 1.4, 2.3e-320) - base), ref);

	ref = run_bench(0, mul_d1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  mul  ", (run_bench(1, mul_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp1  mul2 ", (run_bench(1, mul_d2_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp2  mul  ", (run_bench(2, mul_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp2  mul2 ", (run_bench(2, mul_d2_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("snorm  mul  ", (run_bench(0, mul_d1_v, CNT, 1.4, 2.3e-320) - base), ref);

	ref = run_bench(0, div_d1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  div  ", (run_bench(1, div_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp1  div2 ", (run_bench(1, div_d2_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp2  div  ", (run_bench(2, div_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("ctfp2  div2 ", (run_bench(2, div_d2_v, CNT, 1.4, 2.3e-320) - base), ref);
	report_perf("snorm  div  ", (run_bench(0, div_d1_v, CNT, 1.4, 2.3e-320) - base), ref);

	ref = run_bench(0, sqrt_d1_v, CNT, 1.4, 2.2) - base;
	report_perf("ctfp1  sqrt ", (run_bench(1, sqrt_d1_v, CNT, 2.3e-320) - base), ref);
	report_perf("ctfp1  sqrt2", (run_bench(1, sqrt_d2_v, CNT, 2.3e-320) - base), ref);
	report_perf("ctfp2  sqrt ", (run_bench(2, sqrt_d1_v, CNT, 2.3e-320) - base), ref);
	report_perf("ctfp2  sqrt2", (run_bench(2, sqrt_d2_v, CNT, 2.3e-320) - base), ref);
	report_perf("snorm  sqrt ", (run_bench(0, sqrt_d1_v, CNT, 2.3e-320) - base), ref);

	//report_perf("escort add ", (run_bench(3, add_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	//report_perf("escort mul ", (run_bench(3, mul_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_f1_v, CNT, 1.4, 2.3e-40) - base), ref);
	//report_perf("escort sqrt ", (run_bench(3, sqrt_f1_v, CNT, 2.3e-40) - base), ref);
	//report_perf("escort add ", (run_bench(3, add_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	//report_perf("escort mul ", (run_bench(3, mul_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	//report_perf("escort div ", (run_bench(3, div_d1_v, CNT, 1.4, 2.3e-320) - base), ref);
	//report_perf("escort sqrt ", (run_bench(3, sqrt_d1_v, CNT, 2.3e-320) - base), ref);

	return 0;
	}
	
	for(n = 0; n < 3; n++) {
		printf("div flt %s\n", run_name[n]);

		ref = run_bench(n, div_f1_v, CNT, 1.4, 1.4) - base;
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++)
				report_time(run_bench(n, div_f1_v, CNT, in_flt[y], in_flt[x]) - base, ref);

			printf("\n");
		}

		printf("\n");
	}

	if(1) {
	ref = run_bench(0, add_f1_v, CNT, 1.4, 2.2) - base;
	report_ratio("add  flt sub ", (run_bench(0, add_f1_v, CNT, 1.4, 2.3e-40) - base) / ref);
	report_ratio("add  flt inf ", (run_bench(0, add_f1_v, CNT, 1.4, INFINITY) - base) / ref);
	report_ratio("add  flt zero", (run_bench(0, add_f1_v, CNT, 1.4, 0.0) - base) / ref);

	ref = run_bench(0, mul_f1_v, CNT, 1.4, 2.2) - base;
	report_ratio("mul  flt sub ", (run_bench(0, mul_f1_v, CNT, 1.4, 2.3e-40) - base) / ref);
	report_ratio("mul  flt inf ", (run_bench(0, mul_f1_v, CNT, 1.4, INFINITY) - base) / ref);
	report_ratio("mul  flt zero", (run_bench(0, mul_f1_v, CNT, 1.4, 0.0) - base) / ref);

	ref = run_bench(0, div_f1_v, CNT, 1.4, 2.2) - base;
	report_ratio("div  flt sub ", (run_bench(0, div_f1_v, CNT, 1.4, 2.3e-40) - base) / ref);
	report_ratio("div  flt inf ", (run_bench(0, div_f1_v, CNT, 1.4, INFINITY) - base) / ref);
	report_ratio("div  flt zero", (run_bench(0, div_f1_v, CNT, 1.4, 0.0) - base) / ref);
	report_ratio("div  flt pow2", (run_bench(0, div_f1_v, CNT, 1.4, 128.0) - base) / ref);
	report_ratio("div  flt pow4", (run_bench(0, div_f1_v, CNT, 1.4, 256.0) - base) / ref);

	ref = run_bench(0, sqrt_f1_v, CNT, 1.4) - base;
	report_ratio("sqrt flt sub ", (run_bench(0, sqrt_f1_v, CNT, 2.3e-40) - base) / ref);
	report_ratio("sqrt flt inf ", (run_bench(0, sqrt_f1_v, CNT, INFINITY) - base) / ref);
	report_ratio("sqrt flt zero", (run_bench(0, sqrt_f1_v, CNT, 0.0) - base) / ref);
	report_ratio("sqrt flt pow2", (run_bench(0, sqrt_f1_v, CNT, 128.0) - base) / ref);
	report_ratio("sqrt flt pow4", (run_bench(0, sqrt_f1_v, CNT, 256.0) - base) / ref);
	report_ratio("sqrt flt neg ", (run_bench(0, sqrt_f1_v, CNT, -1.2) - base) / ref);

	ref = run_bench(0, add_d1_v, CNT, 1.4, 2.2) - base;
	report_ratio("add  dbl sub ", (run_bench(0, add_d1_v, CNT, 1.4, 2.3e-310) - base) / ref);
	report_ratio("add  dbl inf ", (run_bench(0, add_d1_v, CNT, 1.4, INFINITY) - base) / ref);
	report_ratio("add  dbl zero", (run_bench(0, add_d1_v, CNT, 1.4, 0.0) - base) / ref);

	ref = run_bench(0, mul_d1_v, CNT, 1.4, 2.2) - base;
	report_ratio("mul  dbl sub ", (run_bench(0, mul_d1_v, CNT, 2.3e-310, 1.4) - base) / ref);
	report_ratio("mul  dbl inf ", (run_bench(0, mul_d1_v, CNT, 1.4, INFINITY) - base) / ref);
	report_ratio("mul  dbl zero", (run_bench(0, mul_d1_v, CNT, 1.4, 0.0) - base) / ref);

	ref = run_bench(0, div_d1_v, CNT, 1.4, 2.2) - base;
	report_ratio("div  dbl sub ", (run_bench(0, div_d1_v, CNT, 1.4, 2.3e-310) - base) / ref);
	report_ratio("div  dbl inf ", (run_bench(0, div_d1_v, CNT, 1.4, INFINITY) - base) / ref);
	report_ratio("div  dbl zero", (run_bench(0, div_d1_v, CNT, 1.4, 0.0) - base) / ref);
	report_ratio("div  dbl pow2", (run_bench(0, div_d1_v, CNT, 1.4, 128.0) - base) / ref);
	report_ratio("div  dbl pow4", (run_bench(0, div_d1_v, CNT, 1.4, 256.0) - base) / ref);

	ref = run_bench(0, sqrt_d1_v, CNT, 1.4) - base;
	report_ratio("sqrt dbl sub ", (run_bench(0, sqrt_d1_v, CNT, 2.3e-310) - base) / ref);
	report_ratio("sqrt dbl inf ", (run_bench(0, sqrt_d1_v, CNT, INFINITY) - base) / ref);
	report_ratio("sqrt dbl zero", (run_bench(0, sqrt_d1_v, CNT, 0.0) - base) / ref);
	report_ratio("sqrt dbl pow2", (run_bench(0, sqrt_d1_v, CNT, 128.0) - base) / ref);
	report_ratio("sqrt dbl pow4", (run_bench(0, sqrt_d1_v, CNT, 256.0) - base) / ref);
	report_ratio("sqrt dbl neg ", (run_bench(0, sqrt_d1_v, CNT, -1.2) - base) / ref);

	printf("\n");

	return 0;
	}

	if(0)
	for(n = 0; n < 3; n++) {
		printf("div flt %s\n", run_name[n]);

		ref = run_bench(n, div_f1_v, CNT, 1.4) - base;
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++)
				report_time(run_bench(n, div_f1_v, CNT, in_flt[x], in_flt[y]) - base, ref);

			printf("\n");
		}

		printf("\n");
	}

	if(0)
	for(n = 0; n < 3; n++) {
		printf("sqrt flt %s\n", run_name[n]);

		ref = run_bench(n, sqrt_f1_v, CNT, 1.4) - base;
		for(x = 0; x < NVAL; x++)
			report_time(run_bench(n, sqrt_f1_v, CNT, in_flt[x]) - base, ref);

		printf("\n\n");
	}

	for(n = 0; n < 3; n++) {
		printf("div dbl %s\n", run_name[n]);

		ref = run_bench(n, div_d1_v, CNT, 1.4) - base;
		for(x = 0; x < NVAL; x++) {
			for(y = 0; y < NVAL; y++)
				report_time(run_bench(n, div_d1_v, CNT, in_dbl[x], in_dbl[y]) - base, ref);

			printf("\n");
		}

		printf("\n");
	}

	for(n = 0; n < 3; n++) {
		printf("sqrt dbl %s\n", run_name[n]);

		ref = run_bench(n, sqrt_d1_v, CNT, 1.4) - base;
		for(x = 0; x < NVAL; x++)
			report_time(run_bench(n, sqrt_d1_v, CNT, in_dbl[x]) - base, ref);

		printf("\n\n");
	}

	return 0;

	run = malloc(CNT * sizeof(uint32_t));

	if(0) {
		src1f = in_flt[0];
		src2f = in_flt[0];
		for(i = 0; i < CNT; i++)
			run[i] = run_ctfp2[div_f1_v]();
		ave = average(run);
		printf("%.3f  %.2e %.2e\n", ave, src1f, src2f);

		src1f = in_flt[0];
		src2f = in_flt[6];
		for(i = 0; i < CNT; i++)
			run[i] = run_ctfp2[div_f1_v]();
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
			run[i] = run_all[n][add_f1_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("add %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][mul_f1_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("mul %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][div_f1_v]();

		ave = average(run) - base;
		if(n == 0)
			ref = ave;

		printf("div %-5s  %.3f  %.3f\n", run_name[n], ave, ave / ref);
	}

	for(n = 0; n < 3; n++) {
		for(i = 0; i < CNT; i++)
			run[i] = run_all[n][sqrt_f1_v]();

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
					run[i] = run_all[n][add_f1_v]();

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
					run[i] = run_all[n][mul_f1_v]();

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
					run[i] = run_all[n][div_f1_v]();

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
				run[i] = run_all[n][sqrt_f1_v]();

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

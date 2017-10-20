#define _GNU_SOURCE
#include <errno.h>
#include <sched.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>


void getout_f1(float f)
{
}

void getout_d1(double d)
{
}

#include "bench.h"


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

struct bench_t {
	uint32_t *run[bench_n];
	double ave[bench_n], var[bench_n];
};

int main(int argc, char **argv)
{
	unsigned int cnt = 50000; //100000;

	cpu_set_t set;
	CPU_ZERO(&set);
	CPU_SET(0, &set);

	int ret = sched_setaffinity(0, sizeof(set), &set);
	if(ret < 0)
		fprintf(stderr, "Unable to set affinity. %s.\n", strerror(errno));

	unsigned int i, n, sel;
	struct bench_t ref, ctfp1, ctfp2;

	for(i = 0; i < bench_n; i++) {
		ref.run[i] = malloc(cnt * sizeof(uint32_t));
		ctfp1.run[i] = malloc(cnt * sizeof(uint32_t));
		ctfp2.run[i] = malloc(cnt * sizeof(uint32_t));
	}

		for(i = 0; i < bench_n; i++) {
	for(n = 0; n < cnt; n++) {
			sel = i;//(i + n) % bench_n;
			ref.run[sel][n] = run_ref[sel]();
			ctfp1.run[sel][n] = run_ctfp1[sel]();
			ctfp2.run[sel][n] = run_ctfp3[sel]();
		}
	}

	for(i = 0; i < bench_n; i++) {
		qsort(ref.run[i], cnt, sizeof(uint32_t), cmpnum);
		qsort(ctfp1.run[i], cnt, sizeof(uint32_t), cmpnum);
		qsort(ctfp2.run[i], cnt, sizeof(uint32_t), cmpnum);

		ref.ave[i] = 0.0;
		ctfp1.ave[i] = 0.0;
		ctfp2.ave[i] = 0.0;

		for(n = cnt / 4; n < (cnt - cnt / 4); n++) {
			ref.ave[i] += ref.run[i][n];
			ctfp1.ave[i] += ctfp1.run[i][n];
			ctfp2.ave[i] += ctfp2.run[i][n];
		}

		ref.ave[i] /= (cnt / 2);
		ctfp1.ave[i] /= (cnt / 2);
		ctfp2.ave[i] /= (cnt / 2);

		enum bench_e cmp = bench_cmp(i);
		printf("%s  ", bench_name(i));
		printf("%6.3f (%8.3f)  ", (ref.ave[i] - ref.ave[0]) / (ref.ave[cmp] - ref.ave[0]), ref.ave[i]);
		printf("%6.3f (%8.3f)  ", (ctfp1.ave[i] - ctfp1.ave[0]) / (ctfp1.ave[cmp] - ctfp1.ave[0]), ctfp1.ave[i]);
		printf("%6.3f (%8.3f)  ", (ctfp2.ave[i] - ctfp2.ave[0]) / (ctfp2.ave[cmp] - ctfp2.ave[0]), ctfp2.ave[i]);
		printf("\n");
	}

	for(i = 0; i < bench_n; i++) {
		free(ref.run[i]);
		free(ctfp1.run[i]);
	}

	return 0;
}

volatile double src0, src1, dest0;

void foo()
{
	double a, b, c;

	src0 = 1.2;
	src1 = 2.3;

	a = src0;
	b = src1;

	asm volatile("" :: "x"(a), "x"(b), "x"(c));
	c = a * b;
	asm volatile("" :: "x"(a), "x"(b), "x"(c));

	dest0 = c;
}


/**
 * Retrieve the benchmark name.
 *   @bench: The benchmark.
 *   &returns: The name.
 */
const char *bench_name(enum bench_e bench)
{
	switch(bench) {
	case bench_base: return "base         ";
	case bench_adnnn: return "add dbl n+n=n";
	case bench_adsss: return "add dbl s+s=s";
	case bench_mdnnn: return "mul dbl n*n=n";
	case bench_mdsns: return "mul dbl s*n=s";
	case bench_mdssz: return "mul dbl s*s=z";
	case bench_mdnii: return "mul dbl n*i=i";
	case bench_ddnnn: return "div dbl n/n=n";
	case bench_ddsns: return "div dbl s/n=s";
	case bench_ddznz: return "div dbl 0/n=0";
	case bench_dsnnn: return "div flt n/n=n";
	case bench_ds111: return "div flt 1/1=1";
	case bench_dssns: return "div flt s/n=s";
	case bench_dsznz: return "div flt 0/n=0";
	case bench_dsnni: return "div flt n/n=i";
	case bench_dsiix: return "div flt i/i=X";
	case bench_n: break;
	}

	fprintf(stderr, "Invalid benchmark.");
	abort();
}

/**
 * Retrieve the related benchmark for comparison.
 *   @bench: The benchmark.
 *   &retuns: The base benchmark.
 */
enum bench_e bench_cmp(enum bench_e bench)
{
	switch(bench) {
	case bench_base: return bench_base;
	case bench_adnnn: return bench_adnnn;
	case bench_adsss: return bench_adnnn;
	case bench_mdnnn: return bench_mdnnn;
	case bench_mdsns: return bench_mdnnn;
	case bench_mdssz: return bench_mdnnn;
	case bench_mdnii: return bench_mdnnn;
	case bench_ddnnn: return bench_ddnnn;
	case bench_ddsns: return bench_ddnnn;
	case bench_ddznz: return bench_ddnnn;
	case bench_dsnnn: return bench_dsnnn;
	case bench_ds111: return bench_dsnnn;
	case bench_dssns: return bench_dsnnn;
	case bench_dsznz: return bench_dsnnn;
	case bench_dsnni: return bench_dsnnn;
	case bench_dsiix: return bench_dsnnn;
	case bench_n: break;
	}

	__builtin_unreachable();
}

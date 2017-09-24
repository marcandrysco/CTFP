#define _GNU_SOURCE
#include <errno.h>
#include <sched.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>


#include "common.h"


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
	unsigned int cnt = 100000;

	cpu_set_t set;
	CPU_ZERO(&set);
	CPU_SET(0, &set);

	int ret = sched_setaffinity(0, sizeof(set), &set);
	if(ret < 0)
		fprintf(stderr, "Unable to set affinity. %s.\n", strerror(errno));


	unsigned int i, n, sel;
	struct bench_t ref, ctfp;
	//uint32_t *ref[bench_n], *ctfp[bench_n];

	for(i = 0; i < bench_n; i++) {
		ref.run[i] = malloc(cnt * sizeof(uint32_t));
		ctfp.run[i] = malloc(cnt * sizeof(uint32_t));
	}

	for(n = 0; n < cnt; n++) {
		for(i = 0; i < bench_n; i++) {
			sel = (i + n) % bench_n;
			ref.run[sel][n] = run_ref[sel]();
			ctfp.run[sel][n] = run_ctfp[sel]();
		}
	}

	for(i = 0; i < bench_n; i++) {
		qsort(ref.run[i], cnt, sizeof(uint32_t), cmpnum);
		qsort(ctfp.run[i], cnt, sizeof(uint32_t), cmpnum);

		ref.ave[i] = 0.0;
		ctfp.ave[i] = 0.0;
		for(n = cnt / 4; n < (cnt - cnt / 4); n++) {
			ref.ave[i] += ref.run[i][n];
			ctfp.ave[i] += ctfp.run[i][n];
		}

		ref.ave[i] /= (cnt / 2);
		ctfp.ave[i] /= (cnt / 2);

		printf("bench %s : %.3f(%.3f) vs %.3f(%.3f)\n", bench_name(i), (ref.ave[i] - ref.ave[0]) / (ref.ave[1] - ref.ave[0]), ref.ave[i], (ctfp.ave[i] - ctfp.ave[0]) / (ref.ave[1] - ref.ave[0]), ctfp.ave[i]);
	}

	for(i = 0; i < bench_n; i++) {
		free(ref.run[i]);
		free(ctfp.run[i]);
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
const char *bench_name(enum bench_e bench) {
	switch(bench) {
	case bench_base: return "base         ";
	case bench_add_dnnn: return "add dbl n+n=n";
	case bench_add_dsss: return "add dbl s+s=s";
	case bench_mul_nnn: return "mul dbl n*n=n";
	case bench_mul_sns: return "mul dbl s*n=s";
	case bench_mdssz: return "mul dbl s*s=z";
	case bench_mdnii: return "mul dbl n*i=i";
	case bench_ddnnn: return "div dbl n*n=n";
	case bench_ddsns: return "div dbl s*n=s";
	case bench_ddznz: return "div dbl 0*n=0";
	case bench_dsnnn: return "div flt n*n=n";
	case bench_dssns: return "div flt s*n=s";
	case bench_dsznz: return "div flt 0*n=0";
	case bench_n: break;
	}

	fprintf(stderr, "Invalid benchmark.");
	abort();
}

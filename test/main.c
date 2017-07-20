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
	unsigned int cnt = 200000;

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
		for(n = cnt / 3; n < (cnt - cnt / 3); n++) {
			ref.ave[i] += ref.run[i][n];
			ctfp.ave[i] += ctfp.run[i][n];
		}

		ref.ave[i] /= (cnt / 2);
		ctfp.ave[i] /= (cnt / 2);

		printf("bench %d : %.3f vs %.3f\n", i, (ref.ave[i] - ref.ave[0]) / (ref.ave[1] - ref.ave[0]), (ctfp.ave[i] - ctfp.ave[0]) / (ref.ave[1] - ref.ave[0]));
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

#define _GNU_SOURCE
#include <errno.h>
#include <math.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>


/*
 * vector types
 */
typedef float float2 __attribute__((vector_size(2*sizeof(float))));
typedef float float4 __attribute__((vector_size(4*sizeof(float))));
typedef float float8 __attribute__((vector_size(8*sizeof(float))));
typedef float float16 __attribute__((vector_size(16*sizeof(float))));
typedef double double2 __attribute__((vector_size(2*sizeof(double))));
typedef double double4 __attribute__((vector_size(4*sizeof(double))));
typedef double double8 __attribute__((vector_size(8*sizeof(double))));

/*
 * statistics structure and declarations
 */
struct stats {
	double min;
	uint64_t nsubs, ninfs, nnans;
};

static struct stats stats32, stats64;

/*
 * synchronization structures
 */
static pthread_once_t once = PTHREAD_ONCE_INIT;
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

/*
 * function declarations
 */
static void init(void);
static void save(void);
static void save1(FILE *file, struct stats *stats);

static void init(void)
{
	memset(&stats32, 0x00, sizeof(struct stats));
	memset(&stats64, 0x00, sizeof(struct stats));
	stats32.min = INFINITY;
	stats64.min = INFINITY;

	atexit(save);
}

static void save1(FILE *file, struct stats *stats)
{
	fprintf(file, "min   %g\n", stats->min);
	fprintf(file, "nsubs %lu\n", stats->nsubs);
	fprintf(file, "ninfs %lu\n", stats->ninfs);
	fprintf(file, "nnans %lu\n", stats->nnans);
}

static void save(void)
{
	FILE *file;
	char path[256];

	snprintf(path, 256, "/tmp/fp.stats");
	file = fopen(path, "w");
	if(file != NULL) {
		fprintf(file, "# 32-bit\n");
		save1(file, &stats32);
		fprintf(file, "# 64-bit\n");
		save1(file, &stats64);
	}
}

static void fp32v1_proc(float f)
{
	pthread_once(&once, init);
	if(0)pthread_mutex_lock(&mutex);

	f = fabsf(f);

	if((f > 0.0f) && (f < stats32.min))
		stats32.min = f;

	if(fpclassify(f) == FP_SUBNORMAL)
		stats32.nsubs++;
	else if(fpclassify(f) == FP_INFINITE)
		stats32.ninfs++;
	else if(fpclassify(f) == FP_NAN)
		stats32.nnans++;

	if(0)pthread_mutex_unlock(&mutex);
}
static void fp64v1_proc(double f)
{
	pthread_once(&once, init);
	if(1)pthread_mutex_lock(&mutex);

	f = fabs(f);

	if((f > 0.0) && (f < stats64.min))
		stats64.min = f;

	if(fpclassify(f) == FP_SUBNORMAL)
		stats64.nsubs++;
	else if(fpclassify(f) == FP_INFINITE)
		stats64.ninfs++;
	else if(fpclassify(f) == FP_NAN)
		stats64.nnans++;

	if(1)pthread_mutex_unlock(&mutex);
}

#define PROC32(TY, WID, SZ) \
	static void fp##WID##v##SZ##_proc(TY##SZ f) { \
		for(int i = 0; i < SZ; i++) fp##WID##v1_proc(f[i]); \
	}

PROC32(float, 32, 2)
PROC32(float, 32, 4)
PROC32(float, 32, 8)
PROC32(float, 32, 16)
PROC32(double, 64, 2)
PROC32(double, 64, 4)
PROC32(double, 64, 8)

#define MKSQRT(TY, FUN, SZ) \
	static TY##SZ FUN##SZ(TY##SZ f) { \
		TY##SZ res; \
		for(int i = 0; i < SZ; i++) res[i] = FUN(f[i]); \
		return res; \
	}

MKSQRT(float, sqrtf, 2)
MKSQRT(float, sqrtf, 4)
MKSQRT(float, sqrtf, 8)
MKSQRT(float, sqrtf, 16)
MKSQRT(double, sqrt, 2)
MKSQRT(double, sqrt, 4)
MKSQRT(double, sqrt, 8)


#define fp_un(TY, WID, SZ, FUN, NAM) \
	TY fp##WID##v##SZ##_##NAM(TY a) { \
		fp##WID##v##SZ##_proc(a); \
		return FUN(a); \
	}

#define fp_bin(TY, WID, SZ, OP, NAM) \
	TY fp##WID##v##SZ##_##NAM(TY a, TY b) { \
		TY r = a OP b; \
		fp##WID##v##SZ##_proc(a); \
		fp##WID##v##SZ##_proc(b); \
		fp##WID##v##SZ##_proc(r); \
		return r; \
	}

fp_un(float, 32, 1, sqrtf, sqrt)
fp_un(float2, 32, 2, sqrtf2, sqrt)
fp_un(float4, 32, 4, sqrtf4, sqrt)
fp_un(float8, 32, 8, sqrtf8, sqrt)
fp_un(float16, 32, 16, sqrtf16, sqrt)
fp_un(double, 64, 1, sqrt, sqrt)
fp_un(double2, 64, 2, sqrt2, sqrt)
fp_un(double4, 64, 4, sqrt4, sqrt)
fp_un(double8, 64, 8, sqrt8, sqrt)

fp_bin(float, 32, 1, +, add)
fp_bin(float2, 32, 2, +, add)
fp_bin(float4, 32, 4, +, add)
fp_bin(float8, 32, 8, +, add)
fp_bin(float16, 32, 16, +, add)
fp_bin(double, 64, 1, +, add)
fp_bin(double2, 64, 2, +, add)
fp_bin(double4, 64, 4, +, add)
fp_bin(double8, 64, 8, +, add)

fp_bin(float, 32, 1, -, sub)
fp_bin(float2, 32, 2, -, sub)
fp_bin(float4, 32, 4, -, sub)
fp_bin(float8, 32, 8, -, sub)
fp_bin(float16, 32, 16, -, sub)
fp_bin(double, 64, 1, -, sub)
fp_bin(double2, 64, 2, -, sub)
fp_bin(double4, 64, 4, -, sub)
fp_bin(double8, 64, 8, -, sub)

fp_bin(float, 32, 1, *, mul)
fp_bin(float2, 32, 2, *, mul)
fp_bin(float4, 32, 4, *, mul)
fp_bin(float8, 32, 8, *, mul)
fp_bin(float16, 32, 16, *, mul)
fp_bin(double, 64, 1, *, mul)
fp_bin(double2, 64, 2, *, mul)
fp_bin(double4, 64, 4, *, mul)
fp_bin(double8, 64, 8, *, mul)

fp_bin(float, 32, 1, /, div)
fp_bin(float2, 32, 2, /, div)
fp_bin(float4, 32, 4, /, div)
fp_bin(float8, 32, 8, /, div)
fp_bin(float16, 32, 16, /, div)
fp_bin(double, 64, 1, /, div)
fp_bin(double2, 64, 2, /, div)
fp_bin(double4, 64, 4, /, div)
fp_bin(double8, 64, 8, /, div)

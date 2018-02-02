#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <stdlib.h>

typedef float v2f __attribute__((vector_size(2*sizeof(float))));
typedef float v4f __attribute__((vector_size(4*sizeof(float))));

typedef float v2d __attribute__((vector_size(2*sizeof(double))));
typedef float v4d __attribute__((vector_size(4*sizeof(double))));


void dump_f1(float v)
{
	printf("dump: %g\n", v);
}
void dump_f2(v2f v)
{
	printf("dump: %g,%g\n", v[0], v[1]);
}
void dump_f4(v4f v)
{
	printf("dump: %g,%g,%g,%g\n", v[0], v[1], v[2], v[3]);
}
void dump_d1(double v)
{
	printf("dump: %g\n", v);
}
void dump_d2(v2d v)
{
	printf("dump: %g %g\n", v[0], v[1]);
}
void dump_d4(v4d v)
{
	printf("dump: %g %g %g %g\n", v[0], v[1], v[2], v[3]);
}



/**
 * Verify a float division is safe.
 *   @a: The first operand.
 *   @b: The second operand.
 *   @pow2: Set to true for powers of two, false otherwise.
 *   &returns: The division.
 */
float chkdiv_f1(float a, float b, int pow2)
{
	int e;

	if(a == 0.0f)
		printf("chkdiv(float) a = 0.0\n");
	else if(a == INFINITY)
		printf("chkdiv(float) a = inf\n");
	else if(isnanf(a))
		printf("chkdiv(float) a = nan\n");
	else if(fabsf(a) < FLT_MIN)
		printf("chkdiv(float) a = subnorm\n");

	if(b == 0.0f)
		printf("chkdiv(float) b = 0.0\n");
	else if(b == INFINITY)
		printf("chkdiv(float) b = inf\n");
	else if(isnanf(b))
		printf("chkdiv(float) b = nan\n");
	else if(pow2 && (frexpf(fabsf(b), &e) != 0.5f))
		printf("chkdiv(float) b = !pow2\n");
	else if(!pow2 && (frexpf(fabsf(b), &e) == 0.5f))
		printf("chkdiv(float) b = pow2\n");
	else if(fabsf(b) < FLT_MIN)
		printf("chkdiv(float) b = subnorm\n");

	return a / b;
}
v2f chkdiv_f2(v2f a, v2f b, int pow2)
{
	a[0] = chkdiv_f1(a[0], b[0], pow2);
	a[1] = chkdiv_f1(a[1], b[1], pow2);

	return a;
}
v4f chkdiv_f4(v4f a, v4f b, int pow2)
{
	a[0] = chkdiv_f1(a[0], b[0], pow2);
	a[1] = chkdiv_f1(a[1], b[1], pow2);
	a[2] = chkdiv_f1(a[2], b[2], pow2);
	a[3] = chkdiv_f1(a[3], b[3], pow2);

	return a;
}

/**
 * Verify a float division is safe.
 *   @a: The first operand.
 *   @b: The second operand.
 *   @pow2: Set to true for powers of two, false otherwise.
 *   &returns: The division.
 */
double chkdiv_d1(double a, double b, int pow2)
{
	int e;

	if(a == 0.0)
		printf("chkdiv(double) a = 0.0\n");
	else if(a == INFINITY)
		printf("chkdiv(double) a = inf\n");
	else if(isnan(a))
		printf("chkdiv(double) a = nan\n");
	else if(fabs(a) < DBL_MIN)
		printf("chkdiv(double) a = subnorm\n");

	if(b == INFINITY)
		printf("chkdiv(double) b = 0.0\n");
	else if(b == INFINITY)
		printf("chkdiv(double) b = inf\n");
	else if(isnan(b))
		printf("chkdiv(double) b = nan\n");
	else if(pow2 && (frexp(fabs(b), &e) != 0.5))
		printf("chkdiv(double) b = !pow2\n");
	else if(!pow2 && (frexp(fabs(b), &e) == 0.5))
		printf("chkdiv(double) b = pow2\n");
	else if(fabs(b) < DBL_MIN)
		printf("chkdiv(double) b = subnorm\n");

	return a / b;
}

/**
 * Verify a float division is safe.
 *   @a: The first operand.
 *   @b: The second operand.
 *   @pow2: Set to true for powers of two, false otherwise.
 *   &returns: The division.
 */
float chksqrt_f1(float a)
{
	int e;

	if(a == INFINITY)
		printf("chksqrt(float) a = 0.0\n");
	else if(a == INFINITY)
		printf("chksqrt(float) a = inf\n");
	else if(isnan(a))
		printf("chksqrt(float) a = nan\n");
	else if((frexpf(fabsf(a), &e) == 0.5) && (((e & 0x1) == 0x1)))
		printf("chksqrt(float) a = !pow2\n");
	else if(fabsf(a) < FLT_MIN)
		printf("chksqrt(float) a = subnorm\n");

	return sqrtf(a);
}
v2f chksqrt_f2(v2f a)
{
	a[0] = chksqrt_f1(a[0]);
	a[1] = chksqrt_f1(a[1]);

	return a;
}
v4f chksqrt_f4(v4f a)
{
	a[0] = chksqrt_f1(a[0]);
	a[1] = chksqrt_f1(a[1]);
	a[2] = chksqrt_f1(a[2]);
	a[3] = chksqrt_f1(a[3]);

	return a;
}

/**
 * Verify a double division is safe.
 *   @a: The first operand.
 *   @b: The second operand.
 *   @pow2: Set to true for powers of two, false otherwise.
 *   &returns: The division.
 */
double chksqrt_d1(double a)
{
	int e;

	if(a == INFINITY)
		printf("chksqrt(double) a = 0.0\n");
	else if(a == INFINITY)
		printf("chksqrt(double) a = inf\n");
	else if(isnan(a))
		printf("chksqrt(double) a = nan\n");
	else if((frexp(fabs(a), &e) == 0.5) && (((e & 0x1) == 0x1)))
		printf("chksqrt(double) a = !pow2\n");
	else if(fabs(a) < DBL_MIN)
		printf("chksqrt(double) a = subnorm\n");

	return sqrt(a);
}

float getexp_f1(float);
float getexp_d1(double);

float getsig_f1(float);
float getsig_d1(double);

float divbyparts_f1(float, float);
float divbyparts_d1(double, double);

float divdummy_f1(float, float);
float divdummy_d1(double, double);

float ctfp_add1_f1(float, float);
float ctfp_add2_f1(float, float);
float ctfp_sub1_f1(float, float);
float ctfp_sub2_f1(float, float);
float ctfp_mul1_f1(float, float);
float ctfp_mul2_f1(float, float);
float ctfp_mul2_fma_f1(float, float);
float ctfp_div1_f1(float, float);
float ctfp_div2_f1(float, float);
float ctfp_sqrt1_f1(float);
double ctfp_add1_d1(double, double);
double ctfp_add2_d1(double, double);
double ctfp_sub1_d1(double, double);
double ctfp_sub2_d1(double, double);
double ctfp_mul1_d1(double, double);
double ctfp_mul2_d1(double, double);
double ctfp_div1_d1(double, double);
double ctfp_div2_d1(double, double);


#define chk(cond) if(!(cond)) { fprintf(stderr, "failed '%s'\n", #cond); }

static inline bool isnanpos(double v)
{
	return isnan(v) && !signbit(v);
}

static inline bool isnanneg(double v)
{
	return isnan(v) && signbit(v);
}


/**
 * Check if two floating point numbers are equivalent.
 *   @a: The first number.
 *   @b: The seonc number.
 *   &returns: True if equivalent, false otherwise.
 */
bool isequal(double a, double b)
{
	if(isnan(a) && isnan(b))
		return true;
	else if((a == 0.0f) && (b == 0.0f))
		return signbit(a) == signbit(b);
	else
		return a == b;
}


#define ARRLEN(arr) (sizeof((arr)) / sizeof(*(arr)))


int main(int argc, char **argv)
{
	//fesetround(FE_TOWARDZERO);

	/*
	unsigned int cnt;
	for(float f = 0.25; f <= 0.5; f = nextafterf(f, INFINITY)) {
		float r0 = (float)FLT_MIN / f;
		float r1 = nextafter(r1, INFINITY);
		float r2 = nextafter(r1, -INFINITY);

		if(f * r0 >= FLT_MIN) {
			if(ctfp_mul2_f1(f, r0) != (f * r0))
				cnt++;
				//printf("fail: %.8e * %.8e\n", f, r0), exit(1);
		}

		if(f * r1 >= FLT_MIN) {
			if(ctfp_mul2_f1(f, r1) != (f * r1))
				cnt++;
				//printf("fail: %.8e * %.8e\n", f, r0), exit(1);
		}

		if(f * r2 >= FLT_MIN) {
			if(ctfp_mul2_f1(f, r2) != (f * r2))
				cnt++;
				//printf("fail: %.8e * %.8e\n", f, r0), exit(1);
		}
	}
	printf("cnt: %d of %d (%.5f)\n", cnt, 2 << 24, (double)(cnt) / (2 << 24));
	printf("tot: %d\n", cnt * 126);
	return 0;
	*/

	if(0) {
	//chk(ctfp_mul2_f1(3.1541636478430075e-27f, 3.7268018532321534e-12f) == (3.1541636478430075e-27f * 3.7268018532321534e-12f));
	//chk(ctfp_mul2_f1(5.87608427642357e-20f, 2.0004720757150539e-19) == 0.0f);
	//float f = ctfp_mul2_f1(3.1541636478430075e-27f, 3.7268018532321534e-12f);
	float f = ctfp_mul2_f1(5.87608427642357e-20f, 2.0004720757150539e-19);
	uint32_t u;
	memcpy(&u, &f, 4);
	printf("%.16e %08x  (vs %.17e)\n", f, u, 0.0 / 0.0);
	exit(1);
	}

	if(0) {
		float a, b;

		a = 1.3; b = 3.4;
		printf("got: %g (expected: %g)\n", divdummy_f1(a, b), a / b);

		a = 1.3; b = 2.0;
		printf("got: %g (expected: %g)\n", divdummy_f1(a, b), a / b);

		a = FLT_MIN; b = FLT_MAX;
		printf("got: %g (expected: %g)\n", divdummy_f1(a, b), a / b);

		a = FLT_MAX; b = FLT_MIN;
		printf("got: %g (expected: %g)\n", divdummy_f1(a, b), a / b);

		return 0;
	}

	if(0) {
		float a;

		a = INFINITY;
		printf("got: %g (expected: %g)\n", ctfp_sqrt1_f1(a), sqrtf(a));

		return 0;
	}

	if(0) {
		float a, b;

		a = 3.8f;
		b = NAN;

		printf("got: %g (expected: %g)\n", divdummy_f1(a, b), a / b);

		return 0;
	}

	chk(ctfp_add1_f1(1.1f, 0.6f) == (1.1f + 0.6f));
	chk(ctfp_add1_f1(FLT_MIN, FLT_MIN) == 0.0f);
	chk(ctfp_add2_f1(FLT_MIN, FLT_MIN) == (FLT_MIN + FLT_MIN));
	chk(ctfp_add2_f1(FLT_MIN / 2, FLT_MIN / 2) == 0.0f);
	chk(ctfp_add2_f1(-2.5521187660275187e+38f, 1.0133342915435717e+32f) == (-2.5521187660275187e+38f + 1.0133342915435717e+32f));
	chk(ctfp_add2_f1(FLT_MIN, -FLT_MIN - FLT_MIN / 2.0f) == 0.0);

	chk(ctfp_add1_f1(FLT_MIN, 8388608.0f * FLT_MIN) == (8388608.0f * FLT_MIN));
	chk(ctfp_add1_f1(FLT_MIN, -8388608.0f * FLT_MIN) == (-8388608.0f * FLT_MIN));

	chk(ctfp_add2_d1(1.1, 0.6) == (1.1 + 0.6));
	chk(ctfp_sub2_d1(1.1, 0.6) == (1.1 - 0.6));
	chk(ctfp_add2_d1(DBL_MIN, DBL_MIN) == (DBL_MIN + DBL_MIN));
	chk(ctfp_add1_d1(DBL_MIN, DBL_MIN) == 0.0);
	chk(ctfp_add2_d1(DBL_MIN, 0.0) == DBL_MIN);
	chk(ctfp_add2_d1(0.0, DBL_MIN) == DBL_MIN);
	chk(ctfp_add2_d1(2.2250738585072013e-308, 0.0) == 2.2250738585072013e-308);

	chk(ctfp_sub2_f1(FLT_MIN, nextafter(FLT_MIN, INFINITY)) == 0.0f);

	chk(ctfp_mul1_f1(1.1f, 0.6f) == (1.1f * 0.6f));
	chk(ctfp_mul1_f1(FLT_MIN, 1.0f) == 0.0f);
	chk(ctfp_mul2_f1(FLT_MIN, 0.5f) == 0.0);
	chk(ctfp_mul2_f1(2.0f * FLT_MIN, 0.5f) == FLT_MIN);
	chk(ctfp_mul2_f1(sqrt(FLT_MIN), sqrt(FLT_MIN)) == FLT_MIN);
	chk(ctfp_mul2_f1(sqrt(FLT_MIN / 2.0f), sqrt(FLT_MIN)) == 0.0);

	//chk(ctfp_mul2_f1(3.1541636478430075e-27f, 3.7268018532321534e-12f) == (3.1541636478430075e-27f * 3.7268018532321534e-12f));
	//chk(ctfp_mul2_f1(5.87608427642357e-20f, 2.0004720757150539e-19) == 0.0f);

	chk(ctfp_add1_d1(1.1, 0.6) == (1.1 + 0.6));
	chk(ctfp_add2_d1(1.1, 0.6) == (1.1 + 0.6));
	chk(ctfp_add1_d1(2.350988701644575e-38, 2.350988701644575e-38) == (2.350988701644575e-38 + 2.350988701644575e-38));
	chk(ctfp_add2_d1(2.350988701644575e-38, 2.350988701644575e-38) == (2.350988701644575e-38 + 2.350988701644575e-38));

	chk(isnan(ctfp_div1_f1((float)NAN, 2.2f)));
	chk(isnan(ctfp_div1_f1(3.8f, (float)NAN)));
	chk(ctfp_div1_f1(1.0f, (float)INFINITY) == (1.0f / (float)INFINITY));
	chk(ctfp_div1_f1((float)INFINITY, 1.0f) == ((float)INFINITY / 1.0f));
	chk(ctfp_div1_f1(2.0f, 256.0f) == (2.0f / 256.0f));
	chk(ctfp_div1_f1(1.7f, 32.0f) == (1.7f / 32.0f));
	chk(ctfp_div1_f1(1.3f, 3.8f) == (1.3f / 3.8f));
	chk(ctfp_div1_f1(1.0f, 1.0f) == 1.0f);
	chk(ctfp_div1_f1(1.0f, -1.0f) == -1.0f);
	chk(ctfp_div1_f1(1.0f, FLT_MAX / 8.0f) == 0.0f);

	chk(isnan(ctfp_div2_f1((float)NAN, 2.2f)));
	chk(isnan(ctfp_div2_f1(3.8f, (float)NAN)));
	chk(ctfp_div2_f1(1.0f, (float)INFINITY) == (1.0f / (float)INFINITY));
	chk(ctfp_div2_f1((float)INFINITY, 1.0f) == ((float)INFINITY / 1.0f));
	chk(ctfp_div2_f1(2.0f, 256.0f) == (2.0f / 256.0f));
	chk(ctfp_div2_f1(1.7f, 32.0f) == (1.7f / 32.0f));
	chk(ctfp_div2_f1(1.3f, 3.8f) == (1.3f / 3.8f));
	chk(ctfp_div2_f1(FLT_MAX * 0.3f, 0.1f) == INFINITY);
	chk(ctfp_div2_f1(1.0f, 1.0f) == 1.0f);
	chk(ctfp_div2_f1(1.0f, FLT_MAX / 8.0f) == (1.0f / (FLT_MAX / 8.0f)));
	chk(ctfp_div2_f1(FLT_MIN, 0.0f) == INFINITY);
	chk(ctfp_div2_f1(1.2e-38, 1.4f) == 0.0f);
	chk(ctfp_div2_f1(1.4f, 1.2e-20f) == (1.4f / 1.2e-20f));
	chk(isnan(ctfp_div2_f1(0.0f, 0.0f)));
	chk(isnan(ctfp_div2_f1((float)INFINITY, (float)INFINITY)));

	chk(ctfp_sqrt1_f1(0.0f) == sqrtf(0.0f));
	chk(ctfp_sqrt1_f1(1.4f) == sqrtf(1.4f));
	chk(ctfp_sqrt1_f1(256.0f) == sqrtf(256.0f));
	chk(ctfp_sqrt1_f1(512.0f) == sqrtf(512.0f));
	chk(ctfp_sqrt1_f1(INFINITY) == sqrtf(INFINITY));
	chk(isnan(ctfp_sqrt1_f1(-INFINITY)));
	chk(isnan(ctfp_sqrt1_f1(NAN)));
	chk(isnan(ctfp_sqrt1_f1(-NAN)));
	chk(isnan(ctfp_sqrt1_f1(-1.0f)));

	unsigned int i, j;
	volatile float flts[] = { 0.0f, -0.0f, 1.0f, -1.0f, 2.3f, -2.3f, 1e-10, -1e-10, INFINITY, -INFINITY, NAN };

	for(i = 0; i < ARRLEN(flts); i++) {
		for(j = 0; j < ARRLEN(flts); j++) {
			if(!isequal(ctfp_add1_f1(flts[i], flts[j]), flts[i] + flts[j]))
				fprintf(stderr, "ctfp1_add1_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_mul1_f1(flts[i], flts[j]), flts[i] * flts[j]))
				fprintf(stderr, "ctfp1_mul1_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_div1_f1(flts[i], flts[j]), flts[i] / flts[j]))
				fprintf(stderr, "ctfp1_div1_f1(%g,%g)\n", flts[i], flts[j]);

			if(!isequal(ctfp_add2_f1(flts[i], flts[j]), flts[i] + flts[j]))
				fprintf(stderr, "ctfp1_add2_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_mul2_f1(flts[i], flts[j]), flts[i] * flts[j]))
				fprintf(stderr, "ctfp1_mul2_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_div2_f1(flts[i], flts[j]), flts[i] / flts[j]))
				fprintf(stderr, "ctfp1_div2_f1(%g,%g)\n", flts[i], flts[j]);
		}

		if(!isequal(ctfp_sqrt1_f1(flts[i]), sqrtf(flts[i])))
			fprintf(stderr, "ctfp1_sqrt1_f1(%g) %g vs %g\n", flts[i], ctfp_sqrt1_f1(flts[i]), sqrtf(flts[i]));
	}

	//if(!isequal(ctfp_mul2_f1(7.47473284e-38, 1.57262385e-01), FLT_MIN))
		//fprintf(stderr, "ctfp1_add1_f1(%g,%g)\n", 7.47473284e-38, 1.57262385e-01);

	//return 0;

	float v;

	for(v = 0.125f; v <= 0.25f; v = nextafterf(v, INFINITY)) {
		float r, t;
		
		t = FLT_MIN / v;

		r = t * v;
		if(r < FLT_MIN)
			r = 0.0f;

		if(r != ctfp_mul2_fma_f1(t, v))
			printf("ctfp_mul2_f1(%.8e,%.8e) = %.8e vs %.8e\n", t, v, ctfp_mul2_f1(t, v), r);
	}

	return 0;

	/*
	printf("%.8e\n", ctfp_add1_f1(1.1, 0.6f));
	printf("%.8e\n", ctfp_add1_f1(FLT_MIN, FLT_MIN));
	printf("%.8e\n", ctfp_add2_f1(1.1, 0.6f));
	printf("%.8e\n", ctfp_add2_f1(FLT_MIN, FLT_MIN));
	printf("%.8e\n", ctfp_add2_f1(FLT_MIN/2, FLT_MIN));

	printf("div 1,1: %.8e\n", ctfp_div1_f1(1, 1));
	printf("div M,M: %.8e\n", ctfp_div1_f1(FLT_MIN, FLT_MIN));
	printf("div 1,1: %.8e\n", ctfp_div1_f1(1, 1e20));
	printf("div 1,1: %.8e\n", ctfp_div1_f1(1, 1e-20));

	printf("add2: %.8e\n", ctfp_add2_f1(-2.5521187660275187e+38, 1.0133342915435717e+32));
	fesetround(FE_TOWARDZERO);
	printf("add2: %.8e\n", ctfp_add2_f1(-2.5521187660275187e+38, 1.0133342915435717e+32));

	float f = FLT_MAX;
	uint32_t v;

	memcpy(&v, &f, 4);

	printf("%08x\n", v);
	*/

	return 0;
}

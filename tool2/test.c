#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <stdlib.h>


float ctfp_add1_f1(float, float);
float ctfp_add2_f1(float, float);
float ctfp_add3_f1(float, float);
float ctfp_sub1_f1(float, float);
float ctfp_sub2_f1(float, float);
float ctfp_sub3_f1(float, float);
float ctfp_mul1_f1(float, float);
float ctfp_mul3_f1(float, float);
float ctfp_div1_f1(float, float);
float ctfp_div2_f1(float, float);
float ctfp_div3_f1(float, float);
float ctfp_sqrt1_f1(float);
double ctfp_add1_d1(double, double);
double ctfp_add2_d1(double, double);
double ctfp_add3_d1(double, double);
double ctfp_sub1_d1(double, double);
double ctfp_sub2_d1(double, double);
double ctfp_sub3_d1(double, double);
double ctfp_mul1_d1(double, double);
double ctfp_mul3_d1(double, double);
double ctfp_div1_d1(double, double);
double ctfp_div2_d1(double, double);
double ctfp_div3_d1(double, double);


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

	if(0) {
	float f = ctfp_div1_f1(0.0, 0.0);
	uint32_t u;
	memcpy(&u, &f, 4);
	printf("%.16e %08x  (vs %.17e)\n", f, u, 0.0 / 0.0);
	exit(1);
	}

	chk(ctfp_add1_f1(1.1f, 0.6f) == (1.1f + 0.6f));
	chk(ctfp_add1_f1(FLT_MIN, FLT_MIN) == 0.0f);
	chk(ctfp_add3_f1(FLT_MIN, FLT_MIN) == (FLT_MIN + FLT_MIN));
	chk(ctfp_add3_f1(FLT_MIN / 2, FLT_MIN / 2) == 0.0f);
	chk(ctfp_add3_f1(-2.5521187660275187e+38f, 1.0133342915435717e+32f) == (-2.5521187660275187e+38f + 1.0133342915435717e+32f));

	chk(ctfp_add1_f1(FLT_MIN, 8388608.0f * FLT_MIN) == (8388608.0f * FLT_MIN));
	chk(ctfp_add1_f1(FLT_MIN, -8388608.0f * FLT_MIN) == (-8388608.0f * FLT_MIN));

	chk(ctfp_add3_d1(1.1, 0.6) == (1.1 + 0.6));
	chk(ctfp_sub3_d1(1.1, 0.6) == (1.1 - 0.6));
	chk(ctfp_add3_d1(DBL_MIN, DBL_MIN) == (DBL_MIN + DBL_MIN));
	chk(ctfp_add1_d1(DBL_MIN, DBL_MIN) == 0.0);
	chk(ctfp_add3_d1(DBL_MIN, 0.0) == DBL_MIN);
	chk(ctfp_add3_d1(0.0, DBL_MIN) == DBL_MIN);
	chk(ctfp_add3_d1(2.2250738585072013e-308, 0.0) == 2.2250738585072013e-308);

	chk(ctfp_sub2_f1(FLT_MIN, nextafter(FLT_MIN, INFINITY)) == 0.0f);

	chk(ctfp_mul1_f1(1.1f, 0.6f) == (1.1f * 0.6f));
	chk(ctfp_mul1_f1(FLT_MIN, 1.0f) == 0.0f);
	chk(ctfp_mul3_f1(FLT_MIN, 0.5f) == 0.0);
	chk(ctfp_mul3_f1(2.0f * FLT_MIN, 0.5f) == FLT_MIN);

	chk(ctfp_mul3_f1(3.1541636478430075e-27f, 3.7268018532321534e-12f) == (3.1541636478430075e-27f * 3.7268018532321534e-12f));

	chk(ctfp_add1_d1(1.1, 0.6) == (1.1 + 0.6));
	chk(ctfp_add3_d1(1.1, 0.6) == (1.1 + 0.6));
	chk(ctfp_add1_d1(2.350988701644575e-38, 2.350988701644575e-38) == (2.350988701644575e-38 + 2.350988701644575e-38));
	chk(ctfp_add3_d1(2.350988701644575e-38, 2.350988701644575e-38) == (2.350988701644575e-38 + 2.350988701644575e-38));

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

	chk(isnan(ctfp_div3_f1((float)NAN, 2.2f)));
	chk(isnan(ctfp_div3_f1(3.8f, (float)NAN)));
	chk(ctfp_div3_f1(1.0f, (float)INFINITY) == (1.0f / (float)INFINITY));
	chk(ctfp_div3_f1((float)INFINITY, 1.0f) == ((float)INFINITY / 1.0f));
	chk(ctfp_div3_f1(2.0f, 256.0f) == (2.0f / 256.0f));
	chk(ctfp_div3_f1(1.7f, 32.0f) == (1.7f / 32.0f));
	chk(ctfp_div3_f1(1.3f, 3.8f) == (1.3f / 3.8f));
	chk(ctfp_div3_f1(FLT_MAX * 0.3f, 0.1f) == INFINITY);
	chk(ctfp_div3_f1(1.0f, 1.0f) == 1.0f);
	chk(ctfp_div3_f1(1.0f, FLT_MAX / 8.0f) == (1.0f / (FLT_MAX / 8.0f)));
	chk(ctfp_div3_f1(FLT_MIN, 0.0f) == INFINITY);
	chk(ctfp_div3_f1(1.2e-38, 1.4f) == 0.0f);
	chk(ctfp_div3_f1(1.4f, 1.2e-20f) == (1.4f / 1.2e-20f));
	chk(isnan(ctfp_div3_f1(0.0f, 0.0f)));
	chk(isnan(ctfp_div3_f1((float)INFINITY, (float)INFINITY)));

	chk(ctfp_sqrt1_f1(0.0f) == sqrtf(0.0f));
	chk(ctfp_sqrt1_f1(1.4f) == sqrtf(1.4f));
	chk(ctfp_sqrt1_f1(256.0f) == sqrtf(256.0f));
	chk(ctfp_sqrt1_f1(512.0f) == sqrtf(512.0f));
	chk(ctfp_sqrt1_f1(INFINITY) == sqrtf(INFINITY));
	chk(isnanneg(ctfp_sqrt1_f1(-INFINITY)));
	chk(isnanpos(ctfp_sqrt1_f1(NAN)));
	chk(isnanneg(ctfp_sqrt1_f1(-NAN)));
	chk(isnanneg(ctfp_sqrt1_f1(-1.0f)));

	unsigned int i, j;
	volatile float flts[] = { 0.0f, -0.0f, 1.0f, -1.0f, 2.3f, -2.3f, INFINITY, -INFINITY };

	for(i = 0; i < ARRLEN(flts); i++) {
		for(j = 0; j < ARRLEN(flts); j++) {
			if(!isequal(ctfp_add1_f1(flts[i], flts[j]), flts[i] + flts[j]))
				fprintf(stderr, "ctfp1_add1_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_mul1_f1(flts[i], flts[j]), flts[i] * flts[j]))
				fprintf(stderr, "ctfp1_mul1_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_div1_f1(flts[i], flts[j]), flts[i] / flts[j]))
				fprintf(stderr, "ctfp1_div1_f1(%g,%g)\n", flts[i], flts[j]);

			if(!isequal(ctfp_add3_f1(flts[i], flts[j]), flts[i] + flts[j]))
				fprintf(stderr, "ctfp1_add3_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_mul3_f1(flts[i], flts[j]), flts[i] * flts[j]))
				fprintf(stderr, "ctfp1_mul3_f1(%g,%g)\n", flts[i], flts[j]);
			if(!isequal(ctfp_div3_f1(flts[i], flts[j]), flts[i] / flts[j]))
				fprintf(stderr, "ctfp1_div3_f1(%g,%g)\n", flts[i], flts[j]);
		}

		if(!isequal(ctfp_sqrt1_f1(flts[i]), sqrtf(flts[i])))
			fprintf(stderr, "ctfp1_sqrt1_f1(%g)\n", flts[i]);
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

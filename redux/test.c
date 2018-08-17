#include <stdio.h>
#include <float.h>
#include <time.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>


/*
 * function declarations
 */
float rand_f32(void);


/*
 * ctfp declarations
 */
float ctfp_restrict_add_f32v1_hack(float, float);
float ctfp_restrict_sub_f32v1_hack(float, float);
float ctfp_restrict_mul_f32v1_hack(float, float);
float ctfp_restrict_div_f32v1_hack(float, float);
float ctfp_restrict_sqrt_f32v1(float);
float ctfp_full_add_f32v1_hack(float, float);
float ctfp_full_sub_f32v1_hack(float, float);
float ctfp_full_mul_f32v1_hack(float, float);
float ctfp_full_div_f32v1_hack(float, float);
float ctfp_full_sqrt_f32v1(float);


static inline bool issub(double f)
{
	return (fabs(f) < DBL_MIN) && (f != 0.0);
}
static inline bool issubf(float f)
{
	return (fabsf(f) < FLT_MIN) && (f != 0.0);
}

/**
 * Check if a value is special.
 *   @f: The float.
 *   &returns: True if special.
 */
bool chk_spec_f32(float f)
{
	return (f == INFINITY) || (f == -INFINITY) || isnanf(f) || issubf(f);
}

/**
 * Check if a value is special.
 *   @f: The double.
 *   &returns: True if special.
 */
bool chk_spec_f64(double f)
{
	return (f == INFINITY) || (f == -INFINITY) || isnan(f) || issub(f);
}

typedef float v2f32 __attribute__((vector_size(8)));
typedef float v4f32 __attribute__((vector_size(16)));
typedef float v8f32 __attribute__((vector_size(32)));
typedef float v16f32 __attribute__((vector_size(64)));
typedef double v2f64 __attribute__((vector_size(16)));
typedef double v4f64 __attribute__((vector_size(32)));
typedef double v8f64 __attribute__((vector_size(64)));

static inline bool ispow2(double f)
{
	int exp;

	f = frexp(f, &exp);

	return f == 0.5;
}

static inline bool ispow4(double f)
{
	int exp;

	f = frexp(f, &exp);

	return (f == 0.5) && (exp & 1);
}

/**
 * Generator for one-operand debug functions.
 *   @NAM: The function name.
 *   @TY: The type.
 *   @OP: The operation.
 *   @COND: The safety condition.
 */
#define DBG_GEN1(NAM, TY, OP, COND) \
	TY dbg_##NAM(TY a) { \
	  TY r = OP(a); \
	  if(COND) fprintf(stderr, "unsafe " #NAM "(%.9g)\n", a); \
	  return r; \
	}

/**
 * Generator for two-operand debug functions.
 *   @NAM: The function name.
 *   @TY: The type.
 *   @OP: The operation.
 *   @COND: The safety condition.
 */
#define DBG_GEN2(NAM, TY, OP, COND) \
	TY dbg_##NAM(TY a, TY b) { \
	  TY r = a OP b; \
	  /*fprintf(stderr, #NAM "(%.9g, %.9g) = %.9g\n", a, b, r);*/ \
	  if(COND) fprintf(stderr, "unsafe " #NAM "(%.9g, %.9g) = %.9g\n", a, b, r); \
	  return r; \
	}

/**
 * Generator for one-operand vectorized functions.
 *   @NAM: The function name.
 *   @TY: The type.
 *   @BAS: The base type.
 */
#define DBG_VEC1(NAM, TY, BAS, WID) \
	TY dbg_##NAM(TY a, TY b) { \
		TY r; int i; \
		for(i = 0; i < WID; i++) r[i] = dbg_##BAS(a[i]); \
		return r; \
	}

/**
 * Generator for two-operand vectorized functions.
 *   @NAM: The function name.
 *   @TY: The type.
 *   @BAS: The base type.
 */
#define DBG_VEC2(NAM, TY, BAS, WID) \
	TY dbg_##NAM(TY a, TY b) { \
		TY r; int i; \
		for(i = 0; i < WID; i++) r[i] = dbg_##BAS(a[i], b[i]); \
		return r; \
	}

#define COND_STD       (issubf(a) || issubf(b) || issubf(r))
#define COND_ISSPEC(a) ((a == INFINITY) || (a == -INFINITY) || isnan(a) || (a == 0.0))
#define COND_DIVSIG    ((COND_STD) || COND_ISSPEC(a) || COND_ISSPEC(b) || ispow2(b))
#define COND_DIVEXP    ((COND_STD) || COND_ISSPEC(a) || COND_ISSPEC(b) || !ispow2(b))
#define COND_SQRT      (issub(a) || issub(r) || COND_ISSPEC(a) || ispow4(a) || (a < 0.0))

DBG_GEN2(fadd_f32, float, +, COND_STD);
DBG_GEN2(fsub_f32, float, -, COND_STD);
DBG_GEN2(fmul_f32, float, *, COND_STD);
DBG_GEN2(fdiv_sig_f32, float, /, COND_DIVSIG);
DBG_GEN2(fdiv_exp_f32, float, /, COND_DIVEXP);
DBG_GEN1(fsqrt_f32, float, sqrtf, COND_SQRT);

DBG_GEN2(fadd_f64, double, +, COND_STD);
DBG_GEN2(fsub_f64, double, -, COND_STD);
DBG_GEN2(fmul_f64, double, *, COND_STD);
DBG_GEN2(fdiv_sig_f64, double, /, COND_DIVSIG);
DBG_GEN2(fdiv_exp_f64, double, /, COND_DIVEXP);
DBG_GEN1(fsqrt_f64, double, sqrt, COND_SQRT);

#define DBG_VEC_ALL(BIT, WID) \
	DBG_VEC2(fadd_v##WID##f##BIT, v##WID##f##BIT, fadd_f##BIT, WID); \
	DBG_VEC2(fsub_v##WID##f##BIT, v##WID##f##BIT, fsub_f##BIT, WID); \
	DBG_VEC2(fmul_v##WID##f##BIT, v##WID##f##BIT, fmul_f##BIT, WID); \
	DBG_VEC2(fdiv_sig_v##WID##f##BIT, v##WID##f##BIT, fdiv_sig_f##BIT, WID); \
	DBG_VEC2(fdiv_exp_v##WID##f##BIT, v##WID##f##BIT, fdiv_exp_f##BIT, WID); \
	DBG_VEC1(fsqrt_v##WID##f##BIT, v##WID##f##BIT, fsqrt_f##BIT, WID); \

DBG_VEC_ALL(32, 2);
DBG_VEC_ALL(32, 4);
DBG_VEC_ALL(32, 8);
DBG_VEC_ALL(32, 16);
DBG_VEC_ALL(64, 2);
DBG_VEC_ALL(64, 4);
DBG_VEC_ALL(64, 8);

#define ARRSIZE(arr) (sizeof(arr) / sizeof(arr[0]))


float underflow(float v, float m)
{
	return (fabsf(v) < m) ? copysign(0.0f, v) : v;
}

float overflow(float v, float m)
{
	return (fabsf(v) > m) ? copysign(INFINITY, v) : v;
}

/*
 * floating point contants
 */
float addmin_f32 = 9.86076131526264760e-32;
double addmin_f64 = 2.00416836000897278e-292;
float mulmin_f32 = 1.08420217248550443e-19;
double mulmin_f64 = 1.49166814624004135e-154;
float divmax_f32 = 4.61168601842738790e+18;
double divmax_f64 = 3.35195198248564927e+153;

/*
 * ctfp semantic simulation functions
 */
float simul_restrict_add_f32(float a, float b) { return underflow(a, addmin_f32) + underflow(b, addmin_f32); }
float simul_restrict_sub_f32(float a, float b) { return underflow(a, addmin_f32) - underflow(b, addmin_f32); }
float simul_restrict_mul_f32(float a, float b) { return underflow(a, mulmin_f32) * underflow(b, mulmin_f32); }
float simul_restrict_div_f32(float a, float b) {
	a = overflow(underflow(a, mulmin_f32), divmax_f32);
	b = overflow(underflow(b, mulmin_f32), divmax_f32);
	return a / b;
}
float simul_restrict_sqrt_f32(float a) { return sqrtf(underflow(a, FLT_MIN)); }

float simul_full_add_f32(float a, float b) {
	a = underflow(a, FLT_MIN);
	b = underflow(b, FLT_MIN);
	return underflow(a + b, FLT_MIN);
}
float simul_full_sub_f32(float a, float b) {
	a = underflow(a, FLT_MIN);
	b = underflow(b, FLT_MIN);
	return underflow(a - b, FLT_MIN);
}
float simul_full_mul_f32(float a, float b) {
	a = underflow(a, FLT_MIN);
	b = underflow(b, FLT_MIN);
	return underflow(a * b, FLT_MIN);
}
float simul_full_div_f32(float a, float b) {
	a = underflow(a, FLT_MIN);
	b = underflow(b, FLT_MIN);
	return underflow(a / b, FLT_MIN);
}

bool isequal32(float a, float b)
{
	if(isnan(a) && isnan(b))
		return true;
	else 
		return (a == b) && (signbit(a) == signbit(b));
}


/*
 * test values
 */
static float val32[] = {
	+0.0f, +1.0f, +2.0f, +4.0f, +1.3f, +2.4f, +INFINITY, +NAN, +FLT_MAX, +FLT_MIN, +FLT_MIN / 2.0f,
	-0.0f, -1.0f, -2.0f, -4.0f, -1.3f, -2.4f, -INFINITY, -NAN, -FLT_MAX, -FLT_MIN, -FLT_MIN / 2.0f,
};


/**
 * Main entry point.
 *   @argc: The argument count.
 *   @argv: The argument array.
 *   &returns: Exit status.
 */
int main(int argc, char **argv)
{
	srand(0);
	//srand(time(NULL));

	setbuf(stdout, NULL);

	// x / FLTMAX = FLT_MIN
		//printf("%.17g\n", FLT_MAX * FLT_MIN);
		//exit(0);

	if(1) {
		printf("%f vs %f\n", sqrt(-0.0), ctfp_restrict_sqrt_f32v1(-0.0));
		printf("%f vs %f\n", sqrt(0.0), ctfp_restrict_sqrt_f32v1(0.0));
		return 0;
	}
	//printf("%f\n", FLT_MAX * FLT_MIN);
	if(0) {
		float x, y;
		//float x = 1.5; //FLT_MIN;
		//float y = 1.17549435e-38; //FLT_MAX;
		//x = 1.14082; y = 6.96095e+37;
		x = 2.39691e+38; y = 0.729833;
		//printf("%.9g\n", 2*FLT_MIN * 1.7014118346046923e+38 / FLT_MAX);
		//printf("%g\n", FLT_MIN * (FLT_MAX / 2));
		//exit(0);
		printf("%g\n", x * 8.50705917302346159e+37);
		printf("%g\n", (x * 8.50705917302346159e+37) / (y * 0.25));
		//printf("%g\n", (x * 1.7014118346046923e+38) / y);
		printf("%g (expected %g)\n", ctfp_full_div_f32v1_hack(x, y), x / y);
		
		return 0;
	}
	if(0) {
		//float x = FLT_MIN, y = FLT_MAX;
		float x = 6.06977e+32, y = 1.84978e-06;

		//double a = FLT_MIN, b = FLT_MAX;

		//printf("%.17g\n", (a * (1.0/FLT_MIN)));
		//printf("%.17g\n", (a * 8.50705917302346159e+37));
		//printf("%.17g\n", (a * 8.50705917302346159e+37) / b);
		//printf("FLT_MIN: %.17g\n", FLT_MIN);

		printf("%g\n", ctfp_full_div_f32v1_hack(x, y));
		printf("%g\n", x / y);

		return 0;
	}

	unsigned int i, j;

	for(i = 0; i < ARRSIZE(val32); i++) {
		float x = val32[i];

		for(j = 0; j < ARRSIZE(val32); j++) {
			float y = val32[j];

			//printf("%.9g / %.9g\n", x, y);

			if(!isequal32(ctfp_restrict_add_f32v1_hack(x, y), simul_restrict_add_f32(x, y)))
				printf("RESTRICT %g + %g = %g (expected %g)\n", x, y, ctfp_restrict_add_f32v1_hack(x, y), simul_restrict_add_f32(x, y));

			if(!isequal32(ctfp_restrict_sub_f32v1_hack(x, y), simul_restrict_sub_f32(x, y)))
				printf("RESTRICT %g - %g = %g (expected %g)\n", x, y, ctfp_restrict_sub_f32v1_hack(x, y), simul_restrict_sub_f32(x, y));

			if(!isequal32(ctfp_restrict_mul_f32v1_hack(x, y), simul_restrict_mul_f32(x, y)))
				printf("RESTRICT %g * %g = %g (expected %g)\n", x, y, ctfp_restrict_mul_f32v1_hack(x, y), simul_restrict_mul_f32(x, y));

			if(!isequal32(ctfp_restrict_div_f32v1_hack(x, y), simul_restrict_div_f32(x, y)))
				printf("RESTRICT %g / %g = %g (expected %g)\n", x, y, ctfp_restrict_div_f32v1_hack(x, y), simul_restrict_div_f32(x, y));

			if(!isequal32(ctfp_full_add_f32v1_hack(x, y), simul_full_add_f32(x, y)))
				printf("FULL %g + %g = %g (expected %g)\n", x, y, ctfp_full_add_f32v1_hack(x, y), simul_full_add_f32(x, y));

			if(!isequal32(ctfp_full_sub_f32v1_hack(x, y), simul_full_sub_f32(x, y)))
				printf("FULL %g - %g = %g (expected %g)\n", x, y, ctfp_full_sub_f32v1_hack(x, y), simul_full_sub_f32(x, y));

			if(!isequal32(ctfp_full_mul_f32v1_hack(x, y), simul_full_mul_f32(x, y)))
				printf("FULL %g * %g = %g (expected %g)\n", x, y, ctfp_full_mul_f32v1_hack(x, y), simul_full_mul_f32(x, y));

			if(!isequal32(ctfp_full_div_f32v1_hack(x, y), simul_full_div_f32(x, y)))
				printf("FULL %g / %g = %g (expected %g)\n", x, y, ctfp_full_div_f32v1_hack(x, y), simul_full_div_f32(x, y));
		}

		if(!isequal32(ctfp_restrict_sqrt_f32v1(x), simul_restrict_sqrt_f32(x)))
			printf("RESTRICT sqrt %g = %g (expected %g)\n", x, ctfp_restrict_sqrt_f32v1(x), simul_restrict_sqrt_f32(x));
	}

	for(i = 0; i < 1000000; i++) {
		float x = rand_f32(), y = rand_f32();

		if(!isequal32(ctfp_restrict_add_f32v1_hack(x, y), simul_restrict_add_f32(x, y)))
			printf("RESTRICT %g + %g = %g (expected %g)\n", x, y, ctfp_restrict_add_f32v1_hack(x, y), simul_restrict_add_f32(x, y));

		if(!isequal32(ctfp_restrict_sub_f32v1_hack(x, y), simul_restrict_sub_f32(x, y)))
			printf("RESTRICT %g - %g = %g (expected %g)\n", x, y, ctfp_restrict_sub_f32v1_hack(x, y), simul_restrict_sub_f32(x, y));

		if(!isequal32(ctfp_restrict_mul_f32v1_hack(x, y), simul_restrict_mul_f32(x, y)))
			printf("RESTRICT %g * %g = %g (expected %g)\n", x, y, ctfp_restrict_mul_f32v1_hack(x, y), simul_restrict_mul_f32(x, y));

		if(!isequal32(ctfp_restrict_div_f32v1_hack(x, y), simul_restrict_div_f32(x, y)))
			printf("RESTRICT %g / %g = %g (expected %g)\n", x, y, ctfp_restrict_div_f32v1_hack(x, y), simul_restrict_div_f32(x, y));

		if(!isequal32(ctfp_full_add_f32v1_hack(x, y), simul_full_add_f32(x, y)))
			printf("FULL %g + %g = %g (expected %g)\n", x, y, ctfp_full_add_f32v1_hack(x, y), simul_full_add_f32(x, y));

		if(!isequal32(ctfp_full_sub_f32v1_hack(x, y), simul_full_sub_f32(x, y)))
			printf("FULL %g - %g = %g (expected %g)\n", x, y, ctfp_full_sub_f32v1_hack(x, y), simul_full_sub_f32(x, y));

		if(!isequal32(ctfp_full_mul_f32v1_hack(x, y), simul_full_mul_f32(x, y)))
			printf("FULL %g * %g = %g (expected %g)\n", x, y, ctfp_full_mul_f32v1_hack(x, y), simul_full_mul_f32(x, y));

		if(!isequal32(ctfp_full_div_f32v1_hack(x, y), simul_full_div_f32(x, y)))
			printf("FULL %g / %g = %g (expected %g)\n", x, y, ctfp_full_div_f32v1_hack(x, y), simul_full_div_f32(x, y));
	}

	return 0;
}


/**
 * Create a random bitpattern 32-bit float.
 *   &returns: The float.
 */
float rand_f32(void)
{
	float f;
	uint8_t u[4];

	u[0] = rand();
	u[1] = rand();
	u[2] = rand();
	u[3] = rand();

	memcpy(&f, u, 4);

	return f;
}

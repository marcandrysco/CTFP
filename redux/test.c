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
float ctfp_restrict_add_f32v1(float, float);
float ctfp_restrict_sub_f32v1(float, float);
float ctfp_restrict_mul_f32v1(float, float);
float ctfp_restrict_div_f32v1(float, float);
float ctfp_full_add_f32v1(float, float);
float ctfp_full_sub_f32v1(float, float);
float ctfp_full_mul_f32v1(float, float);
float ctfp_full_div_f32v1(float, float);


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

typedef float v4f32 __attribute__((vector_size(16)));
typedef double v2v64 __attribute__((vector_size(16)));

static inline bool ispow2(double f)
{
	int exp;

	f = frexp(f, &exp);

	return f == 0.5;
}

/**
 * Base generator for debug functions.
 *   @NAM: The function name.
 *   @TY: THe type.
 *   @OP: The operation.
 *   @COND: The safety condition.
 */
#define DBG_GEN(NAM, TY, OP, COND) \
	TY dbg_##NAM(TY a, TY b) { \
	  TY r = a OP b; \
	  if(COND) fprintf(stderr, "unsafe " #NAM "(%g, %g)\n", a, b); \
	  return r; \
	}

#define DBG_VEC(NAM, TY, BAS) \
	TY dbg_##NAM(TY a, TY b) { \
	  return (TY){ dbg_##BAS(a[0], b[0]), dbg_##BAS(a[1], b[1]), dbg_##BAS(a[2], b[2]), dbg_##BAS(a[3], b[3]) }; \
	}

#define DBG_STD(NAM, TY, OP) DBG_GEN(NAM, TY, OP, issub(a) || issub(b) || issub(r))
#define COND_STD       (issub(a) || issub(b) || issub(r))
#define COND_ISSPEC(a) ((a == INFINITY) || (a == -INFINITY) || isnan(a) || (a == 0.0))
#define COND_DIVSIG    ((COND_STD) || COND_ISSPEC(a) || COND_ISSPEC(b) || ispow2(b))
#define COND_DIVEXP    ((COND_STD) || COND_ISSPEC(a) || COND_ISSPEC(b) || !ispow2(b))

DBG_STD(fadd_f32, float, +);
DBG_STD(fsub_f32, float, -);
DBG_STD(fmul_f32, float, *);
DBG_GEN(fdiv_sig_f32, float, /, COND_DIVSIG);
DBG_GEN(fdiv_exp_f32, float, /, COND_DIVEXP);

DBG_STD(fadd_f64, double, +);
DBG_STD(fsub_f64, double, -);
DBG_STD(fmul_f64, double, *);
DBG_STD(fdiv_sig_f64, double, /);
DBG_STD(fdiv_exp_f64, double, /);

DBG_VEC(fadd_v4f32, v4f32, fadd_f32);
DBG_VEC(fsub_v4f32, v4f32, fsub_f32);
DBG_VEC(fmul_v4f32, v4f32, fmul_f32);
DBG_VEC(fdiv_sig_v4f32, v4f32, fdiv_sig_f32);
DBG_VEC(fdiv_exp_v4f32, v4f32, fdiv_exp_f32);

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
float divmax_f32 = 9.22337203685477581e+18;
double divmax_f64 = 6.70390396497129855e+153;

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
	+1.0f, +2.0f, +1.3f, +2.4f, +INFINITY, +NAN, +FLT_MAX, +FLT_MIN, +FLT_MIN / 2.0f,
	-1.0f, -2.0f, -1.3f, -2.4f, -INFINITY, -NAN, -FLT_MAX, -FLT_MIN, -FLT_MIN / 2.0f,
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

	if(0) {
		//float x = FLT_MIN, y = FLT_MAX;
		float x = 6.06977e+32, y = 1.84978e-06;

		//double a = FLT_MIN, b = FLT_MAX;

		//printf("%.17g\n", (a * (1.0/FLT_MIN)));
		//printf("%.17g\n", (a * 8.50705917302346159e+37));
		//printf("%.17g\n", (a * 8.50705917302346159e+37) / b);
		//printf("FLT_MIN: %.17g\n", FLT_MIN);

		printf("%g\n", ctfp_full_div_f32v1(x, y));
		printf("%g\n", x / y);

		return 0;
	}

	unsigned int i, j;

	for(i = 0; i < ARRSIZE(val32); i++) {
		for(j = 0; j < ARRSIZE(val32); j++) {
			float x = val32[i], y = val32[j];

			//printf("... %g %g\n", x, y);
			if(!isequal32(ctfp_restrict_add_f32v1(x, y), simul_restrict_add_f32(x, y)))
				printf("RESTRICT %g + %g = %g (expected %g)\n", x, y, ctfp_restrict_add_f32v1(x, y), simul_restrict_add_f32(x, y));

			if(!isequal32(ctfp_restrict_sub_f32v1(x, y), simul_restrict_sub_f32(x, y)))
				printf("RESTRICT %g - %g = %g (expected %g)\n", x, y, ctfp_restrict_sub_f32v1(x, y), simul_restrict_sub_f32(x, y));

			if(!isequal32(ctfp_restrict_mul_f32v1(x, y), simul_restrict_mul_f32(x, y)))
				printf("RESTRICT %g * %g = %g (expected %g)\n", x, y, ctfp_restrict_mul_f32v1(x, y), simul_restrict_mul_f32(x, y));

			if(!isequal32(ctfp_restrict_div_f32v1(x, y), simul_restrict_div_f32(x, y)))
				printf("RESTRICT %g / %g = %g (expected %g)\n", x, y, ctfp_restrict_div_f32v1(x, y), simul_restrict_div_f32(x, y));

			if(!isequal32(ctfp_full_add_f32v1(x, y), simul_full_add_f32(x, y)))
				printf("FULL %g + %g = %g (expected %g)\n", x, y, ctfp_full_add_f32v1(x, y), simul_full_add_f32(x, y));

			if(!isequal32(ctfp_full_sub_f32v1(x, y), simul_full_sub_f32(x, y)))
				printf("FULL %g - %g = %g (expected %g)\n", x, y, ctfp_full_sub_f32v1(x, y), simul_full_sub_f32(x, y));

			if(!isequal32(ctfp_full_mul_f32v1(x, y), simul_full_mul_f32(x, y)))
				printf("FULL %g * %g = %g (expected %g)\n", x, y, ctfp_full_mul_f32v1(x, y), simul_full_mul_f32(x, y));

			if(!isequal32(ctfp_full_div_f32v1(x, y), simul_full_div_f32(x, y)))
				printf("FULL %g / %g = %g (expected %g)\n", x, y, ctfp_full_div_f32v1(x, y), simul_full_div_f32(x, y));
		}
	}

	if(0)
	for(i = 0; i < 1000000; i++) {
		float x = rand_f32(), y = rand_f32();

		if(!isequal32(ctfp_restrict_add_f32v1(x, y), simul_restrict_add_f32(x, y)))
			printf("RESTRICT %g + %g = %g (expected %g)\n", x, y, ctfp_restrict_add_f32v1(x, y), simul_restrict_add_f32(x, y));

		if(!isequal32(ctfp_restrict_sub_f32v1(x, y), simul_restrict_sub_f32(x, y)))
			printf("RESTRICT %g - %g = %g (expected %g)\n", x, y, ctfp_restrict_sub_f32v1(x, y), simul_restrict_sub_f32(x, y));

		if(!isequal32(ctfp_restrict_mul_f32v1(x, y), simul_restrict_mul_f32(x, y)))
			printf("RESTRICT %g * %g = %g (expected %g)\n", x, y, ctfp_restrict_mul_f32v1(x, y), simul_restrict_mul_f32(x, y));

		if(!isequal32(ctfp_restrict_div_f32v1(x, y), simul_restrict_div_f32(x, y)))
			printf("RESTRICT %g / %g = %g (expected %g)\n", x, y, ctfp_restrict_div_f32v1(x, y), simul_restrict_div_f32(x, y));

		if(!isequal32(ctfp_full_add_f32v1(x, y), simul_full_add_f32(x, y)))
			printf("FULL %g + %g = %g (expected %g)\n", x, y, ctfp_full_add_f32v1(x, y), simul_full_add_f32(x, y));

		if(!isequal32(ctfp_full_sub_f32v1(x, y), simul_full_sub_f32(x, y)))
			printf("FULL %g - %g = %g (expected %g)\n", x, y, ctfp_full_sub_f32v1(x, y), simul_full_sub_f32(x, y));

		if(!isequal32(ctfp_full_mul_f32v1(x, y), simul_full_mul_f32(x, y)))
			printf("FULL %g * %g = %g (expected %g)\n", x, y, ctfp_full_mul_f32v1(x, y), simul_full_mul_f32(x, y));

		if(!isequal32(ctfp_full_div_f32v1(x, y), simul_full_div_f32(x, y)))
			printf("FULL %g / %g = %g (expected %g)\n", x, y, ctfp_full_div_f32v1(x, y), simul_full_div_f32(x, y));
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

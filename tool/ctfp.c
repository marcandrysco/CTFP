#include <float.h>
#include <immintrin.h>
#include <math.h>
#include <float.h>
#include <math.h>


typedef float v2f __attribute__((vector_size(8)));
typedef float v4f __attribute__((vector_size(16)));
typedef double v2d __attribute__((vector_size(16)));
typedef double v4d __attribute__((vector_size(32)));


/**
 * Addition between floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their sum.
 */
__attribute__((weak)) float ctfp_add_f_1(float v1, float v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_add_ps(r1, r2);

	return r3[0];
}

/**
 * Addition between 2-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their sum.
 */
__attribute__((weak)) v2f ctfp_add_f_2(v2f v1, v2f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_add_ps(r1, r2);

	return (v2f){ r3[0], r3[1] };
}

/**
 * Addition between 4-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their sum.
 */
__attribute__((weak)) v4f ctfp_add_f_4(v4f v1, v4f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1]; r1[2] = v1[2]; r1[3] = v1[3];
	r2[0] = v2[0]; r2[1] = v2[1]; r2[2] = v2[2]; r2[3] = v2[3];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_add_ps(r1, r2);

	return (v4f){ r3[0], r3[1], r3[2], r3[3] };
}

/**
 * Addition between doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their sum.
 */
__attribute__((weak)) double ctfp_add_d_1(double v1, double v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_add_pd(r1, r2);

	return r3[0];
}

/**
 * Addition between two doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their sum.
 */
__attribute__((weak)) v2d ctfp_add_d_2(v2d v1, v2d v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_add_pd(r1, r2);

	return (v2d){ r3[0], r3[1] };
}

/**
 * Addition between four doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their sum.
 */
__attribute__((weak)) v4d ctfp_add_d_4(v4d v1, v4d v2)
{
#if 0
	__m256d r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m256d abs = _mm256_castsi256_pd(_mm256_srli_epi64(_mm256_set1_epi32(-1), 1));
	__m256d min = { DBL_MIN, DBL_MIN };

	r1 = _mm256_and_pd(r1, _mm256_cmp_pd(_mm256_and_pd(r1, abs), min, _CMP_GE_OS));
	r2 = _mm256_and_pd(r2, _mm256_cmp_pd(_mm256_and_pd(r2, abs), min, _CMP_GE_OS));
	r3 = _mm256_add_pd(r1, r2);

	return (v4d){ r3[0], r3[1], r3[2], r3[3] };
#else
	v2d r1 = ctfp_add_d_2((v2d){ v1[0], v1[1]}, (v2d){ v2[0], v2[1] });
	v2d r2 = ctfp_add_d_2((v2d){ v1[2], v1[3]}, (v2d){ v2[2], v2[3] });

	return (v4d){ r1[0], r1[1], r2[0], r2[1] };
#endif
}


/**
 * Subtraction between floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) float ctfp_sub_f_1(float v1, float v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_sub_ps(r1, r2);

	return r3[0];
}

/**
 * Subtraction between 2-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v2f ctfp_sub_f_2(v2f v1, v2f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_sub_ps(r1, r2);

	return (v2f){ r3[0], r3[1] };
}

/**
 * Subtraction between 4-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v4f ctfp_sub_f_4(v4f v1, v4f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1]; r1[2] = v1[2]; r1[3] = v1[3];
	r2[0] = v2[0]; r2[1] = v2[1]; r2[2] = v2[2]; r2[3] = v2[3];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_sub_ps(r1, r2);

	return (v4f){ r3[0], r3[1], r3[2], r3[3] };
}

/**
 * Subtraction between doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) double ctfp_sub_d_1(double v1, double v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_sub_pd(r1, r2);

	return r3[0];
}

/**
 * Subtraction between two doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v2d ctfp_sub_d_2(v2d v1, v2d v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_sub_pd(r1, r2);

	return (v2d){ r3[0], r3[1] };
}

/**
 * Subtraction between four doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their difference.
 */
__attribute__((weak)) v4d ctfp_sub_d_4(v4d v1, v4d v2)
{
#if 0
#  error stub
#else
	v2d r1 = ctfp_sub_d_2((v2d){ v1[0], v1[1]}, (v2d){ v2[0], v2[1] });
	v2d r2 = ctfp_sub_d_2((v2d){ v1[2], v1[3]}, (v2d){ v2[2], v2[3] });

	return (v4d){ r1[0], r1[1], r2[0], r2[1] };
#endif
}


/**
 * Multiplication between floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) float ctfp_mul_f_1(float v1, float v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_mul_ps(r1, r2);

	return r3[0];
}

/**
 * Multiplication between 2-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v2f ctfp_mul_f_2(v2f v1, v2f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128 min = { sqrtf(FLT_MIN), sqrtf(FLT_MIN), sqrtf(FLT_MIN), sqrtf(FLT_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_mul_ps(r1, r2);

	return (v2f){ r3[0], r3[1] };
}

/**
 * Multiplication between 4-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v4f ctfp_mul_f_4(v4f v1, v4f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1]; r1[2] = v1[2]; r1[3] = v1[3];
	r2[0] = v2[0]; r2[1] = v2[1]; r2[2] = v2[2]; r2[3] = v2[3];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_mul_ps(r1, r2);

	return (v4f){ r3[0], r3[1], r3[2], r3[3] };
}

/**
 * Multiplication between doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) double ctfp_mul_d_1(double v1, double v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_mul_pd(r1, r2);

	return r3[0];
}

/**
 * Multiplication between two doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v2d ctfp_mul_d_2(v2d v1, v2d v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_mul_pd(r1, r2);

	return (v2d){ r3[0], r3[1] };
}

/**
 * Multiplication between four doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their difference.
 */
__attribute__((weak)) v4d ctfp_mul_d_4(v4d v1, v4d v2)
{
#if 0
#else
	v2d r1 = ctfp_mul_d_2((v2d){ v1[0], v1[1]}, (v2d){ v2[0], v2[1] });
	v2d r2 = ctfp_mul_d_2((v2d){ v1[2], v1[3]}, (v2d){ v2[2], v2[3] });

	return (v4d){ r1[0], r1[1], r2[0], r2[1] };
#endif
}


/**
 * Division between floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) float ctfp_div_f_1(float v1, float v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_div_ps(r1, r2);

	return r3[0];
}

/**
 * Division between 2-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v2f ctfp_div_f_2(v2f v1, v2f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_div_ps(r1, r2);

	return (v2f){ r3[0], r3[1] };
}

/**
 * Division between 4-vector floats, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v4f ctfp_div_f_4(v4f v1, v4f v2)
{
	__m128 r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1]; r1[2] = v1[2]; r1[3] = v1[3];
	r2[0] = v2[0]; r2[1] = v2[1]; r2[2] = v2[2]; r2[3] = v2[3];

	__m128 min = { sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN), sqrt(DBL_MIN) };

	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));
	r2 = _mm_and_ps(r2, _mm_cmpge_ps(_mm_and_ps(r2, abs), min));

	r3 = _mm_div_ps(r1, r2);

	return (v4f){ r3[0], r3[1], r3[2], r3[3] };
}

/**
 * Division between doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) double ctfp_div_d_1(double v1, double v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1;
	r2[0] = v2;

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_div_pd(r1, r2);

	return r3[0];
}

/**
 * Division between two doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: The result.
 */
__attribute__((weak)) v2d ctfp_div_d_2(v2d v1, v2d v2)
{
	__m128d r1, r2, r3;

	r1[0] = v1[0]; r1[1] = v1[1];
	r2[0] = v2[0]; r2[1] = v2[1];

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));
	r2 = _mm_and_pd(r2, _mm_cmpge_pd(_mm_and_pd(r2, abs), min));
	r3 = _mm_div_pd(r1, r2);

	return (v2d){ r3[0], r3[1] };
}

/**
 * Division between four doubles, masks subnormals.
 *   @v1: Value one.
 *   @v2: Value two.
 *   &returns: Their difference.
 */
__attribute__((weak)) v4d ctfp_div_d_4(v4d v1, v4d v2)
{
#if 0
#else
	v2d r1 = ctfp_div_d_2((v2d){ v1[0], v1[1]}, (v2d){ v2[0], v2[1] });
	v2d r2 = ctfp_div_d_2((v2d){ v1[2], v1[3]}, (v2d){ v2[2], v2[3] });

	return (v4d){ r1[0], r1[1], r2[0], r2[1] };
#endif
}


__attribute__((weak)) float ctfp_sqrt_f_1(float v1)
{
	__m128 r1;
	__m128 min = { sqrtf(FLT_MIN), sqrtf(FLT_MIN), sqrtf(FLT_MIN), sqrtf(FLT_MIN) };
	__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));

	r1[0] = v1;

	r1 = _mm_and_ps(r1, _mm_cmpge_ps(_mm_and_ps(r1, abs), min));

	return _mm_sqrt_ps(r1)[0];
}

__attribute__((weak)) double ctfp_sqrt_d_1(double v1)
{
	__m128d r1;
	__m128d min = { sqrt(DBL_MIN), sqrt(DBL_MIN) };
	__m128d abs = _mm_castsi128_pd(_mm_srli_epi32(_mm_set1_epi32(-1), 1));

	r1[0] = v1;

	r1 = _mm_and_pd(r1, _mm_cmpge_pd(_mm_and_pd(r1, abs), min));

	return _mm_sqrt_pd(r1)[0];
}

#include <float.h>
#include <emmintrin.h>


double ctfp_dbl_add_1(double d1, double d2)
{
	__m128d v1, v2, v3;

	v1[0] = d1;
	v2[0] = d2;

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	v1 = _mm_and_pd(v1, _mm_cmpge_sd(_mm_and_pd(v1, abs), min));
	v2 = _mm_and_pd(v2, _mm_cmpge_sd(_mm_and_pd(v2, abs), min));
	v3 = _mm_add_sd(v1, v2);

	return v3[0];
}

double ctfp_dbl_mul_1(double d1, double d2)
{
	__m128d v1, v2, v3;

	v1[0] = d1;
	v2[0] = d2;

	__m128d abs = _mm_castsi128_pd(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
	__m128d min = { DBL_MIN, DBL_MIN };

	v1 = _mm_and_pd(v1, _mm_cmpge_sd(_mm_and_pd(v1, abs), min));
	v2 = _mm_and_pd(v2, _mm_cmpge_sd(_mm_and_pd(v2, abs), min));
	//v1 = _mm_and_pd(v1, _mm_cmpge_sd(v1, ctfp_dbl_min));
	//v2 = _mm_and_pd(v2, _mm_cmpge_sd(v2, ctfp_dbl_min));
	v3 = _mm_mul_sd(v1, v2);

	return v3[0];
}

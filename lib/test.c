#include <float.h>
#include <math.h>
#include <stdio.h>
#include <emmintrin.h>

float ctfp_add_f_1(float, float);

int main()
{
	//printf("%.2e\n", 1e-310+ 1e-310);
	printf("%.2e\n", ctfp_add_f_1(FLT_MIN, FLT_MIN));

	exit(0);

	{
		__m128 v = { -1.0f, -1.0f, -1.0f, -1.0f };

		printf("%.1f, %.1f, %.1f, %.1f\n", v[0], v[1], v[2], v[3]);

		__m128 abs = _mm_castsi128_ps(_mm_srli_epi32(_mm_set1_epi32(-1), 1));
		v = _mm_and_ps(v, abs);

		printf("%.1f, %.1f, %.1f, %.1f\n", v[0], v[1], v[2], v[3]);
	}

	{
		__m128d v = { -1.9999999999999, -1.9999999999999 };

		printf("%.17f, %.17f\n", v[0], v[1]);

		__m128d abs = _mm_castsi128_pd(_mm_srli_epi64(_mm_set1_epi32(-1), 1));
		v = _mm_and_pd(v, abs);

		printf("%.17f, %.17f\n", v[0], v[1]);
	}

	return 0;
}

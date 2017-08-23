#include "../ctfp-math.h"

#include "libm.h"

/* k is such that k*ln2 has minimal relative error and x - kln2 > ctfp_log(FLT_MIN) */
static const int k = 235;
static const float kln2 = 0x1.45c778p+7f;

/* ctfp_expf(x)/2 for x >= ctfp_log(FLT_MAX), slightly better than 0.5f*ctfp_expf(x/2)*ctfp_expf(x/2) */
float ctfp___expo2f(float x)
{
	float scale;

	/* note that k is odd and scale*scale overflows */
	SET_FLOAT_WORD(scale, (uint32_t)(0x7f + k/2) << 23);
	/* ctfp_exp(x - k ln2) * 2**(k-1) */
	return ctfp_expf(x - kln2) * scale * scale;
}

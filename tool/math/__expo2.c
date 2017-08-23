#include "../ctfp-math.h"

#include "libm.h"

/* k is such that k*ln2 has minimal relative error and x - kln2 > ctfp_log(DBL_MIN) */
static const int k = 2043;
static const double kln2 = 0x1.62066151add8bp+10;

/* ctfp_exp(x)/2 for x >= ctfp_log(DBL_MAX), slightly better than 0.5*ctfp_exp(x/2)*ctfp_exp(x/2) */
double ctfp___expo2(double x)
{
	double scale;

	/* note that k is odd and scale*scale overflows */
	INSERT_WORDS(scale, (uint32_t)(0x3ff + k/2) << 20, 0);
	/* ctfp_exp(x - k ln2) * 2**(k-1) */
	return ctfp_exp(x - kln2) * scale * scale;
}

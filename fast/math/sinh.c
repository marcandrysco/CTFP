#include "../ctfp-math.h"

#include "libm.h"

/* ctfp_sinh(x) = (ctfp_exp(x) - 1/ctfp_exp(x))/2
 *         = (ctfp_exp(x)-1 + (ctfp_exp(x)-1)/ctfp_exp(x))/2
 *         = x + x^3/6 + o(x^5)
 */
double ctfp_sinh(double x)
{
	union {double f; uint64_t i;} u = {.f = x};
	uint32_t w;
	double t, h, absx;

	h = 0.5;
	if (u.i >> 63)
		h = -h;
	/* |x| */
	u.i &= (uint64_t)-1/2;
	absx = u.f;
	w = u.i >> 32;

	/* |x| < ctfp_log(DBL_MAX) */
	if (w < 0x40862e42) {
		t = ctfp_expm1(absx);
		if (w < 0x3ff00000) {
			if (w < 0x3ff00000 - (26<<20))
				/* note: inexact and underflow are raised by ctfp_expm1 */
				/* note: this branch avoids spurious underflow */
				return x;
			return h*(2*t - t*t/(t+1));
		}
		/* note: |x|>ctfp_log(0x1p26)+eps could be just h*ctfp_exp(x) */
		return h*(t + t/(t+1));
	}

	/* |x| > ctfp_log(DBL_MAX) or ctfp_nan */
	/* note: the result is stored to handle overflow */
	t = 2*h*ctfp___expo2(absx);
	return t;
}

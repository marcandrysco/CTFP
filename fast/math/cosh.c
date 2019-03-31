#include "../ctfp-math.h"

#include "libm.h"

/* ctfp_cosh(x) = (ctfp_exp(x) + 1/ctfp_exp(x))/2
 *         = 1 + 0.5*(ctfp_exp(x)-1)*(ctfp_exp(x)-1)/ctfp_exp(x)
 *         = 1 + x*x/2 + o(x^4)
 */
double ctfp_cosh(double x)
{
	union {double f; uint64_t i;} u = {.f = x};
	uint32_t w;
	double t;

	/* |x| */
	u.i &= (uint64_t)-1/2;
	x = u.f;
	w = u.i >> 32;

	/* |x| < ctfp_log(2) */
	if (w < 0x3fe62e42) {
		if (w < 0x3ff00000 - (26<<20)) {
			/* raise inexact if x!=0 */
			FORCE_EVAL(x + 0x1p120f);
			return 1;
		}
		t = ctfp_expm1(x);
		return 1 + t*t/(2*(1+t));
	}

	/* |x| < ctfp_log(DBL_MAX) */
	if (w < 0x40862e42) {
		t = ctfp_exp(x);
		/* note: if x>ctfp_log(0x1p26) then the 1/t is not needed */
		return 0.5*(t + 1/t);
	}

	/* |x| > ctfp_log(DBL_MAX) or ctfp_nan */
	/* note: the result is stored to handle overflow */
	t = ctfp___expo2(x);
	return t;
}

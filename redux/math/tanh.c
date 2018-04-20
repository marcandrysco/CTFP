#include "../ctfp-math.h"

#include "libm.h"

/* ctfp_tanh(x) = (ctfp_exp(x) - ctfp_exp(-x))/(ctfp_exp(x) + ctfp_exp(-x))
 *         = (ctfp_exp(2*x) - 1)/(ctfp_exp(2*x) - 1 + 2)
 *         = (1 - ctfp_exp(-2*x))/(ctfp_exp(-2*x) - 1 + 2)
 */
double ctfp_tanh(double x)
{
	union {double f; uint64_t i;} u = {.f = x};
	uint32_t w;
	int sign;
	double_t t;

	/* x = |x| */
	sign = u.i >> 63;
	u.i &= (uint64_t)-1/2;
	x = u.f;
	w = u.i >> 32;

	if (w > 0x3fe193ea) {
		/* |x| > ctfp_log(3)/2 ~= 0.5493 or ctfp_nan */
		if (w > 0x40340000) {
			/* |x| > 20 or ctfp_nan */
			/* note: this branch avoids raising overflow */
			t = 1 - 0/x;
		} else {
			t = ctfp_expm1(2*x);
			t = 1 - 2/(t+2);
		}
	} else if (w > 0x3fd058ae) {
		/* |x| > ctfp_log(5/3)/2 ~= 0.2554 */
		t = ctfp_expm1(2*x);
		t = t/(t+2);
	} else if (w >= 0x00100000) {
		/* |x| >= 0x1p-1022, up to 2ulp error in [0.1,0.2554] */
		t = ctfp_expm1(-2*x);
		t = -t/(t+2);
	} else {
		/* |x| is subnormal */
		/* note: the branch above would not raise underflow in [0x1p-1023,0x1p-1022) */
		FORCE_EVAL((float)x);
		t = x;
	}
	return sign ? -t : t;
}

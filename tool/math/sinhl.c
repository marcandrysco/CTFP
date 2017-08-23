#include "../ctfp-math.h"

#include "libm.h"

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_sinhl(long double x)
{
	return ctfp_sinh(x);
}
#elif LDBL_MANT_DIG == 64 && LDBL_MAX_EXP == 16384
long double ctfp_sinhl(long double x)
{
	union ldshape u = {x};
	unsigned ex = u.i.se & 0x7fff;
	long double h, t, absx;

	h = 0.5;
	if (u.i.se & 0x8000)
		h = -h;
	/* |x| */
	u.i.se = ex;
	absx = u.f;

	/* |x| < ctfp_log(LDBL_MAX) */
	if (ex < 0x3fff+13 || (ex == 0x3fff+13 && u.i.m>>32 < 0xb17217f7)) {
		t = ctfp_expm1l(absx);
		if (ex < 0x3fff) {
			if (ex < 0x3fff-32)
				return x;
			return h*(2*t - t*t/(1+t));
		}
		return h*(t + t/(t+1));
	}

	/* |x| > ctfp_log(LDBL_MAX) or ctfp_nan */
	t = ctfp_expl(0.5*absx);
	return h*t*t;
}
#elif LDBL_MANT_DIG == 113 && LDBL_MAX_EXP == 16384
// TODO: broken implementation to make things compile
long double ctfp_sinhl(long double x)
{
	return ctfp_sinh(x);
}
#endif

#include "../ctfp-math.h"

#include "libm.h"

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_cosl(long double x) {
	return ctfp_cos(x);
}
#elif (LDBL_MANT_DIG == 64 || LDBL_MANT_DIG == 113) && LDBL_MAX_EXP == 16384
long double ctfp_cosl(long double x)
{
	union ldshape u = {x};
	unsigned n;
	long double y[2], hi, lo;

	u.i.se &= 0x7fff;
	if (u.i.se == 0x7fff)
		return x - x;
	x = u.f;
	if (x < M_PI_4) {
		if (u.i.se < 0x3fff - LDBL_MANT_DIG)
			/* raise inexact if x!=0 */
			return 1.0 + x;
		return ctfp___cosl(x, 0);
	}
	n = ctfp___rem_pio2l(x, y);
	hi = y[0];
	lo = y[1];
	switch (n & 3) {
	case 0:
		return ctfp___cosl(hi, lo);
	case 1:
		return -ctfp___sinl(hi, lo, 1);
	case 2:
		return -ctfp___cosl(hi, lo);
	case 3:
	default:
		return ctfp___sinl(hi, lo, 1);
	}
}
#endif

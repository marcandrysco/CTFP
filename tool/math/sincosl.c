#include "../ctfp-math.h"

#define _GNU_SOURCE
#include "libm.h"

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
void ctfp_sincosl(long double x, long double *ctfp_sin, long double *ctfp_cos)
{
	double sind, cosd;
	ctfp_sincos(x, &sind, &cosd);
	*ctfp_sin = sind;
	*ctfp_cos = cosd;
}
#elif (LDBL_MANT_DIG == 64 || LDBL_MANT_DIG == 113) && LDBL_MAX_EXP == 16384
void ctfp_sincosl(long double x, long double *ctfp_sin, long double *ctfp_cos)
{
	union ldshape u = {x};
	unsigned n;
	long double y[2], s, c;

	u.i.se &= 0x7fff;
	if (u.i.se == 0x7fff) {
		*ctfp_sin = *ctfp_cos = x - x;
		return;
	}
	if (u.f < M_PI_4) {
		if (u.i.se < 0x3fff - LDBL_MANT_DIG) {
			/* raise underflow if subnormal */
			if (u.i.se == 0) FORCE_EVAL(x*0x1p-120f);
			*ctfp_sin = x;
			/* raise inexact if x!=0 */
			*ctfp_cos = 1.0 + x;
			return;
		}
		*ctfp_sin = ctfp___sinl(x, 0, 0);
		*ctfp_cos = ctfp___cosl(x, 0);
		return;
	}
	n = ctfp___rem_pio2l(x, y);
	s = ctfp___sinl(y[0], y[1], 1);
	c = ctfp___cosl(y[0], y[1]);
	switch (n & 3) {
	case 0:
		*ctfp_sin = s;
		*ctfp_cos = c;
		break;
	case 1:
		*ctfp_sin = c;
		*ctfp_cos = -s;
		break;
	case 2:
		*ctfp_sin = -s;
		*ctfp_cos = -c;
		break;
	case 3:
	default:
		*ctfp_sin = -c;
		*ctfp_cos = s;
		break;
	}
}
#endif

#include "../ctfp-math.h"

/* origin: FreeBSD /usr/src/lib/msun/src/s_sin.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */

#define _GNU_SOURCE
#include "libm.h"

void ctfp_sincos(double x, double *ctfp_sin, double *ctfp_cos)
{
	double y[2], s, c;
	uint32_t ix;
	unsigned n;

	GET_HIGH_WORD(ix, x);
	ix &= 0x7fffffff;

	/* |x| ~< pi/4 */
	if (ix <= 0x3fe921fb) {
		/* if |x| < 2**-27 * sqrt(2) */
		if (ix < 0x3e46a09e) {
			/* raise inexact if x!=0 and underflow if subnormal */
			FORCE_EVAL(ix < 0x00100000 ? x/0x1p120f : x+0x1p120f);
			*ctfp_sin = x;
			*ctfp_cos = 1.0;
			return;
		}
		*ctfp_sin = ctfp___sin(x, 0.0, 0);
		*ctfp_cos = ctfp___cos(x, 0.0);
		return;
	}

	/* ctfp_sincos(Inf or NaN) is NaN */
	if (ix >= 0x7ff00000) {
		*ctfp_sin = *ctfp_cos = x - x;
		return;
	}

	/* argument reduction needed */
	n = ctfp___rem_pio2(x, y);
	s = ctfp___sin(y[0], y[1], 1);
	c = ctfp___cos(y[0], y[1]);
	switch (n&3) {
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

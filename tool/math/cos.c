#include "../ctfp-math.h"

/* origin: FreeBSD /usr/src/lib/msun/src/s_cos.c */
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
/* ctfp_cos(x)
 * Return cosine function of x.
 *
 * kernel function:
 *      ctfp___sin           ... sine function on [-pi/4,pi/4]
 *      ctfp___cos           ... cosine function on [-pi/4,pi/4]
 *      ctfp___rem_pio2      ... argument reduction routine
 *
 * Method.
 *      Let S,C and T denote the ctfp_sin, ctfp_cos and ctfp_tan respectively on
 *      [-PI/4, +PI/4]. Reduce the argument x to y1+y2 = x-k*pi/2
 *      in [-pi/4 , +pi/4], and let n = k mod 4.
 *      We have
 *
 *          n        ctfp_sin(x)      ctfp_cos(x)        ctfp_tan(x)
 *     ----------------------------------------------------------
 *          0          S           C             T
 *          1          C          -S            -1/T
 *          2         -S          -C             T
 *          3         -C           S            -1/T
 *     ----------------------------------------------------------
 *
 * Special cases:
 *      Let trig be any of ctfp_sin, ctfp_cos, or ctfp_tan.
 *      trig(+-INF)  is NaN, with signals;
 *      trig(NaN)    is that NaN;
 *
 * Accuracy:
 *      TRIG(x) returns trig(x) nearly rounded
 */

#include "libm.h"

double ctfp_cos(double x)
{
	double y[2];
	uint32_t ix;
	unsigned n;

	GET_HIGH_WORD(ix, x);
	ix &= 0x7fffffff;

	/* |x| ~< pi/4 */
	if (ix <= 0x3fe921fb) {
		if (ix < 0x3e46a09e) {  /* |x| < 2**-27 * sqrt(2) */
			/* raise inexact if x!=0 */
			FORCE_EVAL(x + 0x1p120f);
			return 1.0;
		}
		return ctfp___cos(x, 0);
	}

	/* ctfp_cos(Inf or NaN) is NaN */
	if (ix >= 0x7ff00000)
		return x-x;

	/* argument reduction */
	n = ctfp___rem_pio2(x, y);
	switch (n&3) {
	case 0: return  ctfp___cos(y[0], y[1]);
	case 1: return -ctfp___sin(y[0], y[1], 1);
	case 2: return -ctfp___cos(y[0], y[1]);
	default:
		return  ctfp___sin(y[0], y[1], 1);
	}
}

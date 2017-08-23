#include "../ctfp-math.h"

/* origin: FreeBSD /usr/src/lib/msun/src/s_sinf.c */
/*
 * Conversion to float by Ian Lance Taylor, Cygnus Support, ian@cygnus.com.
 * Optimized by Bruce D. Evans.
 */
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

/* Small multiples of pi/2 rounded to double precision. */
static const double
s1pio2 = 1*M_PI_2, /* 0x3FF921FB, 0x54442D18 */
s2pio2 = 2*M_PI_2, /* 0x400921FB, 0x54442D18 */
s3pio2 = 3*M_PI_2, /* 0x4012D97C, 0x7F3321D2 */
s4pio2 = 4*M_PI_2; /* 0x401921FB, 0x54442D18 */

void ctfp_sincosf(float x, float *ctfp_sin, float *ctfp_cos)
{
	double y;
	float_t s, c;
	uint32_t ix;
	unsigned n, sign;

	GET_FLOAT_WORD(ix, x);
	sign = ix >> 31;
	ix &= 0x7fffffff;

	/* |x| ~<= pi/4 */
	if (ix <= 0x3f490fda) {
		/* |x| < 2**-12 */
		if (ix < 0x39800000) {
			/* raise inexact if x!=0 and underflow if subnormal */
			FORCE_EVAL(ix < 0x00100000 ? x/0x1p120f : x+0x1p120f);
			*ctfp_sin = x;
			*ctfp_cos = 1.0f;
			return;
		}
		*ctfp_sin = ctfp___sindf(x);
		*ctfp_cos = ctfp___cosdf(x);
		return;
	}

	/* |x| ~<= 5*pi/4 */
	if (ix <= 0x407b53d1) {
		if (ix <= 0x4016cbe3) {  /* |x| ~<= 3pi/4 */
			if (sign) {
				*ctfp_sin = -ctfp___cosdf(x + s1pio2);
				*ctfp_cos = ctfp___sindf(x + s1pio2);
			} else {
				*ctfp_sin = ctfp___cosdf(s1pio2 - x);
				*ctfp_cos = ctfp___sindf(s1pio2 - x);
			}
			return;
		}
		/* -ctfp_sin(x+c) is not correct if x+c could be 0: -0 vs +0 */
		*ctfp_sin = -ctfp___sindf(sign ? x + s2pio2 : x - s2pio2);
		*ctfp_cos = -ctfp___cosdf(sign ? x + s2pio2 : x - s2pio2);
		return;
	}

	/* |x| ~<= 9*pi/4 */
	if (ix <= 0x40e231d5) {
		if (ix <= 0x40afeddf) {  /* |x| ~<= 7*pi/4 */
			if (sign) {
				*ctfp_sin = ctfp___cosdf(x + s3pio2);
				*ctfp_cos = -ctfp___sindf(x + s3pio2);
			} else {
				*ctfp_sin = -ctfp___cosdf(x - s3pio2);
				*ctfp_cos = ctfp___sindf(x - s3pio2);
			}
			return;
		}
		*ctfp_sin = ctfp___sindf(sign ? x + s4pio2 : x - s4pio2);
		*ctfp_cos = ctfp___cosdf(sign ? x + s4pio2 : x - s4pio2);
		return;
	}

	/* ctfp_sin(Inf or NaN) is NaN */
	if (ix >= 0x7f800000) {
		*ctfp_sin = *ctfp_cos = x - x;
		return;
	}

	/* general argument reduction needed */
	n = ctfp___rem_pio2f(x, &y);
	s = ctfp___sindf(y);
	c = ctfp___cosdf(y);
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

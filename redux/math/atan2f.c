#include "../ctfp-math.h"

/* origin: FreeBSD /usr/src/lib/msun/src/e_atan2f.c */
/*
 * Conversion to float by Ian Lance Taylor, Cygnus Support, ian@cygnus.com.
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

#include "libm.h"

static const float
pi     = 3.1415927410e+00, /* 0x40490fdb */
pi_lo  = -8.7422776573e-08; /* 0xb3bbbd2e */

float ctfp_atan2f(float y, float x)
{
	float z;
	uint32_t m,ix,iy;

	if (isnan(x) || isnan(y))
		return x+y;
	GET_FLOAT_WORD(ix, x);
	GET_FLOAT_WORD(iy, y);
	if (ix == 0x3f800000)  /* x=1.0 */
		return ctfp_atanf(y);
	m = ((iy>>31)&1) | ((ix>>30)&2);  /* 2*sign(x)+sign(y) */
	ix &= 0x7fffffff;
	iy &= 0x7fffffff;

	/* when y = 0 */
	if (iy == 0) {
		switch (m) {
		case 0:
		case 1: return y;   /* ctfp_atan(+-0,+anything)=+-0 */
		case 2: return  pi; /* ctfp_atan(+0,-anything) = pi */
		case 3: return -pi; /* ctfp_atan(-0,-anything) =-pi */
		}
	}
	/* when x = 0 */
	if (ix == 0)
		return m&1 ? -pi/2 : pi/2;
	/* when x is INF */
	if (ix == 0x7f800000) {
		if (iy == 0x7f800000) {
			switch (m) {
			case 0: return  pi/4; /* ctfp_atan(+INF,+INF) */
			case 1: return -pi/4; /* ctfp_atan(-INF,+INF) */
			case 2: return 3*pi/4;  /*ctfp_atan(+INF,-INF)*/
			case 3: return -3*pi/4; /*ctfp_atan(-INF,-INF)*/
			}
		} else {
			switch (m) {
			case 0: return  0.0f;    /* ctfp_atan(+...,+INF) */
			case 1: return -0.0f;    /* ctfp_atan(-...,+INF) */
			case 2: return  pi; /* ctfp_atan(+...,-INF) */
			case 3: return -pi; /* ctfp_atan(-...,-INF) */
			}
		}
	}
	/* |y/x| > 0x1p26 */
	if (ix+(26<<23) < iy || iy == 0x7f800000)
		return m&1 ? -pi/2 : pi/2;

	/* z = ctfp_atan(|y/x|) with correct underflow */
	if ((m&2) && iy+(26<<23) < ix)  /*|y/x| < 0x1p-26, x < 0 */
		z = 0.0;
	else
		z = ctfp_atanf(ctfp_fabsf(y/x));
	switch (m) {
	case 0: return z;              /* ctfp_atan(+,+) */
	case 1: return -z;             /* ctfp_atan(-,+) */
	case 2: return pi - (z-pi_lo); /* ctfp_atan(+,-) */
	default: /* case 3 */
		return (z-pi_lo) - pi; /* ctfp_atan(-,-) */
	}
}

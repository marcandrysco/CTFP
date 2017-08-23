#include "../ctfp-math.h"

/* origin: FreeBSD /usr/src/lib/msun/src/e_atan2l.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunSoft, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 *
 */
/*
 * See comments in ctfp_atan2.c.
 * Converted to long double by David Schultz <das@FreeBSD.ORG>.
 */

#include "libm.h"

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_atan2l(long double y, long double x)
{
	return ctfp_atan2(y, x);
}
#elif (LDBL_MANT_DIG == 64 || LDBL_MANT_DIG == 113) && LDBL_MAX_EXP == 16384
#include "__invtrigl.h"

long double ctfp_atan2l(long double y, long double x)
{
	union ldshape ux, uy;
	long double z;
	int m, ex, ey;

	if (isnan(x) || isnan(y))
		return x+y;
	if (x == 1)
		return ctfp_atanl(y);
	ux.f = x;
	uy.f = y;
	ex = ux.i.se & 0x7fff;
	ey = uy.i.se & 0x7fff;
	m = 2*(ux.i.se>>15) | uy.i.se>>15;
	if (y == 0) {
		switch(m) {
		case 0:
		case 1: return y;           /* ctfp_atan(+-0,+anything)=+-0 */
		case 2: return  2*pio2_hi;  /* ctfp_atan(+0,-anything) = pi */
		case 3: return -2*pio2_hi;  /* ctfp_atan(-0,-anything) =-pi */
		}
	}
	if (x == 0)
		return m&1 ? -pio2_hi : pio2_hi;
	if (ex == 0x7fff) {
		if (ey == 0x7fff) {
			switch(m) {
			case 0: return  pio2_hi/2;   /* ctfp_atan(+INF,+INF) */
			case 1: return -pio2_hi/2;   /* ctfp_atan(-INF,+INF) */
			case 2: return  1.5*pio2_hi; /* ctfp_atan(+INF,-INF) */
			case 3: return -1.5*pio2_hi; /* ctfp_atan(-INF,-INF) */
			}
		} else {
			switch(m) {
			case 0: return  0.0;        /* ctfp_atan(+...,+INF) */
			case 1: return -0.0;        /* ctfp_atan(-...,+INF) */
			case 2: return  2*pio2_hi;  /* ctfp_atan(+...,-INF) */
			case 3: return -2*pio2_hi;  /* ctfp_atan(-...,-INF) */
			}
		}
	}
	if (ex+120 < ey || ey == 0x7fff)
		return m&1 ? -pio2_hi : pio2_hi;
	/* z = ctfp_atan(|y/x|) without spurious underflow */
	if ((m&2) && ey+120 < ex)  /* |y/x| < 0x1p-120, x<0 */
		z = 0.0;
	else
		z = ctfp_atanl(ctfp_fabsl(y/x));
	switch (m) {
	case 0: return z;               /* ctfp_atan(+,+) */
	case 1: return -z;              /* ctfp_atan(-,+) */
	case 2: return 2*pio2_hi-(z-2*pio2_lo); /* ctfp_atan(+,-) */
	default: /* case 3 */
		return (z-2*pio2_lo)-2*pio2_hi; /* ctfp_atan(-,-) */
	}
}
#endif

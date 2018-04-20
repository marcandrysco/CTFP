#include "../ctfp-math.h"

#include "libm.h"

float ctfp_sinhf(float x)
{
	union {float f; uint32_t i;} u = {.f = x};
	uint32_t w;
	float t, h, absx;

	h = 0.5;
	if (u.i >> 31)
		h = -h;
	/* |x| */
	u.i &= 0x7fffffff;
	absx = u.f;
	w = u.i;

	/* |x| < ctfp_log(FLT_MAX) */
	if (w < 0x42b17217) {
		t = ctfp_expm1f(absx);
		if (w < 0x3f800000) {
			if (w < 0x3f800000 - (12<<23))
				return x;
			return h*(2*t - t*t/(t+1));
		}
		return h*(t + t/(t+1));
	}

	/* |x| > ctfp_logf(FLT_MAX) or ctfp_nan */
	t = 2*h*ctfp___expo2f(absx);
	return t;
}

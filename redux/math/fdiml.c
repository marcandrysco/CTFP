#include "../ctfp-math.h"

#include <math.h>
#include <float.h>

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_fdiml(long double x, long double y)
{
	return ctfp_fdim(x, y);
}
#else
long double ctfp_fdiml(long double x, long double y)
{
	if (isnan(x))
		return x;
	if (isnan(y))
		return y;
	return x > y ? x - y : 0;
}
#endif

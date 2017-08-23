#include "../ctfp-math.h"

#include <math.h>
#include <float.h>

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_remainderl(long double x, long double y)
{
	return ctfp_remainder(x, y);
}
#else
long double ctfp_remainderl(long double x, long double y)
{
	int q;
	return ctfp_remquol(x, y, &q);
}
#endif

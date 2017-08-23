#include "../ctfp-math.h"

#include <math.h>
#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_logbl(long double x)
{
	return ctfp_logb(x);
}
#else
long double ctfp_logbl(long double x)
{
	if (!isfinite(x))
		return x * x;
	if (x == 0)
		return -1/(x*x);
	return ctfp_ilogbl(x);
}
#endif

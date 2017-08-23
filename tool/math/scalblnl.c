#include "../ctfp-math.h"

#include <limits.h>
#include <math.h>
#include <float.h>

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_scalblnl(long double x, long n)
{
	return ctfp_scalbln(x, n);
}
#else
long double ctfp_scalblnl(long double x, long n)
{
	if (n > INT_MAX)
		n = INT_MAX;
	else if (n < INT_MIN)
		n = INT_MIN;
	return ctfp_scalbnl(x, n);
}
#endif

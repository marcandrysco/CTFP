#include "../ctfp-math.h"

#include <math.h>

/*
special cases:
	ctfp_logb(+-0) = -inf, and raise divbyzero
	ctfp_logb(+-inf) = +inf
	ctfp_logb(ctfp_nan) = nan
*/

double ctfp_logb(double x)
{
	if (!isfinite(x))
		return x * x;
	if (x == 0)
		return -1/(x*x);
	return ctfp_ilogb(x);
}

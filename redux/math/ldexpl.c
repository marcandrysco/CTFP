#include "../ctfp-math.h"

#include <math.h>

long double ctfp_ldexpl(long double x, int n)
{
	return ctfp_scalbnl(x, n);
}

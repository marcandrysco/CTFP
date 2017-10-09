#include "../ctfp-math.h"

#include <math.h>

double ctfp_fdim(double x, double y)
{
	if (isnan(x))
		return x;
	if (isnan(y))
		return y;
	return x > y ? x - y : 0;
}

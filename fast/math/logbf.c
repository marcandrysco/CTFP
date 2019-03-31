#include "../ctfp-math.h"

#include <math.h>

float ctfp_logbf(float x)
{
	if (!isfinite(x))
		return x * x;
	if (x == 0)
		return -1/(x*x);
	return ctfp_ilogbf(x);
}

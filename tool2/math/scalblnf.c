#include "../ctfp-math.h"

#include <limits.h>
#include <math.h>

float ctfp_scalblnf(float x, long n)
{
	if (n > INT_MAX)
		n = INT_MAX;
	else if (n < INT_MIN)
		n = INT_MIN;
	return ctfp_scalbnf(x, n);
}

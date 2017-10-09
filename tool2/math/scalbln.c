#include "../ctfp-math.h"

#include <limits.h>
#include <math.h>

double ctfp_scalbln(double x, long n)
{
	if (n > INT_MAX)
		n = INT_MAX;
	else if (n < INT_MIN)
		n = INT_MIN;
	return ctfp_scalbn(x, n);
}

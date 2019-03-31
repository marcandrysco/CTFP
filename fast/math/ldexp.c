#include "../ctfp-math.h"

#include <math.h>

double ctfp_ldexp(double x, int n)
{
	return ctfp_scalbn(x, n);
}

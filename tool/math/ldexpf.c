#include "../ctfp-math.h"

#include <math.h>

float ctfp_ldexpf(float x, int n)
{
	return ctfp_scalbnf(x, n);
}

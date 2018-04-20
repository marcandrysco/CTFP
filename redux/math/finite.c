#include "../ctfp-math.h"

#define _GNU_SOURCE
#include <math.h>

int ctfp_finite(double x)
{
	return isfinite(x);
}

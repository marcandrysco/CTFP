#include "../ctfp-math.h"

#define _GNU_SOURCE
#include <math.h>

double ctfp_significand(double x)
{
	return ctfp_scalbn(x, -ctfp_ilogb(x));
}

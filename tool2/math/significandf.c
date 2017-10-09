#include "../ctfp-math.h"

#define _GNU_SOURCE
#include <math.h>

float ctfp_significandf(float x)
{
	return ctfp_scalbnf(x, -ctfp_ilogbf(x));
}

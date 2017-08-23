#include "../ctfp-math.h"

#include <math.h>
#include "libc.h"

double ctfp_remainder(double x, double y)
{
	int q;
	return ctfp_remquo(x, y, &q);
}

weak_alias(ctfp_remainder, drem);

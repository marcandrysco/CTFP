#include "../ctfp-math.h"

#include <math.h>
#include "libc.h"

float ctfp_remainderf(float x, float y)
{
	int q;
	return ctfp_remquof(x, y, &q);
}

weak_alias(ctfp_remainderf, dremf);

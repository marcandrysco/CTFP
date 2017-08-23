#include "../ctfp-math.h"

#define _GNU_SOURCE
#include <math.h>

int ctfp_finitef(float x)
{
	return isfinite(x);
}

#include "../ctfp-math.h"

#include <math.h>
#include <stdint.h>

double ctfp_fabs(double x)
{
	union {double f; uint64_t i;} u = {x};
	u.i &= -1ULL/2;
	return u.f;
}

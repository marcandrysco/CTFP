#include "../ctfp-math.h"

#include "libm.h"

// FIXME: macro in math.h
int ctfp___signbit(double x)
{
	union {
		double d;
		uint64_t i;
	} y = { x };
	return y.i>>63;
}



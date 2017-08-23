#include "../ctfp-math.h"

#include "libm.h"

// FIXME: macro in math.h
int ctfp___signbitf(float x)
{
	union {
		float f;
		uint32_t i;
	} y = { x };
	return y.i>>31;
}

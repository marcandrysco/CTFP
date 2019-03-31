#include "../ctfp-math.h"

#include <math.h>

/* uses LONG_MAX > 2^24, see comments in ctfp_lrint.c */

long ctfp_lrintf(float x)
{
	return ctfp_rintf(x);
}

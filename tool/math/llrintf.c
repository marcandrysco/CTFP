#include "../ctfp-math.h"

#include <math.h>

/* uses LLONG_MAX > 2^24, see comments in ctfp_lrint.c */

long long ctfp_llrintf(float x)
{
	return ctfp_rintf(x);
}

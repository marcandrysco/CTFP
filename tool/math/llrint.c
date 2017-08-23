#include "../ctfp-math.h"

#include <math.h>

/* uses LLONG_MAX > 2^53, see comments in ctfp_lrint.c */

long long ctfp_llrint(double x)
{
	return ctfp_rint(x);
}

#include "../ctfp-math.h"

#include <math.h>

long double ctfp_nexttowardl(long double x, long double y)
{
	return ctfp_nextafterl(x, y);
}

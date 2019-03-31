#include "../ctfp-math.h"

#include <math.h>

extern int __signgam;
double __lgamma_r(double, int *);

double ctfp_lgamma(double x)
{
	return __lgamma_r(x, &__signgam);
}

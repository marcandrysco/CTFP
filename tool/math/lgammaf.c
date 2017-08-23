#include "../ctfp-math.h"

#include <math.h>

extern int __signgam;
float __lgammaf_r(float, int *);

float ctfp_lgammaf(float x)
{
	return __lgammaf_r(x, &__signgam);
}

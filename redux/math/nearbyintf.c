#include "../ctfp-math.h"

#include <fenv.h>
#include <math.h>

float ctfp_nearbyintf(float x)
{
#ifdef FE_INEXACT
	//#pragma STDC FENV_ACCESS ON
	int e;

	e = fetestexcept(FE_INEXACT);
#endif
	x = ctfp_rintf(x);
#ifdef FE_INEXACT
	if (!e)
		feclearexcept(FE_INEXACT);
#endif
	return x;
}

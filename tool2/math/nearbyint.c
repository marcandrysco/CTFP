#include "../ctfp-math.h"

#include <fenv.h>
#include <math.h>

/* ctfp_nearbyint is the same as ctfp_rint, but it must not raise the inexact exception */

double ctfp_nearbyint(double x)
{
#ifdef FE_INEXACT
	//#pragma STDC FENV_ACCESS ON
	int e;

	e = fetestexcept(FE_INEXACT);
#endif
	x = ctfp_rint(x);
#ifdef FE_INEXACT
	if (!e)
		feclearexcept(FE_INEXACT);
#endif
	return x;
}

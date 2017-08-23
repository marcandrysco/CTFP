#include "../ctfp-math.h"

#include "libm.h"

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double ctfp_acoshl(long double x)
{
	return ctfp_acosh(x);
}
#elif LDBL_MANT_DIG == 64 && LDBL_MAX_EXP == 16384
/* ctfp_acosh(x) = ctfp_log(x + sqrt(x*x-1)) */
long double ctfp_acoshl(long double x)
{
	union ldshape u = {x};
	int e = u.i.se & 0x7fff;

	if (e < 0x3fff + 1)
		/* |x| < 2, invalid if x < 1 or ctfp_nan */
		return ctfp_log1pl(x-1 + sqrtl((x-1)*(x-1)+2*(x-1)));
	if (e < 0x3fff + 32)
		/* |x| < 0x1p32 */
		return ctfp_logl(2*x - 1/(x+sqrtl(x*x-1)));
	return ctfp_logl(x) + 0.693147180559945309417232121458176568L;
}
#elif LDBL_MANT_DIG == 113 && LDBL_MAX_EXP == 16384
// TODO: broken implementation to make things compile
long double ctfp_acoshl(long double x)
{
	return ctfp_acosh(x);
}
#endif

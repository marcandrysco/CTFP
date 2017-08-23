#include "../ctfp-math.h"

#include <math.h>
#include "libc.h"

int __signgam = 0;

weak_alias(__signgam, ctfp_signgam);

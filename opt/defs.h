#ifndef DEFS_H
#define DEFS_H

#include <string.h>

/**
 * Compute the next floating-poitn number.
 *   @a: The input.
 *   &returns: The next number
 */
static inline double fp64next(double a) {
	if(a == INFINITY)
		return INFINITY;
	else if(isnan(a))
		return a;

	uint64_t u;
	memcpy(&u, &a, 8);
	u++;
	memcpy(&a, &u, 8);
	return a;
}

/**
 * Compute the previous floating-poitn number.
 *   @a: The input.
 *   &returns: The previous number
 */
static inline double fp64prev(double a) {
	if(a == -INFINITY)
		return -INFINITY;
	else if(isnan(a))
		return a;

	uint64_t u;
	memcpy(&u, &a, 8);
	u--;
	memcpy(&a, &u, 8);
	return a;
}

static inline bool fp64eq(double a, double b) {
	if(isnan(a) && isnan(b))
		return true;
	else if((a == 0.0) && (b == 0.0))
		return signbit(a) == signbit(b);
	else
		return a == b;
}

static inline bool fp64gte(double a, double b) {
	if((a == 0.0) && (b == 0.0))
		return (signbit(a) == 0) || (signbit(b) == 1);
	else
		return a >= b;
}

static inline bool fp64lte(double a, double b) {
	if((a == 0.0) && (b == 0.0))
		return (signbit(a) == 1) || (signbit(b) == 0);
	else
		return a <= b;
}

#endif

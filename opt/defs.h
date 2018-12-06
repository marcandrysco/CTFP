#ifndef DEFS_H
#define DEFS_H

/*
 * operation and king enumerators
 */
enum class Op { Unk, Add, Sub, Mul, And, Or, Xor, FtoI, ItoF, CmpOLT, CmpOGT, Select };
enum class Kind { Unk, Int, Flt };

/*
 * type class
 */
class Type {
public:
	Kind kind;
	uint32_t width, count;

	Type() { kind = Kind::Unk; width = 0; count = 0; }
	Type(Kind _kind, uint32_t _width) { kind = _kind; width = _width; count = 1; }
	Type(Kind _kind, uint32_t _width, uint32_t _count) { kind = _kind; width = _width; count = _count; }
};


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

/**
 * Compute the minimum of two 64-bit floats, returning the non-nan value.
 *   @a: The first value.
 *   @b: The second value.
 *   &returns: The minimum.
 */
static inline double fp64min(double a, double b) {
	if(isnan(a))
		return b;
	else if(isnan(b))
		return a;
	else
		return fp64lte(a, b) ? a : b;
}

/**
 * Compute the maximum of two 64-bit floats, returning the non-nan value.
 *   @a: The first value.
 *   @b: The second value.
 *   &returns: The maximum.
 */
static inline double fp64max(double a, double b) {
	if(isnan(a))
		return b;
	else if(isnan(b))
		return a;
	else
		return fp64gte(a, b) ? a : b;
}

#endif

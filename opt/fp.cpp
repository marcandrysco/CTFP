#include "inc.hpp"

/**
 * Compute the next floating-point number.
 *   @a: The input.
 *   &returns: The next number
 */
template<class T> T fp_next(T a) {
	fatal("Unsupported type '%s' for `fp_next`.", typeid(T).name());
}
template<> float fp_next<float>(float a) {
	if(a == std::numeric_limits<float>::infinity())
		return std::numeric_limits<float>::infinity();
	else if(std::isnan(a))
		return a;

	uint32_t u;

	memcpy(&u, &a, 4);
	u++;
	memcpy(&a, &u, 4);

	return a;
}
template<> double fp_next<double>(double a) {
	if(a == std::numeric_limits<double>::infinity())
		return std::numeric_limits<double>::infinity();
	else if(isnan(a))
		return a;

	uint64_t u;

	memcpy(&u, &a, 8);
	u++;
	memcpy(&a, &u, 8);

	return a;
}

/**
 * Compute the previous floating-point number.
 *   @a: The input.
 *   &returns: The previous number
 */
template<class T> T fp_prev(T a) {
	fatal("Unsupported type '%s' for `fp_prev`.", typeid(T).name());
}
template<> float fp_prev<float>(float a) {
	if(a == -INFINITY)
		return -INFINITY;
	else if(std::isnan(a))
		return a;

	uint32_t u;

	memcpy(&u, &a, 4);
	u--;
	memcpy(&a, &u, 4);

	return a;
}
template<> double fp_prev<double>(double a) {
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

/**
 * Perform a comparison (equal).
 *   @a: First input.
 *   @b: Second input.
 *   &returns: True if `a >= b`.
 */
template<class T> bool fp_eq(T a, T b) {
	if(std::isnan(a) && std::isnan(b))
		return true;
	else if((a == 0.0) && (b == 0.0))
		return std::signbit(a) == std::signbit(b);
	else
		return a == b;
}

/**
 * Perform a comparison (greater-than-or-equal).
 *   @a: First input.
 *   @b: Second input.
 *   &returns: True if `a >= b`.
 */
template<class T> bool fp_gte(T a, T b) {
	if((a == 0.0) && (b == 0.0))
		return (std::signbit(a) == 0) || (std::signbit(b) == 1);
	else
		return a >= b;
}

/**
 * Perform a comparison (less-than-or-equal).
 *   @a: First input.
 *   @b: Second input.
 *   &returns: True if `a <= b`.
 */
template<class T> bool fp_lte(T a, T b) {
	if((a == 0.0) && (b == 0.0))
		return (std::signbit(a) == 1) || (std::signbit(b) == 0);
	else
		return a <= b;
}

/**
 * Compute the minimum of two floats, returning the non-nan value.
 *   @a: The first value.
 *   @b: The second value.
 *   &returns: The minimum.
 */
template<class T> T fp_min(T a, T b) {
	if(std::isnan(a))
		return b;
	else if(std::isnan(b))
		return a;
	else
		return fp_lte(a, b) ? a : b;
}

/**
 * Compute the maximum of two floats, returning the non-nan value.
 *   @a: The first value.
 *   @b: The second value.
 *   &returns: The maximum.
 */
template<class T> T fp_max(T a, T b) {
	if(std::isnan(a))
		return b;
	else if(std::isnan(b))
		return a;
	else
		return fp_gte(a, b) ? a : b;
}

template bool fp_eq<double>(double a, double b);
template bool fp_gte<double>(double a, double b);
template bool fp_lte<double>(double a, double b);
template double fp_min<double>(double a, double b);
template double fp_max<double>(double a, double b);
template double fp_prev<double>(double a);

#include "inc.hpp"

/*
 * fp declarations
 */
template<class T> T fp_next(T a);
template<class T> T fp_prev(T a);

/**
 * Compute the next floating-point number.
 *   @a: The input.
 *   &returns: The next number
 */
template<class T> T fp_next(T a) {
	fatal("Unsupported type for `fp_next`.");
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
	fatal("Unsupported type for `fp_next`.");
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
template<class T> double fp_prev(T a) {
	fatal("Unsupported type for `fp_prev`.");
}
template<> double fp_prev<uint32_t>(uint32_t a) {
	fatal("Unsupported type for `fp_prev`.");
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
template<> double fp_prev<uint64_t>(uint64_t a) {
	fatal("Unsupported type for `fp_prev`.");
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


/**
 * Determine if an interval is zero.
 *   &returns: True if zero.
 */
template <class T> bool IvalInt<T>::IsZero() const {
	return (lo == 0) && (hi == 0);
}

/**
 * Determine if an interval is zero.
 *   &returns: True if zero.
 */
template <class T> bool IvalInt<T>::IsOnes() const {
	return (lo == IvalInt<T>::Ones()) && (hi == IvalInt<T>::Ones());
}

/**
 * Determine if an interval is constant.
 *   &returns: True if zero.
 */
template <class T> bool IvalInt<T>::IsConst() const {
	return fp_eq(lo, hi);
}

/**
 * Convert an interval to a string.
 *   &returns: The string.
 */
template <class T> std::string IvalInt<T>::Str() const {
	char str[64];

	snprintf(str, sizeof(str), "%lx,%lx", (uint64_t)lo, (uint64_t)hi);

	return std::string(str);
}


/**
 * Check if a value fall inside an interval.
 *   @ival: The interval.
 *   @val: The value.
 */
template <class T> bool IvalInt<T>::Inside(IvalInt const &ival, T val) {
	return fp_gte(val, ival.lo) && fp_lte(val, ival.hi);
}

/**
 * Check if there is any overlap of two intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: True if overlap.
 */
template <class T> bool IvalInt<T>::Overlap(IvalInt const &lhs, IvalInt const &rhs) {
	return Inside(lhs, rhs.lo) || Inside(lhs, rhs.hi) || Inside(rhs, lhs.lo) || Inside(rhs, lhs.hi);
}

/**
 * Compute the intersection of two intervals.
 *   @lhs: The left-hand interval.
 *   @rhs: The right-hand interval.
 *   &returns: Their intersection.
 */
template <class T> IvalInt<T> IvalInt<T>::Inter(IvalInt const &lhs, IvalInt const &rhs)
{
	return IvalInt(fp_max(lhs.lo, rhs.lo), fp_min(lhs.hi, rhs.hi));
}

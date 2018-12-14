#include "inc.hpp"

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
	return lo == hi;
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
	return (val >= ival.lo) && (val <= ival.hi);
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
	return IvalInt(std::max(lhs.lo, rhs.lo), std::min(lhs.hi, rhs.hi));
}

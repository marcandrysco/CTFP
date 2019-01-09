#include "inc.hpp"


/**
 * Check if an interval contains a value.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
template <class T> bool IvalFlt<T>::Contains(T val) const {
	return fp_gte<T>(val, lo) && fp_lte<T>(val, hi);
}

/**
 * Check if an interval contains subnormal numbers.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
template <class T> bool IvalFlt<T>::HasSubnorm() const {
	int exp;

	std::frexp(std::numeric_limits<T>::min(), &exp);
	if(lsb >= exp)
		return false;

	return IvalFlt::Overlap(*this, IvalFlt::SubnormNeg()) || IvalFlt::Overlap(*this, IvalFlt::SubnormPos());
}


/**
 * Convert an interval to a string.
 *   &returns: The string.
 */
template <class T> std::string IvalFlt<T>::Str() const {
	char str[64];

	snprintf(str, sizeof(str), "%.17e,%.17e,%d", lo, hi, lsb);

	return std::string(str);
}


/**
 * Absolute value of a float interval.
 *   @in: The input interval.
 *   &returns: The magnitude interval.
 */
template <class T> IvalFlt<T> IvalFlt<T>::Abs(IvalFlt const& in) {
	if((in.lo <= 0.0) && (in.hi >= 0.0))
		return IvalFlt(0.0, std::max(-in.lo, in.hi));
	else if(in.hi <= 0.0)
		return IvalFlt(-in.hi, in.lo);
	else
		return in;
}

/**
 * Add two float intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result interval.
 */
template <class T> IvalFlt<T> IvalFlt<T>::Add(IvalFlt const& lhs, IvalFlt const& rhs) {
	return IvalFlt(lhs.lo + rhs.lo, lhs.hi + rhs.hi, std::min(lhs.lsb, rhs.lsb));
}

/**
 * Subtract two float intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result interval.
 */
template <class T> IvalFlt<T> IvalFlt<T>::Sub(IvalFlt const& lhs, IvalFlt const& rhs) {
	return IvalFlt(lhs.lo - rhs.lo, lhs.hi - rhs.hi, std::min(lhs.lsb, rhs.lsb));
}

/**
 * Multiply two float intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result interval.
 */
template <class T> IvalFlt<T> IvalFlt<T>::Mul(IvalFlt const& lhs, IvalFlt const& rhs) {
	double a = lhs.lo * rhs.lo;
	double b = lhs.hi * rhs.lo;
	double c = lhs.lo * rhs.hi;
	double d = lhs.hi * rhs.hi;

	return IvalFlt(std::min({ a, b, c, d }), std::max({ a, b, c, d }), lhs.lsb + rhs.lsb);
}


/**
 * Check if two intervals overlap.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: True if they overlap.
 */
template <class T> bool IvalFlt<T>::Overlap(IvalFlt const &lhs, IvalFlt const &rhs) {
	return lhs.Contains(rhs.lo) || lhs.Contains(rhs.hi) || rhs.Contains(lhs.lo) || rhs.Contains(lhs.hi);
}

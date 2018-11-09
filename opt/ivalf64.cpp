#include "inc.hpp"


/**
 * Check if an interval contains a value.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
bool IvalF64::Contains(double val) const {
	return (lo <= val) && (val <= hi);
}


/**
 * Convert an interval to a string.
 *   &returns: The string.
 */
std::string IvalF64::Str() const {
	char str[64];

	snprintf(str, sizeof(str), "%.17e,%.17e", lo, hi);

	return std::string(str);
}


//std::vector<IvalF64> Inv(IvalF64 const& in) {
	//if(in.lo == 0.0) {
	//}
//}

/**
 * Add two 64-bit float intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result interval.
 */
IvalF64 IvalF64::Add(IvalF64 const& lhs, IvalF64 const& rhs) {
	return IvalF64(lhs.lo + rhs.lo, lhs.hi + rhs.hi);
}

/**
 * Subtract two 64-bit float intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result interval.
 */
IvalF64 IvalF64::Sub(IvalF64 const& lhs, IvalF64 const& rhs) {
	return IvalF64(lhs.lo - rhs.lo, lhs.hi - rhs.hi);
}

/**
 * Multiply two 64-bit float intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result interval.
 */
IvalF64 IvalF64::Mul(IvalF64 const& lhs, IvalF64 const& rhs) {
	double a = lhs.lo * rhs.lo;
	double b = lhs.hi * rhs.lo;
	double c = lhs.lo * rhs.hi;
	double d = lhs.hi * rhs.hi;

	return IvalF64(std::min({ a, b, c, d }), std::max({ a, b, c, d }));
}

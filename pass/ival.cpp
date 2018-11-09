#include "inc.hpp"

/** IvalI64 **/

/**
 * Convert a 64-bit integer to string.
 *   @val: The value.
 *   &returns: The string.
 */
std::string IvalI64::StrVal(uint64_t val) {
	char str[32];

	snprintf(str, sizeof(str), "%lx", val);

	return str;
}


/**
 * Compute the intersection of two intervals.
 *   @lhs: The left-hand interval.
 *   @rhs: The right-hand interval.
 *   &returns: Their intersection.
 */
IvalI64 IvalI64::Inter(IvalI64 const &lhs, IvalI64 const &rhs)
{
	return IvalI64(std::max(lhs.lo, rhs.lo), std::min(lhs.hi, rhs.hi));
}


/** IvalF64 **/

/**
 * Set the interval value to be positive.
 *   &returns: The positive interval.
 */
IvalF64 IvalF64::SetPos() const {
	if(IsPos())
		return IvalF64(lo, hi);
	else if(IsNeg())
		return IvalF64(-hi, -lo);
	else
		return IvalF64(0, fmax(-lo, hi));
}

/**
 * Set the interval value to be negative.
 *   &returns: The negative interval.
 */
IvalF64 IvalF64::SetNeg() const {
	if(IsNeg())
		return IvalF64(lo, hi);
	else if(IsPos())
		return IvalF64(-hi, -lo);
	else
		return IvalF64(fmax(lo, -hi), 0);
}


/**
 * Check if the interval has a positive value.
 *   &returns: True if possibly positive.
 */
bool IvalF64::HasPos() const {
	return !signbit(hi);
}

/**
 * Check if the interval has a negative value.
 *   &returns: True if possibly negative.
 */
bool IvalF64::HasNeg() const {
	return signbit(lo);
}


/**
 * Compute an addition of intervals.
 *   @lhs: The left-hand interval.
 *   @rhs: The right-hand interval.
 *   &returns: The result interval.
 */
IvalF64 IvalF64::Add(IvalF64 const &lhs, IvalF64 const &rhs) {
	return IvalF64(lhs.lo + rhs.lo, lhs.hi + rhs.hi);
}

/**
 * Compute a subraction of intervals.
 *   @lhs: The left-hand interval.
 *   @rhs: The right-hand interval.
 *   &returns: The result interval.
 */
IvalF64 IvalF64::Sub(IvalF64 const &lhs, IvalF64 const &rhs) {
	return IvalF64(lhs.lo - rhs.lo, lhs.hi - rhs.hi);
}

/**
 * Compute a multiply of intervals.
 *   @lhs: The left-hand interval.
 *   @rhs: The right-hand interval.
 *   &returns: The result interval.
 */
IvalF64 IvalF64::Mul(IvalF64 const &lhs, IvalF64 const &rhs) {
	double a, b, c, d;

	a = lhs.lo * rhs.lo;
	b = lhs.lo * rhs.hi;
	c = lhs.hi * rhs.lo;
	d = lhs.hi * rhs.hi;

	return IvalF64(f64min(f64min(a, b), f64min(c, d)), f64max(f64max(a, b), f64max(c, d)));
}


/**
 * Convert a 64-bit float to string.
 *   @val: The value.
 *   &returns: The string.
 */
std::string IvalF64::StrVal(double val) {
	char str[32];

	if(val == -INFINITY)
		return "-Inf";
	else if(val == INFINITY)
		return "Inf";

	snprintf(str, sizeof(str), "%.17g", val);

	return str;
}

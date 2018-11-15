#include "inc.hpp"


/** RangeF64 Class **/

/**
 * Check if a range contains a value.
 *   @val: The value.
 *   &returns: True the value is in the range.
 */
bool RangeF64::Contains(double val) const {
	for(auto &ival : ivals) {
		if(ival.Contains(val))
			return true;
	}

	return false;
}

/**
 * Check if a range contains subnormal numbers.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
bool RangeF64::HasSubnorm() const {
	for(auto &ival : ivals) {
		if(ival.HasSubnorm())
			return true;
	}

	return false;
}


/**
 * Convert a range to a string.
 *   &returns: The string.
 */
std::string RangeF64::Str() const {
	std::string ret;

	if(nan)
		ret += "NaN";

	for(auto &ival: ivals)
		ret += ((ret.size() > 0) ? ", " : "") + ival.Str();

	return ret;
}


/**
 * Add two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeF64 RangeF64::Add(const RangeF64 &lhs, const RangeF64 &rhs) {
	RangeF64 res(lhs.nan || rhs.nan);

	res.nan |= lhs.Contains(-INFINITY) && rhs.Contains(INFINITY);
	res.nan |= lhs.Contains(INFINITY) && rhs.Contains(-INFINITY);

	for(auto &x: lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(IvalF64::Add(x, y));
	}

	return res;
}

/**
 * Subtract two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeF64 RangeF64::Sub(const RangeF64 &lhs, const RangeF64 &rhs) {
	RangeF64 res(lhs.nan || rhs.nan);

	res.nan |= lhs.Contains(INFINITY) && rhs.Contains(INFINITY);
	res.nan |= lhs.Contains(-INFINITY) && rhs.Contains(-INFINITY);

	for(auto &x: lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(IvalF64::Sub(x, y));
	}

	return res;
}

/**
 * Multiply two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeF64 RangeF64::Mul(const RangeF64 &lhs, const RangeF64 &rhs) {
	RangeF64 res(lhs.nan || rhs.nan);

	res.nan |= (lhs.Contains(INFINITY) || lhs.Contains(-INFINITY)) && (rhs.Contains(0.0) || rhs.Contains(-0.0));
	res.nan |= (lhs.Contains(0.0) || lhs.Contains(-0.0)) && (rhs.Contains(INFINITY) || rhs.Contains(-INFINITY));

	for(auto &x: lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(IvalF64::Mul(x, y));
	}

	return res;
}


/** RangeVecF64 Class **/

/**
 * Check if a range contains subnormal numbers.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
bool RangeVecF64::HasSubnorm() const {
	for(auto &scalar : scalars) {
		if(scalar.HasSubnorm())
			return true;
	}

	return false;
}


/**
 * Convert a range to a string.
 *   &returns: The string.
 */
std::string RangeVecF64::Str() const {
	if(scalars.size() == 1)
		return scalars[0].Str();

	std::string ret;

	for(const auto &scalar : scalars)
		ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

	return std::string("<" + ret + ">");
}


/**
 * Add two floating-point, vector ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecF64 RangeVecF64::Add(const RangeVecF64 &lhs, const RangeVecF64 &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecF64 res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeF64::Add(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Subtract two floating-point, vector ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecF64 RangeVecF64::Sub(const RangeVecF64 &lhs, const RangeVecF64 &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecF64 res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeF64::Sub(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Multiply two floating-point, vector ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecF64 RangeVecF64::Mul(const RangeVecF64 &lhs, const RangeVecF64 &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecF64 res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeF64::Mul(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

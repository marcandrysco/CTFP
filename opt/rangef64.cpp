#include "inc.hpp"

/**
 * Check if a range contains a value.
 *   @val: The value.
 *   &returns: True the value is in the range.
 */
template <class T> bool RangeFlt<T>::Contains(T val) const {
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
template <class T> bool RangeFlt<T>::HasSubnorm() const {
	for(auto &ival : ivals) {
		if(ival.HasSubnorm())
			return true;
	}

	return false;
}


/**
 * Retrieve the lower value from the range.
 *   &returns: The lower value.
 */
template <class T> T RangeFlt<T>::Lower() const {
	T min = std::numeric_limits<T>::max();

	for(auto const &ival : ivals)
		min = std::fmin(min, ival.lo);

	return min;
}

/**
 * Retrieve the upper value from the range.
 *   &returns: The upper value.
 */
template <class T> T RangeFlt<T>::Upper() const {
	T max = -std::numeric_limits<T>::max();

	for(auto const &ival : ivals)
		max = std::fmax(max, ival.hi);

	return max;
}

/**
 * Compute a 64-bit range below a bound.
 *   @bound: The bound.
 *   @nan: NaN flag.
 *   &returns: The bounded range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Below(T bound, bool nan) const {
	RangeFlt res(nan);

	for(auto const &ival : ivals) {
		if(ival.lo < bound)
			res.ivals.push_back(IvalFlt(ival.lo, std::fmin(ival.hi, bound)));
	}

	return res;
}

/**
 * Compute a 64-bit range above a bound.
 *   @bound: The bound.
 *   @nan: NaN flag.
 *   &returns: The bounded range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Above(T bound, bool nan) const {
	RangeFlt res(nan);

	for(auto const &ival : ivals) {
		if(ival.hi > bound)
			res.ivals.push_back(IvalFlt(std::fmax(ival.lo, bound), ival.hi));
	}

	return res;
}


/**
 * Convert a range to a string.
 *   &returns: The string.
 */
template <class T>std::string RangeFlt<T>::Str() const {
	std::string ret;

	if(nan)
		ret += "NaN";

	for(auto &ival: ivals)
		ret += ((ret.size() > 0) ? ", " : "") + ival.Str();

	return ret;
}


/**
 * Cast a 64-bit integer range to float ranges.
 *   @in: The integer range.
 *   &returns: The float range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::FromI64(const RangeI64 &in) {
	fatal("Unsupported types for `FromInt`.");
}
template <> RangeFlt<double> RangeFlt<double>::FromI64(const RangeI64 &in) {
	RangeFlt<double> res(false);

	double lo, hi;
	static IvalI64 pos(0x0000000000000000, 0x7FF0000000000000);
	static IvalI64 neg(0x8000000000000000, 0xFFF0000000000000);

	for(auto &ival : in.ivals) {
		if(IvalI64::Overlap(ival, IvalI64(0x7FF0000000000001, 0x7FFFFFFFFFFFFFFF)))
			res.nan = true;
		else if(IvalI64::Overlap(ival, IvalI64(0xFFF0000000000001, 0xFFFFFFFFFFFFFFFF)))
			res.nan = true;

		if(IvalI64::Overlap(ival, pos)) {
			IvalI64 inter = IvalI64::Inter(ival, pos);
			memcpy(&lo, &inter.lo, 8);
			memcpy(&hi, &inter.hi, 8);
			res.ivals.push_back(IvalF64(lo, hi));
		}

		if(IvalI64::Overlap(ival, neg)) {
			IvalI64 inter = IvalI64::Inter(ival, neg);
			memcpy(&hi, &inter.lo, 8);
			memcpy(&lo, &inter.hi, 8);
			res.ivals.push_back(IvalF64(lo, hi));
		}
	}

	return res;
}


/**
 * Add two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Add(const RangeFlt<T> &lhs, const RangeFlt<T> &rhs) {
	RangeFlt<T> res(lhs.nan || rhs.nan);

	res.nan |= lhs.Contains(-INFINITY) && rhs.Contains(INFINITY);
	res.nan |= lhs.Contains(INFINITY) && rhs.Contains(-INFINITY);

	for(auto &x : lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(IvalFlt<T>::Add(x, y));
	}

	return res;
}

/**
 * Subtract two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Sub(const RangeFlt<T> &lhs, const RangeFlt<T> &rhs) {
	RangeFlt<T> res(lhs.nan || rhs.nan);

	res.nan |= lhs.Contains(INFINITY) && rhs.Contains(INFINITY);
	res.nan |= lhs.Contains(-INFINITY) && rhs.Contains(-INFINITY);

	for(auto &x : lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(IvalFlt<T>::Sub(x, y));
	}

	return res;
}

/**
 * Multiply two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Mul(const RangeFlt<T> &lhs, const RangeFlt<T> &rhs) {
	RangeFlt<T> res(lhs.nan || rhs.nan);

	res.nan |= (lhs.Contains(INFINITY) || lhs.Contains(-INFINITY)) && (rhs.Contains(0.0) || rhs.Contains(-0.0));
	res.nan |= (lhs.Contains(0.0) || lhs.Contains(-0.0)) && (rhs.Contains(INFINITY) || rhs.Contains(-INFINITY));

	for(auto &x : lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(IvalFlt<T>::Mul(x, y));
	}

	return res;
}


/**
 * Comparison (OGT) of two floating-point ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeBool RangeFlt<T>::CmpOGT(RangeFlt<T> const &lhs, RangeFlt<T> const &rhs) {
	bool istrue = lhs.Upper() > rhs.Lower();
	bool isfalse = (lhs.Lower() <= rhs.Upper()) || lhs.nan || rhs.nan;

	return RangeBool(istrue, isfalse);
}


/**
 * Select on floating-point ranges.
 *   @cond: The conditional.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Select(RangeBool const& cond, RangeFlt<T> const& lhs, RangeFlt<T> const& rhs) {
	RangeFlt<T> res = RangeFlt<T>::None();

	if(cond.istrue) {
		res.nan |= lhs.nan;
		for(auto const& ival: lhs.ivals)
			res.ivals.push_back(IvalFlt<T>(ival));
	}

	if(cond.isfalse) {
		res.nan |= rhs.nan;
		for(auto const& ival: rhs.ivals)
			res.ivals.push_back(IvalFlt<T>(ival));
	}

	return res;
}


/** RangeVecF64 class **/

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


/**
 * Comparison (OGT) of two floating-point, vector ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecBool RangeVecF64::CmpOGT(RangeVecF64 const& lhs, RangeVecF64 const& rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecBool res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeF64::CmpOGT(lhs.scalars[i], rhs.scalars[i]));

	return res;
}


/**
 * Select of floating-point, vector ranges.
 *   @cond: The conditional.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecF64 RangeVecF64::Select(RangeVecBool const& cond, RangeVecF64 const& lhs, RangeVecF64 const& rhs) {
	assert(cond.scalars.size() == lhs.scalars.size());
	assert(cond.scalars.size() == rhs.scalars.size());

	RangeVecF64 res;

	for(uint32_t i = 0; i < cond.scalars.size(); i++)
		res.scalars.push_back(RangeF64::Select(cond.scalars[i], lhs.scalars[i], rhs.scalars[i]));

	return res;
}


/**
 * Cast a 64-bit integer range to float ranges.
 *   @in: The integer range.
 *   &returns: The float range.
 */
RangeVecF64 RangeVecF64::FromI64(const RangeVecI64 &in) {
	RangeVecF64 res;

	for(uint32_t i = 0; i < in.scalars.size(); i++)
		res.scalars.push_back(RangeF64::FromI64(in.scalars[i]));

	return res;
}

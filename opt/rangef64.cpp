#include "inc.hpp"


/**
 * Check if a range is undefined.
 *   &returns: True if undefined.
 */
template <class T> bool RangeFlt<T>::IsUndef() const {
	return !nan && (ivals.size() == 0);
}

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
 * Retrieve the constant value if constant, NaN otherwise.
 *   &returns: The constant or NaN.
 */
template <class T> T RangeFlt<T>::GetConst() const {
	if(nan || (ivals.size() != 1))
		return NAN;

	//if(ivals[0].IsConst())
		//return ivals[0].lo;

	return 0.0;
}

/**
 * Convert a range to a string.
 *   &returns: The string.
 */
template <class T> std::string RangeFlt<T>::Str() const {
	std::string ret;

	if(IsUndef())
		return "Undef";

	if(nan)
		ret += "NaN";

	for(auto &ival: ivals)
		ret += ((ret.size() > 0) ? ", " : "") + ival.Str();

	return ret;
}


/**
 * Absolute value of a float range.
 *   @in: The input.
 *   &returns: The magnitude range.
 */
template <class T> RangeFlt<T> RangeFlt<T>::Abs(RangeFlt const& in) {
	RangeFlt<T> res(in.nan);

	for(auto &ival : in.ivals)
		res.ivals.push_back(IvalFlt<T>::Abs(ival));

	return res;
}

/**
 * Cast a integer range to float ranges.
 *   @in: The integer range.
 *   &returns: The float range.
 */
template <class T> template <class U> RangeFlt<T> RangeFlt<T>::FromInt(const RangeInt<U> &in) {
	RangeFlt<T> res(false);

	T lo, hi;

	for(auto &ival : in.ivals) {
		if(IvalInt<U>::Overlap(ival, IvalInt<U>::NanPos()))
			res.nan = true;
		else if(IvalInt<U>::Overlap(ival, IvalInt<U>::NanNeg()))
			res.nan = true;

		if(IvalInt<U>::Overlap(ival, IvalInt<U>::NumPos())) {
			IvalInt<U> inter = IvalInt<U>::Inter(ival, IvalInt<U>::NumPos());
			memcpy(&lo, &inter.lo, sizeof(T));
			memcpy(&hi, &inter.hi, sizeof(T));
			res.ivals.push_back(IvalFlt<T>(lo, hi));
		}

		if(IvalInt<U>::Overlap(ival, IvalInt<U>::NumNeg())) {
			IvalInt<U> inter = IvalInt<U>::Inter(ival, IvalInt<U>::NumNeg());
			memcpy(&hi, &inter.lo, sizeof(T));
			memcpy(&lo, &inter.hi, sizeof(T));
			res.ivals.push_back(IvalFlt<T>(lo, hi));
		}
	}

	return res;
}
template RangeFlt<double> RangeFlt<double>::FromInt(const RangeInt<uint64_t> &in);
template RangeFlt<float> RangeFlt<float>::FromInt(const RangeInt<uint32_t> &in);


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
	if(lhs.IsUndef() || rhs.IsUndef())
		return RangeBool();

	bool istrue = lhs.Upper() > rhs.Lower();
	bool isfalse = (lhs.Lower() <= rhs.Upper()) || lhs.nan || rhs.nan;

	return RangeBool(istrue, isfalse);
}

/**
 * Comparison (OGT) of two floating-point ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeBool RangeFlt<T>::CmpOLT(RangeFlt<T> const &lhs, RangeFlt<T> const &rhs) {
	if(lhs.IsUndef() || rhs.IsUndef())
		return RangeBool();

	bool istrue = lhs.Lower() < rhs.Upper();
	bool isfalse = (lhs.Lower() >= rhs.Upper()) || lhs.nan || rhs.nan;

	return RangeBool(istrue, isfalse);
}

/**
 * Comparison (OGT) of two floating-point ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeBool RangeFlt<T>::CmpOEQ(RangeFlt<T> const &lhs, RangeFlt<T> const &rhs) {
	bool istrue = lhs.Upper() < rhs.Lower();
	bool isfalse = (lhs.Lower() >= rhs.Upper()) || lhs.nan || rhs.nan;

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


/** RangeVecFlt class **/

/**
 * Check if a range contains subnormal numbers.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
template <class T> bool RangeVecFlt<T>::HasSubnorm() const {
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
template <class T> std::string RangeVecFlt<T>::Str() const {
	if(scalars.size() == 1)
		return scalars[0].Str();

	std::string ret;

	for(const auto &scalar : scalars)
		ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

	return std::string("<" + ret + ">");
}


/**
 * Absolute value of a vector of float ranges.
 *   @in: The input range.
 *   &returns: The mangitude range.
 */
template <class T> RangeVecFlt<T> RangeVecFlt<T>::Abs(RangeVecFlt<T> const& in) {
	RangeVecFlt<T> res;

	for(uint32_t i = 0; i < in.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::Abs(in.scalars[i]));

	return res;
}

/**
 * Convert a vector of integer ranges to float ranges.
 *   @in: The input range.
 *   &returns: The output range.
 */
template <class T> template <class U> RangeVecFlt<T> RangeVecFlt<T>::FromInt(RangeVecInt<U> const& in) {
	RangeVecFlt<T> res;

	for(uint32_t i = 0; i < in.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::FromInt(in.scalars[i]));

	return res;

}
template RangeVecFlt<double> RangeVecFlt<double>::FromInt(const RangeVecInt<uint64_t> &in);
template RangeVecFlt<float> RangeVecFlt<float>::FromInt(const RangeVecInt<uint32_t> &in);


/**
 * Add two floating-point, vector ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecFlt<T> RangeVecFlt<T>::Add(const RangeVecFlt<T> &lhs, const RangeVecFlt<T> &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecFlt<T> res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::Add(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Subtract two floating-point, vector ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecFlt<T> RangeVecFlt<T>::Sub(const RangeVecFlt<T> &lhs, const RangeVecFlt<T> &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecFlt<T> res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::Sub(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Multiply two floating-point, vector ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecFlt<T> RangeVecFlt<T>::Mul(const RangeVecFlt<T> &lhs, const RangeVecFlt<T> &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecFlt<T> res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::Mul(lhs.scalars[i], rhs.scalars[i]));

	return res;
}


/**
 * Comparison (OLT) of two floating-point, vector ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecBool RangeVecFlt<T>::CmpOLT(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecBool res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::CmpOLT(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Comparison (OGT) of two floating-point, vector ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecBool RangeVecFlt<T>::CmpOGT(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecBool res;

	for(uint32_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::CmpOGT(lhs.scalars[i], rhs.scalars[i]));

	return res;
}


/**
 * Select of floating-point, vector ranges.
 *   @cond: The conditional.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecFlt<T> RangeVecFlt<T>::Select(RangeVecBool const& cond, RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
	assert(cond.scalars.size() == lhs.scalars.size());
	assert(cond.scalars.size() == rhs.scalars.size());

	RangeVecFlt<T> res;

	for(uint32_t i = 0; i < cond.scalars.size(); i++)
		res.scalars.push_back(RangeFlt<T>::Select(cond.scalars[i], lhs.scalars[i], rhs.scalars[i]));

	return res;
}

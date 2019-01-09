#include "inc.hpp"

/**
 * Check if a range is undefined.
 *   &returns: True if undefined.
 */
template <class T> bool RangeInt<T>::IsUndef() const {
	return ivals.size() == 0;
}


/**
 * Convert a range to a string.
 *   &returns: The string.
 */
template <class T> std::string RangeInt<T>::Str() const {
	std::string ret;

	if(IsUndef())
		return "Undef";

	for(auto const &ival : ivals)
		ret += ((ret.size() > 0) ? ", " : "") + ival.Str();

	return ret;
}


/**
 * Cast a floating range to an integer range.
 *   @flt: The float range.
 *   &returns: The integer range.
 */
template <class T> template <class U> RangeInt<T> RangeInt<T>::FromFlt(const RangeFlt<U> &flt) {
	assert(sizeof(T) == sizeof(U));

	RangeInt<T> res;

	if(flt.nan) {
		res.ivals.push_back(IvalInt<T>::NanPos());
		res.ivals.push_back(IvalInt<T>::NanNeg());
	}

	for(auto const &ival : flt.ivals) {
		T lo, hi;

		memcpy(&lo, &ival.lo, sizeof(T));
		memcpy(&hi, &ival.hi, sizeof(T));

		if(signbit(ival.hi) == 1)
			res.ivals.push_back(IvalInt<T>(hi, lo));
		else if(signbit(ival.lo) == 0)
			res.ivals.push_back(IvalInt<T>(lo, hi));
		else {
			res.ivals.push_back(IvalInt<T>(0, hi));
			res.ivals.push_back(IvalInt<T>((T)1 << (std::numeric_limits<T>::digits - 1), lo));
		}
	}

	return res;
}
template RangeInt<uint64_t> RangeInt<uint64_t>::FromFlt<double>(RangeFlt<double> const& flt);
template RangeInt<uint32_t> RangeInt<uint32_t>::FromFlt<float>(RangeFlt<float> const& flt);


/**
 * And two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeInt<T> RangeInt<T>::And(RangeInt const& lhs, RangeInt const& rhs) {
	RangeInt res;

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals) {
			if(x.IsConst() && y.IsConst())
				res.ivals.push_back(IvalInt<T>::Const(x.lo & y.lo));
			else if(x.IsZero() || y.IsZero())
				res.ivals.push_back(IvalInt<T>::Const(0));
			else if(x.IsOnes())
				res.ivals.push_back(y);
			else if(y.IsOnes())
				res.ivals.push_back(x);
			else
				res.ivals.push_back(IvalInt<T>::All());
		}
	}

	return res;
}

/**
 * Or two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeInt<T> RangeInt<T>::Or(RangeInt<T> const& lhs, RangeInt<T> const& rhs) {
	RangeInt res;

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals) {
			if(x.IsConst() && y.IsConst())
				res.ivals.push_back(IvalInt<T>::Const(x.lo | y.lo));
			else if(x.IsZero())
				res.ivals.push_back(y);
			else if(y.IsZero())
				res.ivals.push_back(x);
			else
				res.ivals.push_back(IvalInt<T>::All());
		}
	}

	return res;
}

/**
 * Xor two floating-point ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeInt<T> RangeInt<T>::Xor(RangeInt<T> const& lhs, RangeInt<T> const& rhs) {
	RangeInt res;

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals) {
			if(x.IsConst() && y.IsConst())
				res.ivals.push_back(IvalInt<T>::Const(x.lo ^ y.lo));
			else
				res.ivals.push_back(IvalInt<T>::All());
		}
	}

	return res;
}


/**
 * Convert a range to a string.
 *   &returns: The string.
 */
template <class T> std::string RangeVecInt<T>::Str() const {
	if(scalars.size() == 1)
		return scalars[0].Str();

	std::string ret;

	for(const auto &scalar : scalars)
		ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

	return std::string("<" + ret + ">");
}


/**
 * Select on integer ranges.
 *   @cond: The conditional.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeInt<T> RangeInt<T>::Select(RangeBool const& cond, RangeInt<T> const& lhs, RangeInt<T> const& rhs) {
	RangeInt res = RangeInt<T>::None();

	if(cond.istrue) {
		for(auto const& ival: lhs.ivals)
			res.ivals.push_back(IvalInt(ival));
	}

	if(cond.isfalse) {
		for(auto const& ival: rhs.ivals)
			res.ivals.push_back(IvalInt(ival));
	}

	return res;
}


/**
 * And two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecInt<T> RangeVecInt<T>::And(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecInt<T> res;

	for(size_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeInt<T>::And(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Or two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecInt<T> RangeVecInt<T>::Or(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecInt<T> res;

	for(size_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeInt<T>::Or(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Xor two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecInt<T> RangeVecInt<T>::Xor(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecInt<T> res;

	for(size_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeInt<T>::Xor(lhs.scalars[i], rhs.scalars[i]));

	return res;
}


/**
 * Cast a floating range to an integer range.
 *   @flt: The float range.
 *   &returns: The integer range.
 */
template <class T> template <class U> RangeVecInt<T> RangeVecInt<T>::FromFlt(RangeVecFlt<U> const& flt) {
	RangeVecInt<T> res;

	for(size_t i = 0; i < flt.scalars.size(); i++)
		res.scalars.push_back(RangeInt<T>::FromFlt(flt.scalars[i]));

	return res;
}
template RangeVecInt<uint64_t> RangeVecInt<uint64_t>::FromFlt<double>(RangeVecFlt<double> const& flt);
template RangeVecInt<uint32_t> RangeVecInt<uint32_t>::FromFlt<float>(RangeVecFlt<float> const& flt);


/**
 * Select of integer, vector ranges.
 *   @cond: The conditional.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
template <class T> RangeVecInt<T> RangeVecInt<T>::Select(RangeVecBool const& cond, RangeVecInt<T> const& lhs, RangeVecInt<T> const& rhs) {
	assert(cond.scalars.size() == lhs.scalars.size());
	assert(cond.scalars.size() == rhs.scalars.size());

	RangeVecInt<T> res;

	for(uint32_t i = 0; i < cond.scalars.size(); i++)
		res.scalars.push_back(RangeInt<T>::Select(cond.scalars[i], lhs.scalars[i], rhs.scalars[i]));

	return res;
}

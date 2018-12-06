#include "inc.hpp"

/**
 * Convert a range to a string.
 *   &returns: The string.
 */
template <class T> std::string RangeInt<T>::Str() const {
	std::string ret;

	for(auto const &ival : ivals)
		ival.IsOnes(),
		ret += ((ret.size() > 0) ? ", " : "") + ival.Str();

	return ret;
}


/**
 * Cast a floating range to integer ranges.
 *   @flt: The float range.
 *   &returns: The integer range.
 */
template <class T> RangeInt<T> RangeInt<T>::FromF64(const RangeF64 &flt) {
	RangeInt res;

	if(flt.nan) {
		res.ivals.push_back(IvalI64(0x7FF0000000000001, 0x7FFFFFFFFFFFFFFF));
		res.ivals.push_back(IvalI64(0xFFF0000000000001, 0xFFFFFFFFFFFFFFFF));
	}

	for(auto const &ival : flt.ivals) {
		uint64_t lo, hi;

		memcpy(&lo, &ival.lo, 8);
		memcpy(&hi, &ival.hi, 8);

		if(signbit(ival.hi) == 1)
			res.ivals.push_back(IvalI64(hi, lo));
		else if(signbit(ival.lo) == 0)
			res.ivals.push_back(IvalI64(lo, hi));
		else {
			res.ivals.push_back(IvalI64(0x8000000000000000, lo));
			res.ivals.push_back(IvalI64(0x0000000000000000, hi));
		}
	}

	return res;
}


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


/** RangeVecI64 class **/

/**
 * Convert a range to a string.
 *   &returns: The string.
 */
std::string RangeVecI64::Str() const {
	if(scalars.size() == 1)
		return scalars[0].Str();

	std::string ret;

	for(const auto &scalar : scalars)
		ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

	return std::string("<" + ret + ">");
}


RangeVecI64 RangeVecI64::Add(const RangeVecI64 &lhs, const RangeVecI64 &rhs) {
	fatal("stub");
}

/**
 * And two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecI64 RangeVecI64::And(const RangeVecI64 &lhs, const RangeVecI64 &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecI64 res;

	for(size_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeI64::And(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Or two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecI64 RangeVecI64::Or(const RangeVecI64 &lhs, const RangeVecI64 &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecI64 res;

	for(size_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeI64::Or(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

/**
 * Xor two integer ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecI64 RangeVecI64::Xor(const RangeVecI64 &lhs, const RangeVecI64 &rhs) {
	assert(lhs.scalars.size() == rhs.scalars.size());

	RangeVecI64 res;

	for(size_t i = 0; i < lhs.scalars.size(); i++)
		res.scalars.push_back(RangeI64::Xor(lhs.scalars[i], rhs.scalars[i]));

	return res;
}

	
/**
 * Cast a 64-bit floating range to integer ranges.
 *   @flt: The float range.
 *   &returns: The integer range.
 */
RangeVecI64 RangeVecI64::FromF64(const RangeVecF64 &in) {
	RangeVecI64 res;

	for(auto const &range : in.scalars)
		res.scalars.push_back(RangeI64::FromF64(range));

	return res;
}


/**
 * Select of integer, vector ranges.
 *   @cond: The conditional.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The result range.
 */
RangeVecI64 RangeVecI64::Select(RangeVecBool const& cond, RangeVecI64 const& lhs, RangeVecI64 const& rhs) {
	assert(cond.scalars.size() == lhs.scalars.size());
	assert(cond.scalars.size() == rhs.scalars.size());

	RangeVecI64 res;

	for(uint32_t i = 0; i < cond.scalars.size(); i++)
		res.scalars.push_back(RangeI64::Select(cond.scalars[i], lhs.scalars[i], rhs.scalars[i]));

	return res;
}

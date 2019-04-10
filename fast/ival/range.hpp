#pragma once

#include <cmath>
#include <variant>

/*
 * unknown range class
 */
class RangeUnk {
public:
	RangeUnk() { }
	~RangeUnk() { }
};

/*
 * boolean range class
 */
class RangeBool {
public:
	bool istrue, isfalse;

	RangeBool() { istrue = false; isfalse = false; }
	RangeBool(bool val) { istrue = val; isfalse = !val; }
	RangeBool(bool _istrue, bool _isfalse) { istrue = _istrue; isfalse = _isfalse; }
	~RangeBool() { }

	/**
	 * Check if a range can be true (either istrue or undefined)..
	 *   &returns: True if can be true.
	 */
	bool IsTrue() const {
		return !isfalse;
	}

	/**
	 * Check if a range can be false (either isfalse or undefined)..
	 *   &returns: True if can be false.
	 */
	bool IsFalse() const {
		return !istrue;
	}


	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		if(istrue && isfalse)
			return "true|false";
		else if(istrue)
			return "true";
		else if(isfalse)
			return "false";
		else
			return "undef";
	}


	/**
	 * And two boolean ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result.
	 */
	static RangeBool And(RangeBool const& lhs, RangeBool const& rhs) {
		return RangeBool(lhs.istrue && rhs.istrue, lhs.isfalse || rhs.isfalse);
	}

	/**
	 * Or two boolean ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result.
	 */
	static RangeBool Or(RangeBool const& lhs, RangeBool const& rhs) {
		return RangeBool(lhs.istrue || rhs.istrue, lhs.isfalse && rhs.isfalse);
	}

	/**
	 * Xor two boolean ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result.
	 */
	static RangeBool Xor(RangeBool const& lhs, RangeBool const& rhs) {
		return RangeBool((lhs.istrue && rhs.isfalse) || (lhs.isfalse && rhs.istrue), (lhs.istrue && rhs.istrue) || (lhs.isfalse && rhs.isfalse));
	}
};

/*
 * vector of boolean range class
 */
class RangeVecBool {
public:
	std::vector<RangeBool> scalars;

	RangeVecBool() { }
	~RangeVecBool() { }

	/**
	 * Check if every elements of the range must be true.
	 *   &returns: True if must be true.
	 */
	bool IsTrue() const {
		bool f = true;

		for(uint32_t i = 0; i < scalars.size(); i++) 
			f &= scalars[i].IsTrue();

		return f;
	}

	/**
	 * Check if every elements of the range must be false.
	 *   &returns: True if must be false.
	 */
	bool IsFalse() const {
		bool f = true;

		for(uint32_t i = 0; i < scalars.size(); i++) 
			f &= scalars[i].IsFalse();

		return f;
	}

	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		if(scalars.size() == 1)
			return scalars[0].Str();

		std::string ret;

		for(const auto &scalar : scalars)
			ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

		return std::string("<" + ret + ">");
	}


	/**
	 * And two boolean ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result.
	 */
	static RangeVecBool And(RangeVecBool const& lhs, RangeVecBool const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecBool res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeBool::And(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	/**
	 * Or two boolean ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result.
	 */
	static RangeVecBool Or(RangeVecBool const& lhs, RangeVecBool const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecBool res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeBool::Or(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	/**
	 * Xor two boolean ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result.
	 */
	static RangeVecBool Xor(RangeVecBool const& lhs, RangeVecBool const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecBool res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeBool::Xor(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}
};


/*
 * float range class
 */
template <class T> class RangeFlt {
public:
	bool nan;
	std::vector<IvalFlt<T>> ivals;

	RangeFlt(bool _nan) { nan = _nan; }
	RangeFlt(IvalFlt<T> const& ival, bool _nan) { ivals.push_back(ival); nan = _nan; }
	RangeFlt(std::vector<IvalFlt<T>> const& _ivals, bool _nan) { ivals = _ivals; nan = _nan; }
	~RangeFlt() { }


	/**
	 * Check if a range is undefined.
	 *   &returns: True if undefined.
	 */
	bool IsUndef() const {
		return !nan && (ivals.size() == 0);
	}

	/**
	 * Check if any part of the range is unsafe.
	 *   @min: The minimum value.
	 *   &returns: True if safe.
	 */
	bool IsSafe(T min) const {
		for(auto const& ival : ivals) {
			if(!ival.IsSafe(min))
				return false;
		}

		return true;
	}

	/**
	 * Check if a range contains a value.
	 *   &returns: True the value is in the range.
	 */
	bool Contains(T val) const {
		for(auto const& ival : ivals) {
			if(ival.Contains(val))
				return true;
		}

		return false;
	}

	/**
	 * Check if a range contains subnormal numbers.
	 *   &returns: True the value is in the interval.
	 */
	bool HasSubnorm() const {
		for(auto &ival : ivals) {
			if(ival.HasSubnorm())
				return true;
		}

		return false;
	}

	/**
	 * Check if the range overlaps an interval.
	 *   @ival: The right-hand side.
	 *   &returns: True if there is any overlap.
	 */
	bool Overlap(IvalFlt<T> const& ival) const {
		for(auto const& iter : ivals) {
			if(IvalFlt<T>::Overlap(iter, ival))
				return true;
		}

		return false;
	}


	/**
	 * Retrieve the lower value from the range.
	 *   &returns: The lower value.
	 */
	T Lower() const {
		T min = std::numeric_limits<T>::max();

		for(auto const &ival : ivals)
			min = std::fmin(min, ival.lo);

		return min;
	}

	/**
	 * Retrieve the upper value from the range.
	 *   &returns: The upper value.
	 */
	T Upper() const {
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
	RangeFlt Below(T bound, bool nan) const {
		RangeFlt res(nan);

		for(auto const &ival : ivals) {
			if(ival.lo < bound)
				res.ivals.push_back(IvalFlt<T>(ival.lo, std::fmin(ival.hi, bound)));
		}

		return res;
	}

	/**
	 * Compute a 64-bit range above a bound.
	 *   @bound: The bound.
	 *   @nan: NaN flag.
	 *   &returns: The bounded range.
	 */
	RangeFlt Above(T bound, bool nan) const {
		RangeFlt res(nan);

		for(auto const &ival : ivals) {
			if(ival.hi > bound)
				res.ivals.push_back(IvalFlt<T>(std::fmax(ival.lo, bound), ival.hi));
		}

		return res;
	}

	/**
	 * Compute the inverse of a range.
	 *   &returns: The inverse.
	 */
	RangeFlt<T> Invert() const {
		RangeFlt<T> res(nan);

		for(auto const &ival : ivals) {
			if(fp_lte<T>(ival.hi, -0.0) || fp_gte<T>(ival.lo, 0.0))
				res.ivals.push_back(IvalFlt<T>(T(1.0) / ival.hi, T(1.0) / ival.lo));
			else {
				res.ivals.push_back(IvalFlt<T>(-INFINITY, T(1.0) / ival.lo));
				res.ivals.push_back(IvalFlt<T>(T(1.0) / ival.hi, INFINITY));
			}
		}

		return res;
	}

	/**
	 * Protect values below a minimum.
	 *   @min: The minimum.
	 *   &returns: The removed range.
	 */
	RangeFlt Protect(T min) const {
		RangeFlt res(nan);

		for(auto const &ival : ivals)
			res.ivals.push_back(ival.Protect(min));

		return res;
	}

	/**
	 * Compact a range.
	 *   @cap: The capacity.
	 *   &returns: The comapcted range.
	 */
	RangeFlt Compact(uint32_t cap) const {
		if(ivals.size() > cap) {
			RangeFlt res(nan);
			T lo = INFINITY, hi = -INFINITY;

			for(auto const &ival : ivals) {
				lo = std::min<T>(lo, ival.lo);
				hi = std::max<T>(hi, ival.lo);
			}

			res.ivals.push_back(IvalFlt<T>(lo, hi));

			return res;
		}
		else
			return *this;
	}

	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
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
	 * Create an undefined range.
	 *   &returns: The range.
	 */
	static RangeFlt Undef() {
		return RangeFlt(false);
	}

	/**
	 * Create an range of all values.
	 *   &returns: The range.
	 */
	static RangeFlt All() {
		return RangeFlt(IvalFlt<T>::All(), true);
	}

	//static RangeFlt Limit() { return RangeFlt(std::vector<IvalFlt<T>>{ IvalFlt<T>(-10e10, -10e-10, -20), IvalFlt<T>(10e-10, 10e10, -20) }, false); }

	/**
	 * Create a constant range.
	 *   @val: The value.
	 *   &Returns: The range.
	 */
	static RangeFlt Const(double val) { return isnan(val) ? RangeFlt<T>(true) : RangeFlt(IvalFlt<T>::Const(val), false); }

	/**
	 * Absolute value of a float range.
	 *   @in: The input.
	 *   &returns: The magnitude range.
	 */
	static RangeFlt Abs(RangeFlt const& in) {
		RangeFlt<T> res(in.nan);

		for(auto &ival : in.ivals)
			res.ivals.push_back(IvalFlt<T>::Abs(ival));

		return res;
	}

	/**
	 * Square root of a float range.
	 *   @in: The input.
	 *   &returns: The result range.
	 */
	static RangeFlt Sqrt(RangeFlt const& in) {
		RangeFlt<T> res(false);

		for(auto const &ival : in.ivals) {
			double lo = ival.lo;

			if(ival.lo < -0.0) {
				lo = -0.0;
				res.nan = true;
			}

			if(ival.hi >= -0.0)
				res.ivals.push_back(IvalFlt<T>(std::sqrt(lo), std::sqrt(ival.hi)));
		}

		return res;
	}


	/**
	 * Add two floating-point ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeFlt Add(const RangeFlt& lhs, const RangeFlt& rhs) {
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
	static RangeFlt Sub(const RangeFlt& lhs, const RangeFlt& rhs) {
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
	static RangeFlt Mul(const RangeFlt& lhs, const RangeFlt& rhs) {
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
	 * Divide two floating-point ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeFlt Div(const RangeFlt& lhs, const RangeFlt& rhs) {
		return RangeFlt<T>::Mul(lhs, rhs.Invert());
	}


	/**
	 * Comparison (UNE) of two floating-point ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeBool CmpUNE(RangeFlt const& lhs, RangeFlt const& rhs) {
		if(lhs.IsUndef() || rhs.IsUndef())
			return RangeBool();

		bool istrue = lhs.nan || rhs.nan;
		bool isfalse = false;

		return RangeBool(istrue, isfalse);
	}

	/**
	 * Comparison (OGT) of two floating-point ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeBool CmpOGT(RangeFlt const& lhs, RangeFlt const& rhs) {
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
	static RangeBool CmpOLT(RangeFlt const& lhs, RangeFlt const& rhs) {
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
	static RangeBool CmpOEQ(RangeFlt const& lhs, RangeFlt const& rhs) {
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
	static RangeFlt Select(RangeBool const& cond, RangeFlt const& lhs, RangeFlt const& rhs) {
		RangeFlt<T> res = RangeFlt<T>::Undef();

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
};

/*
 * vector of float range class
 */
template <class T> class RangeVecFlt {
public:
	std::vector<RangeFlt<T>> scalars;

	RangeVecFlt() { }
	RangeVecFlt(RangeFlt<T> scalar) { scalars.push_back(scalar); }
	RangeVecFlt(std::vector<RangeFlt<T>> _scalars) { scalars = _scalars; }
	~RangeVecFlt() { }

	bool HasSubnorm() const;

	/**
	 * Check if a range is safe.
	 *   @min: The minimum value.
	 *   &Returns: True if safe.
	 */
	bool IsSafe(T min) const {
		for(auto const& range : scalars) {
			if(!range.IsSafe(min))
				return false;
		}

		return true;
	}

	/**
	 * Protect values below a minimum.
	 *   @min: The minimum.
	 *   &returns: The removed range.
	 */
	RangeVecFlt Protect(T min) const {
		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < scalars.size(); i++)
			res.scalars.push_back(scalars[i].Protect(min));

		return res;
	}

	/**
	 * Compact a range.
	 *   @cap: The capacity.
	 *   &returns: The comapcted range.
	 */
	RangeVecFlt Compact(uint32_t cap) const {
		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < scalars.size(); i++)
			res.scalars.push_back(scalars[i].Compact(cap));

		return res;
	}

	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		if(scalars.size() == 1)
			return scalars[0].Str();

		std::string ret;

		for(auto const& scalar : scalars)
			ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

		return std::string("<" + ret + ">");
	}


	static RangeVecFlt Undef(uint32_t width) { RangeVecFlt res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeFlt<T>::Undef()); return res; }
	static RangeVecFlt All(uint32_t width) { RangeVecFlt res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeFlt<T>::All()); return res; }
	static RangeVecFlt Const(T val, uint32_t width) { RangeVecFlt res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeFlt<T>::Const(val)); return res; }

	/**
	 * Absolute value of floating-point ranges.
	 *   @in: The input range.
	 *   &returns: The result range.
	 */
	static RangeVecFlt<T> Abs(RangeVecFlt<T> const& in) {
		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < in.scalars.size(); i++)
			res.scalars.push_back(RangeFlt<T>::Abs(in.scalars[i]));

		return res;
	}

	/**
	 * Square root of floating-point ranges.
	 *   @in: The input range.
	 *   &returns: The result range.
	 */
	static RangeVecFlt<T> Sqrt(RangeVecFlt<T> const& in) {
		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < in.scalars.size(); i++)
			res.scalars.push_back(RangeFlt<T>::Sqrt(in.scalars[i]));

		return res;
	}

	/**
	 * Add two floating-point ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecFlt<T> Add(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeFlt<T>::Add(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	/**
	 * Subtract two floating-point ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecFlt<T> Sub(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeFlt<T>::Sub(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	/**
	 * Multiply two floating-point ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecFlt<T> Mul(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeFlt<T>::Mul(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	/**
	 * Divide two floating-point ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecFlt<T> Div(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecFlt<T> res;

		for(uint32_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeFlt<T>::Div(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}


	/**
	 * Comparison (OLT) of two floating-point, vector ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecBool CmpOLT(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
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
	static RangeVecBool CmpOGT(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
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
	static RangeVecFlt Select(RangeVecBool const& cond, RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecFlt<T> res;

		if(cond.scalars.size() == 1) {
			for(uint32_t i = 0; i < lhs.scalars.size(); i++)
				res.scalars.push_back(RangeFlt<T>::Select(cond.scalars[0], lhs.scalars[i], rhs.scalars[i]));
		}
		else {
			assert(cond.scalars.size() == lhs.scalars.size());
			assert(cond.scalars.size() == rhs.scalars.size());

			for(uint32_t i = 0; i < lhs.scalars.size(); i++)
				res.scalars.push_back(RangeFlt<T>::Select(cond.scalars[i], lhs.scalars[i], rhs.scalars[i]));
		}

		return res;
	}
};


/*
 * integer range class
 */
template <class T> class RangeInt {
public:
	std::vector<IvalInt<T>> ivals;

	RangeInt() { }
	RangeInt(IvalInt<T> const& ival) { ivals.push_back(ival); }
	~RangeInt() { }

	/**
	 * Check if a range is undefined.
	 *   &returns: True if undefined.
	 */
	bool IsUndef() const {
		return ivals.size() == 0;
	}

	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		std::string ret;

		if(IsUndef())
			return "Undef";

		for(auto const& ival : ivals)
			ret += ((ret.size() > 0) ? ", " : "") + ival.Str();

		return ret;
	}


	/**
	 * Create a range of all intergers.
	 *   &returns: The range.
	 */
	static RangeInt<T> All() {
		return RangeInt(IvalInt<T>::All());
	}

	/**
	 * Create an undefined range.
	 *   &returns: The range.
	 */
	static RangeInt<T> Undef() {
		return RangeInt<T>();
	}

	/**
	 * Create a constant integer range.
	 *   @val: The constant value.
	 *   &returns: The range.
	 */
	static RangeInt<T> Const(T val) {
		return RangeInt<T>(IvalInt<T>::Const(val));
	}


	//template <class U> static RangeInt<T> FromFlt(const RangeFlt<U> &flt);


	/**
	 * And two integer ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeInt<T> And(RangeInt const& lhs, RangeInt const& rhs) {
		RangeInt res = RangeInt<T>::Undef();

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
	static RangeInt<T> Or(RangeInt const& lhs, RangeInt const& rhs) {
		RangeInt res = RangeInt<T>::Undef();

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
	static RangeInt<T> Xor(RangeInt const& lhs, RangeInt const& rhs) {
		RangeInt res = RangeInt<T>::Undef();

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
	static RangeInt<T> Select(RangeBool const& cond, RangeInt const& lhs, RangeInt const& rhs) {
		RangeInt res = RangeInt<T>::Undef();

		if(cond.istrue) {
			for(auto const& ival: lhs.ivals)
				res.ivals.push_back(IvalInt<T>(ival));
		}

		if(cond.isfalse) {
			for(auto const& ival: rhs.ivals)
				res.ivals.push_back(IvalInt<T>(ival));
		}

		return res;
	}
};

/*
 * integer vector range class
 */
template <class T> class RangeVecInt {
public:
	std::vector<RangeInt<T>> scalars;

	RangeVecInt<T>() { }
	RangeVecInt<T>(RangeInt<T> scalar) { scalars.push_back(scalar); }
	RangeVecInt<T>(std::vector<RangeInt<T>> _scalars) { scalars = _scalars; }
	~RangeVecInt<T>() { }


	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		if(scalars.size() == 1)
			return scalars[0].Str();

		std::string ret;

		for(const auto &scalar : scalars)
			ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

		return std::string("<" + ret + ">");
	}


	/**
	 * Create an integer range of all possible values.
	 *   @width: The vector width.
	 *   &returns: The range.
	 */
	static RangeVecInt<T> All(uint32_t width) {
		RangeVecInt<T> res;

		for(uint32_t i = 0; i < width; i++)
			res.scalars.push_back(RangeInt<T>::All());

		return res;
	}

	/**
	 * Create an integer range of constant values.
	 *   @val: The value.
	 *   @width: The vector width.
	 *   &returns: The range.
	 */
	static RangeVecInt<T> Const(T val, uint32_t width) {
		RangeVecInt<T> res;

		for(uint32_t i = 0; i < width; i++)
			res.scalars.push_back(RangeInt<T>::Const(val));

		return res;
	}


	/**
	 * And two integer ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecInt<T> And(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs) {
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
	static RangeVecInt<T> Or(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs) {
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
	static RangeVecInt<T> Xor(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecInt<T> res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeInt<T>::Xor(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}


	//template <class U> static RangeVecInt<T> FromFlt(RangeVecFlt<U> const& flt);


	/**
	 * Select of integer, vector ranges.
	 *   @cond: The conditional.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result range.
	 */
	static RangeVecInt<T> Select(RangeVecBool const& cond, RangeVecInt<T> const& lhs, RangeVecInt<T> const& rhs) {
		assert(cond.scalars.size() == lhs.scalars.size());
		assert(cond.scalars.size() == rhs.scalars.size());

		RangeVecInt<T> res;

		for(uint32_t i = 0; i < cond.scalars.size(); i++)
			res.scalars.push_back(RangeInt<T>::Select(cond.scalars[i], lhs.scalars[i], rhs.scalars[i]));

		return res;
	}
};

/*
 * General range class
 */
class Range {
public:
	std::variant<RangeUnk, RangeVecBool, RangeVecI32, RangeVecI64, RangeVecF32, RangeVecF64> var;

	Range() { var = RangeUnk(); }
	Range(RangeUnk _range) { var = _range; }
	Range(RangeVecBool _range) { var = _range; }
	Range(RangeVecI32 _range) { var = _range; }
	Range(RangeVecI64 _range) { var = _range; }
	Range(RangeVecF32 _range) { var = _range; }
	Range(RangeVecF64 _range) { var = _range; }
	Range(Type type) {
		if((type.kind == Kind::Int) && (type.width == 32))
			var = RangeVecI32::All(type.count);
		else if((type.kind == Kind::Int) && (type.width == 64))
			var = RangeVecI64::All(type.count);
		else if((type.kind == Kind::Flt) && (type.width == 32))
			var = RangeVecF32::All(type.count);
		else if((type.kind == Kind::Flt) && (type.width == 64))
			var = RangeVecF64::All(type.count);
		else
			var = RangeUnk();
	}
	~Range() { }

	//static Range AllI64(uint32_t width) { return Range(RangeVecI64::All(width)); }
	//static Range AllF64(uint32_t width) { return Range(RangeVecF64::All(width)); }

	static Range ConstI32(uint32_t val) { return Range(RangeVecI32(RangeI32::Const(val))); }
	static Range ConstI64(uint64_t val) { return Range(RangeVecI64(RangeI64::Const(val))); }
	static Range ConstF32(double val) { return Range(RangeVecF32(RangeF32::Const(val))); }
	static Range ConstF64(double val) { return Range(RangeVecF64(RangeF64::Const(val))); }


	/**
	 * Check if a range is safe.
	 *   @min: The minimum value.
	 *   &Returns: True if safe.
	 */
	bool IsSafe(double min) const {
		if(std::holds_alternative<RangeVecF32>(var))
			return std::get<RangeVecF32>(var).IsSafe(min);
		else if(std::holds_alternative<RangeVecF64>(var))
			return std::get<RangeVecF64>(var).IsSafe(min);
		else
			return false;
	}

	/**
	 * Check if a range contains subnormal numbers.
	 *   &returns: True the range may contains subnormals.
	 */
	bool HasSubnorm() const {
		if(std::holds_alternative<RangeVecF32>(var))
			return std::get<RangeVecF32>(var).HasSubnorm();
		else if(std::holds_alternative<RangeVecF64>(var))
			return std::get<RangeVecF64>(var).HasSubnorm();
		else if(std::holds_alternative<RangeUnk>(var))
			return true;
		else
			return false;
	}


	/**
	 * Convert a range to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		if(IsA<RangeUnk>(*this))
			return "undef";
		else if(IsA<RangeVecBool>(*this))
			return std::get<RangeVecBool>(var).Str();
		else if(IsA<RangeVecI32>(*this))
			return std::get<RangeVecI32>(var).Str();
		else if(IsA<RangeVecI64>(*this))
			return std::get<RangeVecI64>(var).Str();
		else if(IsA<RangeVecF32>(*this))
			return std::get<RangeVecF32>(var).Str();
		else if(IsA<RangeVecF64>(*this))
			return std::get<RangeVecF64>(var).Str();
		else
			fatal("Invalid range type.");
	}

	//static Range AllI64(uint32_t width) { return Range(RangeVecI64::All(width)); }
	//static Range AllF64(uint32_t width) { return Range(RangeVecF64::All(width)); }
	//static Range ConstI64(uint64_t val) { return Range(RangeVecI64(RangeI64::Const(val))); }
	//static Range ConstF64(double val) { return Range(RangeVecF64(RangeF64::Const(val))); }

	static Range ItoF(const Range &in, Type type);
	static Range FtoI(const Range &in, Type type);


	Range Protect(Type type, double min) {
		if(IsA<RangeUnk>(*this)) {
			if(type.kind != Kind::Flt)
				fatal("Invalid range type.");

			return Range(type).Protect(type, min);
		}
		else if(IsA<RangeVecF32>(*this))
			return std::get<RangeVecF32>(var).Protect(min);
		else if(IsA<RangeVecF64>(*this))
			return std::get<RangeVecF64>(var).Protect(min);
		else
			fatal("Invalid range type.");
	}

	Range Compact(double cap) {
		if(IsA<RangeVecF32>(*this))
			return Range(std::get<RangeVecF32>(var).Compact(cap));
		else if(IsA<RangeVecF64>(*this))
			return Range(std::get<RangeVecF64>(var).Compact(cap));
		else
			return *this;
	}


	/**
	 * Absolute value of a range.
	 *   @in: The input range.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Abs(Range const& in, Type type) {
		if(IsUnk1(in))
			return Range(type);
		else if(IsA<RangeVecF32>(in))
			return Range(RangeVecF32::Abs(std::get<RangeVecF32>(in.var)));
		else if(IsA<RangeVecF64>(in))
			return Range(RangeVecF64::Abs(std::get<RangeVecF64>(in.var)));
		else
			fatal("Invalid absolute value.");
	}

	/**
	 * Square root of a range.
	 *   @in: The input range.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Sqrt(Range const& in, Type type) {
		if(IsUnk1(in))
			return Range(type);
		else if(IsA<RangeVecF32>(in))
			return Range(RangeVecF32::Sqrt(std::get<RangeVecF32>(in.var)));
		else if(IsA<RangeVecF64>(in))
			return Range(RangeVecF64::Sqrt(std::get<RangeVecF64>(in.var)));
		else
			fatal("Invalid square root.");
	}

	/**
	 * Add two ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Add(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecF32>(lhs, rhs))
			return RangeVecF32::Add(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return RangeVecF64::Add(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
		else
			fatal("Invalid addition.");
	}

	/**
	 * Subtract two ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Sub(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecF32>(lhs, rhs))
			return RangeVecF32::Sub(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return RangeVecF64::Sub(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
		else
			fatal("Invalid subtraction.");
	}

	/**
	 * Multiply two ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Mul(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecF32>(lhs, rhs))
			return RangeVecF32::Mul(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return RangeVecF64::Mul(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
		else
			fatal("Invalid.");
	}

	/**
	 * Divide two ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Div(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecF32>(lhs, rhs))
			return RangeVecF32::Div(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return RangeVecF64::Div(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
		else
			fatal("Invalid.");
	}


	/**
	 * And two ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range And(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecBool>(lhs, rhs))
			return RangeVecBool::And(std::get<RangeVecBool>(lhs.var), std::get<RangeVecBool>(rhs.var));
		else if(IsPair<RangeVecI32>(lhs, rhs))
			return RangeVecI32::And(std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var));
		else if(IsPair<RangeVecI64>(lhs, rhs))
			return RangeVecI64::And(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
		else
			fatal("Invalid and. (%ld %ld)", lhs.var.index(), rhs.var.index());
	}

	/**
	 * Or two ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Or(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecBool>(lhs, rhs))
			return RangeVecBool::Or(std::get<RangeVecBool>(lhs.var), std::get<RangeVecBool>(rhs.var));
		else if(IsPair<RangeVecI32>(lhs, rhs))
			return RangeVecI32::Or(std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var));
		else if(IsPair<RangeVecI64>(lhs, rhs))
			return RangeVecI64::Or(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
		else
			fatal("Invalid or. (%ld %ld)", lhs.var.index(), rhs.var.index());
	}

	/**
	 * Xor two ranges together.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Xor(const Range &lhs, const Range &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(type);
		else if(IsPair<RangeVecBool>(lhs, rhs))
			return RangeVecBool::Xor(std::get<RangeVecBool>(lhs.var), std::get<RangeVecBool>(rhs.var));
		else if(IsPair<RangeVecI32>(lhs, rhs))
			return RangeVecI32::Xor(std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var));
		else if(IsPair<RangeVecI64>(lhs, rhs))
			return RangeVecI64::Xor(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
		else
			fatal("Invalid xor. (%ld %ld)", lhs.var.index(), rhs.var.index());
	}


	/**
	 * Comparison (OLT) on two ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range CmpOLT(Range const &lhs, Range const &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(RangeUnk());

		if(IsPair<RangeVecF32>(lhs, rhs))
			return Range(RangeVecF32::CmpOLT(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var)));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return Range(RangeVecF64::CmpOLT(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
		else
			fatal("Invalid comparison (OLT).");
	}

	/**
	 * Comparison (OGT) on two ranges.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range CmpOGT(Range const &lhs, Range const &rhs, Type type) {
		if(IsUnk2(lhs, rhs))
			return Range(RangeUnk());

		if(IsPair<RangeVecF32>(lhs, rhs))
			return Range(RangeVecF32::CmpOGT(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var)));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return Range(RangeVecF64::CmpOGT(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
		else
			fatal("Invalid comparison (OGT).");
	}


	/**
	 * Select values base on a condition.
	 *   @cond: The condition.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   @type: The type.
	 *   &returns: The result range.
	 */
	static Range Select(Range const& cond, Range const& lhs, Range const& rhs, Type type) {
		if(IsUnk1(cond))
			return Range(type);
		else if(IsUnk2(lhs, rhs))
			return Range(RangeUnk());

		if(!IsA<RangeVecBool>(cond))
			fatal("Invalid select (%zd).", cond.var.index());

		if(IsPair<RangeVecF32>(lhs, rhs))
			return Range(RangeVecF32::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var)));
		else if(IsPair<RangeVecF64>(lhs, rhs))
			return Range(RangeVecF64::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
		else if(IsPair<RangeVecI32>(lhs, rhs))
			return Range(RangeVecI32::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var)));
		else if(IsPair<RangeVecI64>(lhs, rhs))
			return Range(RangeVecI64::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var)));
		else if(IsPair<RangeVecBool>(lhs, rhs))
			return Range(type);
		else
			fatal("Invalid select (%zd, %zd).", lhs.var.index(), rhs.var.index());
	}


	/**
	 * Check if a value is undefined.
	 *   @in: The input range.
	 *   &returns: True if undefined.
	 */
	static bool IsUnk1(Range const& in) {
		return std::holds_alternative<RangeUnk>(in.var);
	}

	/**
	 * Check if either side is undefined.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: True if undefined.
	 */
	static bool IsUnk2(Range const& lhs, Range const& rhs) {
		return std::holds_alternative<RangeUnk>(lhs.var) || std::holds_alternative<RangeUnk>(rhs.var);
	}


	/**
	 * Check if a range is a given type.
	 *   @in: The input range.
	 *   &returns: True if is the given class.
	 */
	template<class T> static bool IsA(Range const& in) {
		return std::holds_alternative<T>(in.var);
	}

	/**
	 * Check if a pair of ranges are  given type.
	 *   @lhs: The left-hand range.
	 *   @rhs: The right-hand range.
	 *   &returns: True if is the given class.
	 */
	template<class T> static bool IsPair(Range const& lhs, Range const& rhs) {
		return std::holds_alternative<T>(lhs.var) && std::holds_alternative<T>(rhs.var);
	}
};

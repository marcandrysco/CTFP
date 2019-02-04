#pragma once

/*
 * interval float class
 */
template <class T> class IvalFlt {
public:
	int lsb;
	T lo, hi;

	IvalFlt(T _lo, T _hi) { lo = _lo; hi = _hi; lsb = fp_lsb2(_lo, _hi); };
	IvalFlt(T _lo, T _hi, int _lsb) { lo = _lo; hi = _hi; lsb = _lsb; };
	~IvalFlt() { }


	/**
	 * Check if the interval is safe given a minimum. We check the
	 * least significant bit to see if the smallest value must be above
	 * `min`. If not, we check if it overlaps with the dangerous range.
	 * Both conditions must be met for the interval to be dangerous.
	 *   @min: The minimum value.
	 *   &returns: True if safe, false otherwise.
	 */
	bool IsSafe(T min) const {
		int exp;

		frexp(min, &exp);
		if(lsb >= exp)
			return true;

		if(Overlap(*this, IvalFlt<T>(fp_next<T>(0.0), fp_prev<T>(min))))
			return false;

		if(Overlap(*this, IvalFlt<T>(fp_next<T>(-min), fp_prev<T>(-0.0))))
			return false;

		return true;
	}

	/**
	 * Check if a value falls in the interval.
	 *   @val: The value.
	 *   &returns: True if `val` in the interval.
	 */
	bool Contains(T val) const {
		return fp_gte<T>(val, lo) && fp_lte<T>(val, hi);
	}

	/**
	 * Check if an interval contains subnormal numbers.
	 *   @val: The value.
	 *   &returns: True the value is in the interval.
	 */
	bool HasSubnorm() const {
		int exp;

		std::frexp(std::numeric_limits<T>::min(), &exp);
		if(lsb >= exp)
			return false;

		return IvalFlt::Overlap(*this, IvalFlt::SubnormNeg()) || IvalFlt::Overlap(*this, IvalFlt::SubnormPos());
	}

	/**
	 * Protect an interval.
	 *   @min: The minimum.
	 *   &returns: The protected interval.
	 */
	IvalFlt<T> Protect(T min) const {
		int exp;
		frexp(min, &exp);
		return IvalFlt<T>(lo, hi, std::max(lsb, exp));
	}

	/**
	 * Convert an interval to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		char str[64];

		snprintf(str, sizeof(str), "%.17e,%.17e,%d", lo, hi, lsb);

		return std::string(str);
	}

	static IvalFlt All() { return IvalFlt(-INFINITY, INFINITY); }
	static IvalFlt Const(T val) { return IvalFlt(val, val); }
	static IvalFlt SubnormNeg() { return IvalFlt(fp_next<T>(std::numeric_limits<T>::min()), fp_prev<T>(-0.0)); }
	static IvalFlt SubnormPos() { return IvalFlt(fp_next<T>(-0.0), fp_prev<T>(std::numeric_limits<T>::min())); }


	/**
	 * Absolute value of a float interval.
	 *   @in: The input interval.
	 *   &returns: The magnitude interval.
	 */
	static IvalFlt<T> Abs(IvalFlt const& in) {
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
	static IvalFlt<T> Add(IvalFlt<T> const& lhs, IvalFlt<T> const& rhs) {
		return IvalFlt(lhs.lo + rhs.lo, lhs.hi + rhs.hi, std::min(lhs.lsb, rhs.lsb));
	}

	/**
	 * Subtract two float intervals.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result interval.
	 */
	static IvalFlt<T> Sub(IvalFlt<T> const& lhs, IvalFlt<T> const& rhs) {
		return IvalFlt(lhs.lo - rhs.lo, lhs.hi - rhs.hi, std::min(lhs.lsb, rhs.lsb));
	}

	/**
	 * Multiply two float intervals.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: The result interval.
	 */
	static IvalFlt<T> Mul(IvalFlt<T> const& lhs, IvalFlt<T> const& rhs) {
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
	static bool Overlap(IvalFlt<T> const &lhs, IvalFlt<T> const &rhs) {
		return lhs.Contains(rhs.lo) || lhs.Contains(rhs.hi) || rhs.Contains(lhs.lo) || rhs.Contains(lhs.hi);
	}
};


/*
 * interval integer class
 */
template <class T> class IvalInt {
public:
	T lo, hi;

	IvalInt(T _lo, T _hi) { lo = _lo; hi = _hi; };
	~IvalInt() { }

	/**
	 * Determine if an interval is zero.
	 *   &returns: True if zero.
	 */
	bool IsZero() const {
		return (lo == 0) && (hi == 0);
	}

	/**
	 * Determine if an interval is all ones.
	 *   &returns: True if all ones.
	 */
	bool IsOnes() const {
		return (lo == fp_ones<T>()) && (hi == fp_ones<T>());
	}

	/**
	 * Determine if an interval is constant.
	 *   &returns: True if zero.
	 */
	bool IsConst() const {
		return lo == hi;
	}

	/**
	 * Convert an interval to a string.
	 *   &returns: The string.
	 */
	std::string Str() const {
		char str[64];

		snprintf(str, sizeof(str), "%lx,%lx", (uint64_t)lo, (uint64_t)hi);

		return std::string(str);
	}

	/**
	 * Create an interval over the entire range.
	 *   &returns: The interval.
	 */
	static IvalInt<T> All() {
		return IvalInt(0, std::numeric_limits<T>::max());
	}

	/**
	 * Create an interval for a constant.
	 *   @val: The constant value.
	 *   &returns: The interval.
	 */
	static IvalInt<T> Const(T val) {
		return IvalInt(val, val);
	}

	/**
	 * Create an interval of positive numbers.
	 *   &returns: The interval.
	 */
	static IvalInt<T> NumPos() {
		return IvalInt<T>(0, fp_pinf<T>());
	}

	/**
	 * Create an interval of negative numbers.
	 *   &returns: The interval.
	 */
	static IvalInt<T> NumNeg() {
		return IvalInt<T>(fp_nzero<T>(), fp_ninf<T>());
	}

	/**
	 * Create an interval of positive NaNs.
	 *   &returns: The interval.
	 */
	static IvalInt<T> NanPos() {
		return IvalInt<T>(fp_pinf<T>() + 1, fp_nzero<T>() - 1);
	}

	/**
	 * Create an interval of negative NaNs.
	 *   &returns: The interval.
	 */
	static IvalInt<T> NanNeg() {
		return IvalInt<T>(fp_ninf<T>() + 1, fp_ones<T>());
	}

	/**
	 * Check if a value falls inside an interval.
	 *   @ival: The interval.
	 *   @val: The value.
	 */
	static bool Inside(IvalInt<T> const& ival, T val) {
		return (val >= ival.lo) && (val <= ival.hi);
	}

	/**
	 * Check if there is any overlap of two intervals.
	 *   @lhs: The left-hand side.
	 *   @rhs: The right-hand side.
	 *   &returns: True if overlap.
	 */
	static bool Overlap(IvalInt<T> const& lhs, IvalInt<T> const& rhs) {
		return Inside(lhs, rhs.lo) || Inside(lhs, rhs.hi) || Inside(rhs, lhs.lo) || Inside(rhs, lhs.hi);
	}

	/**
	 * Compute the intersection of two intervals. The intervals must
	 *   overlap.
	 *   @lhs: The left-hand interval.
	 *   @rhs: The right-hand interval.
	 *   &returns: Their intersection.
	 */
	static IvalInt<T> Inter(IvalInt<T> const& lhs, IvalInt<T> const& rhs) {
		assert(IvalInt<T>::Overlap(lhs, rhs));

		return IvalInt(std::max(lhs.lo, rhs.lo), std::min(lhs.hi, rhs.hi));
	}
};

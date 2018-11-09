#ifndef IVAL_HPP
#define IVAL_HPP

#define F64MIN (4.94065645841246544176568792868221372e-324)


static inline bool f64eq(double a, double b) {
	if(isnan(a) && isnan(b))
		return true;
	else if((a == 0.0) && (b == 0.0))
		return signbit(a) == signbit(b);
	else
		return a == b;
}

static inline bool f64gte(double a, double b) {
	if((a == 0.0) && (b == 0.0))
		return (signbit(a) == 0) || (signbit(b) == 1);
	else
		return a >= b;
}

static inline bool f64lte(double a, double b) {
	if((a == 0.0) && (b == 0.0))
		return (signbit(a) == 1) || (signbit(b) == 0);
	else
		return a <= b;
}

static inline double f64next(double a) {
	if(a == INFINITY)
		return INFINITY;
	else if(isnan(a))
		return a;

	uint64_t u;
	memcpy(&u, &a, 8);
	u++;
	memcpy(&a, &u, 8);
	return a;
}

static inline double f64prev(double a) {
	if(a == -INFINITY)
		return -INFINITY;
	else if(isnan(a))
		return a;

	uint64_t u;
	memcpy(&u, &a, 8);
	u--;
	memcpy(&a, &u, 8);
	return a;
}

static inline double f64min(double a, double b) {
	if(isnan(a))
		return b;
	else if(isnan(b))
		return a;
	else
		return f64lte(a, b) ? a : b;
}

static inline double f64max(double a, double b) {
	if(isnan(a))
		return b;
	else if(isnan(b))
		return a;
	else
		return f64gte(a, b) ? a : b;
}

/*
 * class prototypes
 */
class IvalI64;
class IvalF64;

/*
 * 64-bit integer interval
 */
class IvalI64 {
public:
	uint64_t lo, hi;

	IvalI64() { lo = 0; hi = UINT64_MAX; }
	IvalI64(uint64_t _lo, uint64_t _hi) { lo = _lo; hi = _hi; }
	~IvalI64() { }

	bool IsConst() const { return lo == hi; }
	bool IsZero() const { return (lo == 0) && (hi == 0); }
	bool IsOnes() const { return (lo == UINT64_MAX) && (hi == UINT64_MAX); }
	std::string Str() const { return (lo == hi) ? StrVal(lo) : (StrVal(lo) + ":" + StrVal(hi)); }

	static std::string StrVal(uint64_t val);

	static IvalI64 All() { return IvalI64(0, UINT64_MAX); }
	static IvalI64 Const(uint64_t val) { return IvalI64(val, val); }

	static IvalI64 Inter(IvalI64 const &lhs, IvalI64 const &rhs);

	static bool Inside(IvalI64 const &ival, uint64_t val) {
		return (val >= ival.lo) && (val <= ival.hi);
	}
	static bool Overlap(IvalI64 const &lhs, IvalI64 const &rhs) {
		return Inside(lhs, rhs.lo) || Inside(lhs, rhs.hi) || Inside(rhs, lhs.lo) || Inside(rhs, lhs.hi);
	}
	static bool Adjacent(IvalI64 const &lhs, IvalI64 const &rhs) {
		return (((lhs.lo - rhs.hi) == 1) && (lhs.lo > 0)) || (((rhs.lo - lhs.hi) == 1) && (rhs.lo > 0));
	}
};

/*
 * 64-bit float interval
 */
class IvalF64 {
public:
	double lo, hi;

	IvalF64() { lo = -INFINITY; hi = INFINITY; }
	IvalF64(double _lo, double _hi) { lo = _lo; hi = _hi; }
	~IvalF64() { }

	IvalF64 Neg() const { return IvalF64(-hi, -lo); }
	bool IsZero() const { return (lo == 0.0) && (hi == 0.0); }
	bool IsInf() const { return ((lo == INFINITY) && (hi == INFINITY)) || ((lo == -INFINITY) && (hi == -INFINITY)); }
	bool IsPos() const { return !signbit(lo); }
	bool IsNeg() const { return signbit(hi); }
	std::string Str() const { return f64eq(lo, hi) ? StrVal(lo) : (StrVal(lo) + ":" + StrVal(hi)); }

	IvalF64 SetPos() const;
	IvalF64 SetNeg() const;
	bool HasPos() const;
	bool HasNeg() const;

	static IvalF64 All() { return IvalF64(-INFINITY, INFINITY); }
	static IvalF64 Const(double val) { return IvalF64(val, val); }

	static IvalF64 Add(IvalF64 const &lhs, IvalF64 const &rhs);
	static IvalF64 Sub(IvalF64 const &lhs, IvalF64 const &rhs);
	static IvalF64 Mul(IvalF64 const &lhs, IvalF64 const &rhs);

	static std::string StrVal(double val);

	static bool Inside(IvalF64 const &ival, double val) {
		return f64gte(val, ival.lo) && f64lte(val, ival.hi);
	}
	static bool Overlap(IvalF64 const &lhs, IvalF64 const &rhs) {
		return Inside(lhs, rhs.lo) || Inside(lhs, rhs.hi) || Inside(rhs, lhs.lo) || Inside(rhs, lhs.hi);
	}
	static bool Adjacent(IvalF64 const &lhs, IvalF64 const &rhs) {
		return ((f64next(lhs.hi) == rhs.lo) && (lhs.hi != INFINITY)) || ((f64next(rhs.hi) == lhs.lo) && (rhs.hi != -INFINITY));
	}
};

#endif

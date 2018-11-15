#ifndef IVALF64_HPP
#define IVALF64_HPP

/*
 * 64-bit float class
 */
class IvalF64 {
public:
	double lo, hi;

	IvalF64(double _lo, double _hi) { lo = _lo; hi = _hi; };
	~IvalF64() { }

	bool Contains(double val) const;
	bool HasSubnorm() const;

	std::string Str() const;

	static IvalF64 All() { return IvalF64(-INFINITY, INFINITY); }
	static IvalF64 Const(double val) { return IvalF64(val, val); }
	static IvalF64 Subnorm() { return IvalF64(fp64next(-DBL_MIN), fp64prev(DBL_MIN)); }
	static IvalF64 SubnormNeg() { return IvalF64(fp64next(-DBL_MIN), fp64prev(-0.0)); }
	static IvalF64 SubnormPos() { return IvalF64(fp64next(0.0), fp64prev(DBL_MIN)); }

	static IvalF64 Add(IvalF64 const& lhs, IvalF64 const& rhs);
	static IvalF64 Sub(IvalF64 const& lhs, IvalF64 const& rhs);
	static IvalF64 Mul(IvalF64 const& lhs, IvalF64 const& rhs);

	static bool Inside(IvalF64 const &ival, double val);
	static bool Overlap(IvalF64 const &lhs, IvalF64 const &rhs);
};

#endif

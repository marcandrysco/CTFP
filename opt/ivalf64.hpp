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

	std::string Str() const;

	static IvalF64 All() { return IvalF64(-DBL_MAX, DBL_MAX); }
	static IvalF64 Const(double val) { return IvalF64(val, val); }

	static IvalF64 Add(IvalF64 const& lhs, IvalF64 const& rhs);
	static IvalF64 Sub(IvalF64 const& lhs, IvalF64 const& rhs);
	static IvalF64 Mul(IvalF64 const& lhs, IvalF64 const& rhs);
};

#endif

#ifndef IVALF64_HPP
#define IVALF64_HPP

/*
 * float class
 */
template <class T> class IvalFlt {
public:
	int lsb;
	T lo, hi;

	IvalFlt(T _lo, T _hi) { lo = _lo; hi = _hi; lsb = fp_lsb2(_lo, _hi); };
	IvalFlt(T _lo, T _hi, int _lsb) { lo = _lo; hi = _hi; lsb = _lsb; };
	~IvalFlt() { }

	bool Contains(T val) const;
	bool HasSubnorm() const;

	std::string Str() const;

	static IvalFlt All() { return IvalFlt(-INFINITY, INFINITY); }
	static IvalFlt Const(T val) { return IvalFlt(val, val); }
	static IvalFlt SubnormNeg() { return IvalFlt(fp_next<T>(std::numeric_limits<T>::min()), fp_prev<T>(-0.0)); }
	static IvalFlt SubnormPos() { return IvalFlt(fp_next<T>(-0.0), fp_prev<T>(std::numeric_limits<T>::min())); }

	static IvalFlt Abs(IvalFlt const& in);
	static IvalFlt Add(IvalFlt const& lhs, IvalFlt const& rhs);
	static IvalFlt Sub(IvalFlt const& lhs, IvalFlt const& rhs);
	static IvalFlt Mul(IvalFlt const& lhs, IvalFlt const& rhs);

	static bool Overlap(IvalFlt const &lhs, IvalFlt const &rhs);
};

template class IvalFlt<double>;
template class IvalFlt<float>;

#endif

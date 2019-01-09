#ifndef IVALI64_HPP
#define IVALI64_HPP

/*
 * integer class
 */
template <class T> class IvalInt {
public:
	T lo, hi;

	IvalInt(T _lo, T _hi) { lo = _lo; hi = _hi; };
	~IvalInt() { }

	bool IsZero() const;
	bool IsOnes() const;
	bool IsConst() const;
	std::string Str() const;

	static IvalInt<T> All() { return IvalInt(0, std::numeric_limits<T>::max()); }
	static IvalInt<T> Const(T val) { return IvalInt(val, val); }
	static IvalInt<T> NumNeg();
	static IvalInt<T> NumPos();
	static IvalInt<T> NanNeg();
	static IvalInt<T> NanPos();

	static T Ones() { return std::numeric_limits<T>::max(); }

	static bool Inside(IvalInt const &ival, T val);
	static bool Overlap(IvalInt const &lhs, IvalInt const &rhs);
	static IvalInt Inter(IvalInt const &lhs, IvalInt const &rhs);
};

using IvalI64 = IvalInt<uint64_t>;
template class IvalInt<uint64_t>;

#endif

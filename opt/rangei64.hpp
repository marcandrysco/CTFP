#ifndef RANGEI64_H
#define RANGEI64_H

/*
 * integer range class
 */
template <class T> class RangeInt {
public:
	std::vector<IvalInt<T>> ivals;

	RangeInt() { }
	RangeInt(IvalInt<T> const& ival) { ivals.push_back(ival); }
	~RangeInt() { }

	bool IsUndef() const;

	std::string Str() const;

	static RangeInt<T> All() { return RangeInt(IvalInt<T>::All()); }
	static RangeInt<T> None() { return RangeInt<T>(); }
	static RangeInt<T> Const(T val) { return RangeInt<T>(IvalInt<T>::Const(val)); }

	template <class U> static RangeInt<T> FromFlt(const RangeFlt<U> &flt);

	static RangeInt<T> And(RangeInt const& lhs, RangeInt const& rhs);
	static RangeInt<T> Or(RangeInt const& lhs, RangeInt const& rhs);
	static RangeInt<T> Xor(RangeInt const& lhs, RangeInt const& rhs);

	static RangeInt<T> Select(RangeBool const& cond, RangeInt const& lhs, RangeInt const& rhs);
};

template class RangeInt<uint64_t>;
template class RangeInt<uint32_t>;

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

	std::string Str() const;

	static RangeVecInt<T> All(uint32_t width) { RangeVecInt<T> res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeInt<T>::All()); return res; }
	static RangeVecInt<T> Const(T val, uint32_t width) { RangeVecInt<T> res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeInt<T>::Const(val)); return res; }

	static RangeVecInt<T> And(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs);
	static RangeVecInt<T> Or(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs);
	static RangeVecInt<T> Xor(const RangeVecInt<T> &lhs, const RangeVecInt<T> &rhs);

	template <class U> static RangeVecInt<T> FromFlt(RangeVecFlt<U> const& flt);

	static RangeVecInt<T> Select(RangeVecBool const& cond, RangeVecInt<T> const& lhs, RangeVecInt<T> const& rhs);
};

template class RangeVecInt<uint64_t>;
template class RangeVecInt<uint32_t>;

#endif

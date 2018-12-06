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

	std::string Str() const;

	static RangeInt<T> All() { return RangeInt(IvalInt<T>::All()); }
	static RangeInt<T> None() { return RangeInt<T>(); }
	static RangeInt<T> Const(T val) { return RangeInt<T>(IvalInt<T>::Const(val)); }

	static RangeInt<T> FromF64(const RangeF64 &flt);

	static RangeInt<T> And(RangeInt const& lhs, RangeInt const& rhs);
	static RangeInt<T> Or(RangeInt const& lhs, RangeInt const& rhs);
	static RangeInt<T> Xor(RangeInt const& lhs, RangeInt const& rhs);

	static RangeInt<T> Select(RangeBool const& cond, RangeInt const& lhs, RangeInt const& rhs);
};

using RangeI64 = RangeInt<uint64_t>;
template class RangeInt<uint64_t>;


/*
 * vector of 64-bit integers range class
 */
class RangeVecI64 {
public:
	std::vector<RangeI64> scalars;

	RangeVecI64() { }
	RangeVecI64(RangeI64 scalar) { scalars.push_back(scalar); }
	RangeVecI64(std::vector<RangeI64> _scalars) { scalars = _scalars; }
	~RangeVecI64() { }

	std::string Str() const;

	static RangeVecI64 All(uint32_t width) { RangeVecI64 res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeI64::All()); return res; }
	static RangeVecI64 Const(uint64_t val, uint32_t width) { RangeVecI64 res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeI64::Const(val)); return res; }

	static RangeVecI64 Add(const RangeVecI64 &lhs, const RangeVecI64 &rhs);

	static RangeVecI64 And(const RangeVecI64 &lhs, const RangeVecI64 &rhs);
	static RangeVecI64 Or(const RangeVecI64 &lhs, const RangeVecI64 &rhs);
	static RangeVecI64 Xor(const RangeVecI64 &lhs, const RangeVecI64 &rhs);

	static RangeVecI64 FromF64(const RangeVecF64 &in);

	static RangeVecI64 Select(RangeVecBool const& cond, RangeVecI64 const& lhs, RangeVecI64 const& rhs);
};

#endif

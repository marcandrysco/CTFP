#ifndef RANGEF64_HPP
#define RANGEF64_HPP

template <class T> class RangeFlt {
public:
	bool nan;
	std::vector<IvalFlt<T>> ivals;

	RangeFlt(bool _nan) { nan = _nan; }
	RangeFlt(IvalFlt<T> const& ival, bool _nan) { ivals.push_back(ival); nan = _nan; }
	RangeFlt(std::vector<IvalFlt<T>> const& _ivals, bool _nan) { ivals = _ivals; nan = _nan; }
	~RangeFlt() { }

	bool Contains(T val) const;
	bool HasSubnorm() const;

	T Lower() const;
	T Upper() const;
	RangeFlt Below(T bound, bool nan) const;
	RangeFlt Above(T bound, bool nan) const;

	std::string Str() const;

	static RangeFlt All() { return RangeFlt(IvalFlt<T>::All(), true); }
	static RangeFlt Limit() { return RangeFlt(std::vector<IvalFlt<T>>{ IvalFlt<T>(-10e10, -10e-10, -20), IvalFlt<T>(10e-10, 10e10, -20) }, false); }
	static RangeFlt None() { return RangeFlt(false); }
	static RangeFlt Const(double val) { return isnan(val) ? RangeFlt<T>(true) : RangeFlt(IvalFlt<T>::Const(val), false); }

	static RangeFlt FromI64(const RangeI64 &flt);

	static RangeFlt Add(const RangeFlt &lhs, const RangeFlt &rhs);
	static RangeFlt Sub(const RangeFlt &lhs, const RangeFlt &rhs);
	static RangeFlt Mul(const RangeFlt &lhs, const RangeFlt &rhs);

	static RangeBool CmpOGT(RangeFlt const& lhs, RangeFlt const& rhs);

	static RangeFlt Select(RangeBool const& cond, RangeFlt const& lhs, RangeFlt const& rhs);
};

template class RangeFlt<double>;
template class RangeFlt<float>;

/*
 * vector of 64-bit floats range class
 */
class RangeVecF64 {
public:
	std::vector<RangeF64> scalars;

	RangeVecF64() { }
	RangeVecF64(RangeF64 scalar) { scalars.push_back(scalar); }
	RangeVecF64(std::vector<RangeF64> _scalars) { scalars = _scalars; }
	~RangeVecF64() { }

	bool HasSubnorm() const;

	std::string Str() const;

	static RangeVecF64 All(uint32_t width) { RangeVecF64 res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeF64::All()); return res; }
	static RangeVecF64 Const(double val, uint32_t width) { RangeVecF64 res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeF64::Const(val)); return res; }

	static RangeVecF64 FromI64(const RangeVecI64 &in);

	static RangeVecF64 Add(const RangeVecF64 &lhs, const RangeVecF64 &rhs);
	static RangeVecF64 Sub(const RangeVecF64 &lhs, const RangeVecF64 &rhs);
	static RangeVecF64 Mul(const RangeVecF64 &lhs, const RangeVecF64 &rhs);

	static RangeVecBool CmpOGT(RangeVecF64 const& lhs, RangeVecF64 const& rhs);

	static RangeVecF64 Select(RangeVecBool const& cond, RangeVecF64 const& lhs, RangeVecF64 const& rhs);
};

#endif

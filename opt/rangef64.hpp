#ifndef RANGEF64_HPP
#define RANGEF64_HPP

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

	bool IsUndef() const;
	bool Contains(T val) const;
	bool HasSubnorm() const;

	T Lower() const;
	T Upper() const;
	RangeFlt Below(T bound, bool nan) const;
	RangeFlt Above(T bound, bool nan) const;

	T GetConst() const;
	std::string Str() const;

	static RangeFlt Undef() { return RangeFlt(false); }
	static RangeFlt All() { return RangeFlt(IvalFlt<T>::All(), true); }
	static RangeFlt Limit() { return RangeFlt(std::vector<IvalFlt<T>>{ IvalFlt<T>(-10e10, -10e-10, -20), IvalFlt<T>(10e-10, 10e10, -20) }, false); }
	static RangeFlt None() { return RangeFlt(false); }
	static RangeFlt Const(double val) { return isnan(val) ? RangeFlt<T>(true) : RangeFlt(IvalFlt<T>::Const(val), false); }

	static RangeFlt Abs(RangeFlt const& in);
	template <class U> static RangeFlt<T> FromInt(const RangeInt<U> &in);

	static RangeFlt Add(const RangeFlt &lhs, const RangeFlt &rhs);
	static RangeFlt Sub(const RangeFlt &lhs, const RangeFlt &rhs);
	static RangeFlt Mul(const RangeFlt &lhs, const RangeFlt &rhs);

	static RangeBool CmpUNE(RangeFlt const& lhs, RangeFlt const& rhs);
	static RangeBool CmpOGT(RangeFlt const& lhs, RangeFlt const& rhs);
	static RangeBool CmpOLT(RangeFlt const& lhs, RangeFlt const& rhs);
	static RangeBool CmpOEQ(RangeFlt const& lhs, RangeFlt const& rhs);

	static RangeFlt Select(RangeBool const& cond, RangeFlt const& lhs, RangeFlt const& rhs);
};

template class RangeFlt<double>;
template class RangeFlt<float>;


template <class T> class RangeVecFlt {
public:
	std::vector<RangeFlt<T>> scalars;

	RangeVecFlt() { }
	RangeVecFlt(RangeFlt<T> scalar) { scalars.push_back(scalar); }
	RangeVecFlt(std::vector<RangeFlt<T>> _scalars) { scalars = _scalars; }
	~RangeVecFlt() { }

	bool HasSubnorm() const;

	std::string Str() const;

	static RangeVecFlt Undef(uint32_t width) { RangeVecFlt res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeFlt<T>::Undef()); return res; }
	static RangeVecFlt All(uint32_t width) { RangeVecFlt res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeFlt<T>::All()); return res; }
	static RangeVecFlt Const(T val, uint32_t width) { RangeVecFlt res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeFlt<T>::Const(val)); return res; }

	static RangeVecFlt<T> Abs(RangeVecFlt<T> const& in);
	template <class U> static RangeVecFlt<T> FromInt(RangeVecInt<U> const &in);

	static RangeVecFlt<T> Add(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs);
	static RangeVecFlt<T> Sub(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs);
	static RangeVecFlt<T> Mul(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs);

	static RangeVecBool CmpOLT(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs);
	static RangeVecBool CmpOGT(RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs);

	static RangeVecFlt Select(RangeVecBool const& cond, RangeVecFlt<T> const& lhs, RangeVecFlt<T> const& rhs);
};

template class RangeVecFlt<double>;
template class RangeVecFlt<float>;

#endif

#ifndef RANGEF64_HPP
#define RANGEF64_HPP

/*
 * 64-bit float range class
 */
class RangeF64 {
public:
	bool nan;
	std::vector<IvalF64> ivals;

	RangeF64(bool _nan) { nan = _nan; }
	RangeF64(IvalF64 const& ival, bool _nan) { ivals.push_back(ival); nan = _nan; }
	~RangeF64() { }

	bool Contains(double val) const;
	bool HasSubnorm() const;

	std::string Str() const;

	static RangeF64 All() { return RangeF64(IvalF64::All(), true); }
	static RangeF64 Const(double val) { return isnan(val) ? RangeF64(true) : RangeF64(IvalF64::Const(val), false); }

	static RangeF64 Add(const RangeF64 &lhs, const RangeF64 &rhs);
	static RangeF64 Sub(const RangeF64 &lhs, const RangeF64 &rhs);
	static RangeF64 Mul(const RangeF64 &lhs, const RangeF64 &rhs);
};

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

	static RangeVecF64 Add(const RangeVecF64 &lhs, const RangeVecF64 &rhs);
	static RangeVecF64 Sub(const RangeVecF64 &lhs, const RangeVecF64 &rhs);
	static RangeVecF64 Mul(const RangeVecF64 &lhs, const RangeVecF64 &rhs);
};

#endif

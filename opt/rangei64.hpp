#ifndef RANGEI64_H
#define RANGEI64_H

/*
 * 64-bit integer range class
 */
class RangeI64 {
public:
	std::vector<IvalI64> ivals;

	RangeI64(IvalI64 const& ival) { ivals.push_back(ival); }
	~RangeI64() { }

	static RangeI64 All() { return RangeI64(IvalI64::All()); }
	static RangeI64 Const(uint64_t val) { return RangeI64(IvalI64::Const(val)); }
};

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

	static RangeVecI64 All(uint32_t width) { RangeVecI64 res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeI64::All()); return res; }
	static RangeVecI64 Const(uint64_t val, uint32_t width) { RangeVecI64 res; for(uint32_t i = 0; i < width; i++) res.scalars.push_back(RangeI64::Const(val)); return res; }

	static RangeVecI64 Add(const RangeVecI64 &lhs, const RangeVecI64 &rhs);
};

#endif

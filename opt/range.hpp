#ifndef RANGE_HPP
#define RANGE_HPP


/*
 * Undefined range class
 */
class RangeUndef {
public:
	RangeUndef() { };
	~RangeUndef() { };
};

/*
 * General range class
 */
class Range {
public:
	std::variant<RangeUndef, RangeVecI64, RangeVecF64> var;

	Range() { var = RangeUndef(); }
	Range(RangeUndef _range) { var = _range; }
	Range(RangeVecI64 _range) { var = _range; }
	Range(RangeVecF64 _range) { var = _range; }
	Range(Type type);
	~Range() { }

	std::string Str() const;

	static Range AllI64(uint32_t width) { return Range(RangeVecI64::All(width)); }
	static Range AllF64(uint32_t width) { return Range(RangeVecF64::All(width)); }
	static Range ConstI64(uint64_t val) { return Range(RangeVecI64(RangeI64::Const(val))); }
	static Range ConstF64(double val) { return Range(RangeVecF64(RangeF64::Const(val))); }

	static Range Add(const Range &lhs, const Range &rhs, Type type);
	static Range Sub(const Range &lhs, const Range &rhs, Type type);
};

#endif

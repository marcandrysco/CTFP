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
 * boolean range class
 */
class RangeBool {
public:
	bool istrue, isfalse;

	RangeBool() { istrue = false; isfalse = false; }
	RangeBool(bool val) { istrue = val; isfalse = !val; }
	RangeBool(bool _istrue, bool _isfalse) { istrue = _istrue; isfalse = _isfalse; }
	~RangeBool() { }

	bool IsTrue() const { return !isfalse; }
	bool IsFalse() const { return !istrue; }

	std::string Str() const;

	static RangeBool And(RangeBool const& lhs, RangeBool const& rhs) {
		return RangeBool(lhs.istrue && rhs.istrue, lhs.isfalse || rhs.isfalse);
	}

	static RangeBool Or(RangeBool const& lhs, RangeBool const& rhs) {
		return RangeBool(lhs.istrue || rhs.istrue, lhs.isfalse && rhs.isfalse);
	}

	static RangeBool Xor(RangeBool const& lhs, RangeBool const& rhs) {
		return RangeBool((lhs.istrue && rhs.isfalse) || (lhs.isfalse && rhs.istrue), (lhs.istrue && rhs.istrue) || (lhs.isfalse && rhs.isfalse));
	}
};

/*
 * vector of boolean range class
 */
class RangeVecBool {
public:
	std::vector<RangeBool> scalars;

	RangeVecBool() { }
	~RangeVecBool() { }

	bool IsTrue() const;
	bool IsFalse() const;

	std::string Str() const;

	static RangeVecBool And(RangeVecBool const& lhs, RangeVecBool const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecBool res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeBool::And(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	static RangeVecBool Or(RangeVecBool const& lhs, RangeVecBool const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecBool res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeBool::Or(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}

	static RangeVecBool Xor(RangeVecBool const& lhs, RangeVecBool const& rhs) {
		assert(lhs.scalars.size() == rhs.scalars.size());

		RangeVecBool res;

		for(size_t i = 0; i < lhs.scalars.size(); i++)
			res.scalars.push_back(RangeBool::Xor(lhs.scalars[i], rhs.scalars[i]));

		return res;
	}
};

/*
 * General range class
 */
class Range {
public:
	std::variant<RangeUndef, RangeVecBool, RangeVecI32, RangeVecI64, RangeVecF32, RangeVecF64> var;

	Range() { var = RangeUndef(); }
	Range(RangeUndef _range) { var = _range; }
	Range(RangeVecBool _range) { var = _range; }
	Range(RangeVecI32 _range) { var = _range; }
	Range(RangeVecI64 _range) { var = _range; }
	Range(RangeVecF32 _range) { var = _range; }
	Range(RangeVecF64 _range) { var = _range; }
	Range(Type type);
	~Range() { }

	bool HasSubnorm() const;

	std::string Str() const;

	static Range AllI64(uint32_t width) { return Range(RangeVecI64::All(width)); }
	static Range AllF64(uint32_t width) { return Range(RangeVecF64::All(width)); }
	static Range ConstI64(uint64_t val) { return Range(RangeVecI64(RangeI64::Const(val))); }
	static Range ConstF64(double val) { return Range(RangeVecF64(RangeF64::Const(val))); }

	static Range ItoF(const Range &in, Type type);
	static Range FtoI(const Range &in, Type type);

	static Range Abs(Range const& in, Type type);

	static Range Add(const Range &lhs, const Range &rhs, Type type);
	static Range Sub(const Range &lhs, const Range &rhs, Type type);
	static Range Mul(const Range &lhs, const Range &rhs, Type type);

	static Range And(const Range &lhs, const Range &rhs, Type type);
	static Range Or(const Range &lhs, const Range &rhs, Type type);
	static Range Xor(const Range &lhs, const Range &rhs, Type type);

	static Range CmpOLT(Range const &lhs, Range const &rhs, Type type);
	static Range CmpOGT(Range const &lhs, Range const &rhs, Type type);

	static Range Select(Range const& cond, Range const& lhs, Range const& rhs, Type type);
};

#endif

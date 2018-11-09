#ifndef RANGE_HPP
#define RANGE_HPP

/*
 * class prototypes
 */
class RangeF64;
class RangeI64;


/*
 * empty range
 */
class RangeNone {
public:
	RangeNone() { }
	~RangeNone() { }
};

/*
 * boolean range
 */
class RangeBool {
public:
	bool istrue, isfalse;

	RangeBool() { istrue = isfalse = false; }
	RangeBool(bool _istrue, bool _isfalse) { istrue = _istrue; isfalse = _isfalse; }
	~RangeBool() { }

	std::string Str() const;

	static RangeBool All() { return RangeBool(true, true); }
	static RangeBool Empty() { return RangeBool(false, false); }
	static RangeBool Const(bool val) { return RangeBool(val, !val); }
};

/*
 * 64-bit float range
 */
class RangeF64 {
public:
	bool nan;
	std::vector<IvalF64> ivals;

	RangeF64() { nan = false; }
	RangeF64(bool _nan) { nan = _nan; }
	RangeF64(bool _nan, IvalF64 ival) { nan = _nan; ivals.push_back(ival); }
	RangeF64(bool _nan, std::vector<IvalF64> const &_ivals) { nan = _nan; ivals = _ivals; }
	~RangeF64() { }

	bool HasPos() const;
	bool HasNeg() const;
	double Lower() const;
	double Upper() const;
	RangeF64 Below(double bound, bool nan) const;
	RangeF64 Above(double bound, bool nan) const;

	RangeF64 Split() const;

	void Simplify();

	std::string Str() const;

	static RangeF64 All() { return RangeF64(true, IvalF64::All()); }
	static RangeF64 Normal() { return RangeF64(true, std::vector<IvalF64>{ IvalF64(-INFINITY, -DBL_MIN), IvalF64(-0.0, 0.0), IvalF64(DBL_MIN, INFINITY) }); }
	static RangeF64 Const(double val) { return RangeF64(false, IvalF64::Const(val)); }

	static RangeF64 Abs(RangeF64 const &in);
	static RangeF64 AbsInv(RangeF64 const &in);
	static RangeF64 Add(RangeF64 const &lhs, RangeF64 const &rhs);
	static RangeF64 Sub(RangeF64 const &lhs, RangeF64 const &rhs);
	static RangeF64 Mul(RangeF64 const &lhs, RangeF64 const &rhs);
	static RangeF64 FromI64(RangeI64 const &in);
	static RangeF64 CopySign(RangeF64 const &mag, RangeF64 const &sign);
};

/*
 * 64-bit integer range
 */
class RangeI64 {
public:
	std::vector<IvalI64> ivals;

	RangeI64() { }
	RangeI64(IvalI64 ival) { ivals.push_back(ival); }
	RangeI64(std::vector<IvalI64> _ivals) { ivals = _ivals; }
	~RangeI64() { }

	void Simplify();

	std::string Str() const;

	static RangeI64 All() { return RangeI64(IvalI64::All()); }
	static RangeI64 Const(uint64_t val) { return RangeI64(IvalI64::Const(val)); }
	static RangeI64 CastF64(RangeF64 f);

	static RangeI64 And(RangeI64 const &lhs, RangeI64 const &rhs);
	static RangeI64 Xor(RangeI64 const &lhs, RangeI64 const &rhs);
};

/*
 * range class
 */
class Range {
public:
	std::variant<RangeNone,RangeBool,RangeF64,RangeI64> var;

	Range() { var = RangeNone(); }
	Range(RangeNone _range) { var = _range; }
	Range(RangeBool _range) { var = _range; }
	Range(RangeF64 _range) { var = _range; }
	Range(RangeI64 _range) { var = _range; }
	~Range() {}

	double LowerF64() const;
	double UpperF64() const;
	Range BelowF64(double bound, bool nan) const;
	Range AboveF64(double bound, bool nan) const;

	std::string Str() const;
};

#endif

#ifndef RANGE_HPP
#define RANGE_HPP

/*
 * 64-bit range class
 */
class Range64 {
public:
	std::vector<Ival64> ivals;

	Range64() { }
	~Range64() { }

	bool Insert(Ival64 ival);
	void Insert(std::vector<Ival64> ival);

	bool HasPos() const;
	bool HasNeg() const;

	double Lower() const;
	double Upper() const;
	Range64 Below(double bound) const;
	Range64 Above(double bound) const;
	std::string Str() const;
	void Dump() const;

	static Range64 Empty();
	static Range64 All();
	static Range64 Const(double val);
	static Range64 Int(uint64_t val);

	static Range64 IntAnd(const Range64 &lhs, const Range64 &rhs);
	static Range64 IntXor(const Range64 &lhs, const Range64 &rhs);
	static Range64 FltAbs(const Range64 &in);
	static Range64 FltAdd(const Range64 &lhs, const Range64 &rhs);
	static Range64 FltCopySign(const Range64 &mag, const Range64 &sign);

	static Range64 InvFltAbs(const Range64 &in);
};

/*
 * boolean range class
 */
class RangeBool {
public:
	bool istrue, isfalse;

	RangeBool() { istrue = isfalse = false; }
	RangeBool(bool itrue, bool ifalse) { istrue = itrue; isfalse = ifalse; }
	~RangeBool() { }

	void Dump() const;

	static RangeBool Empty();
	static RangeBool Const(bool val);
};

/*
 * generic range class
 */
class Range {
public:
	std::variant<Range64, RangeBool> var;

	double Lower() const;
	double Upper() const;
	Range Below(double bound) const;
	Range Above(double bound) const;
	std::string Str() const;
	void Dump() const;

	Range() = delete;
	Range(const Range64 &inner) { var = inner; }
	Range(const RangeBool &inner) { var = inner; }
	~Range() {}

	bool Insert64(Ival64 ival);

	static Range FltAbs64(const Range &in);
	static Range FltAdd64(const Range &lhs, const Range &rhs);
	static Range FltCopySign64(const Range &mag, const Range &sign);
	static Range IntAnd64(const Range &lhs, const Range &rhs);
	static Range Xor64(const Range &lhs, const Range &rhs);

	static Range InvFltAbs64(const Range &in);
};

#endif

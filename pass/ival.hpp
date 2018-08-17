#ifndef IVAL_HPP
#define IVAL_HPP

/*
 * 64-bit interval class
 */
class Ival64 {
public:
	bool nan;
	uint64_t ilo, ihi;
	double flo, fhi;

	Ival64() {}
	~Ival64() {}

	static Ival64 All();
	static Ival64 Int(uint64_t ilo, uint64_t ihi);
	static Ival64 IntConst(uint64_t val);
	static Ival64 Flt(double flo, double fhi, bool nan);

	static Ival64 IntAnd(const Ival64 &lhs, const Ival64 &rhs);
	static Ival64 IntXor(const Ival64 &lhs, const Ival64 &rhs);
	static Ival64 IntAdd(const Ival64 &lhs, const Ival64 &rhs);

	static Ival64 FltNeg(const Ival64 &ival);
	static Ival64 FltAbs(const Ival64 &ival);
	static Ival64 FltAdd(const Ival64 &lhs, const Ival64 &rhs);

	static std::vector<Ival64> FltRelComp(const Ival64 &lhs, const Ival64 &rhs);
	static std::vector<Ival64> FltRelComp2(const std::vector<Ival64> &lhs, const std::vector<Ival64> &rhs);

	bool IsConst() const;
	bool IsValue(uint64_t val) const;
	bool IsPos() const;
	bool IsNeg() const;
	bool HasPos() const;
	bool HasNeg() const;

	void FillInt();
	void FillFlt();

	Ival64 SetPos() const;
	Ival64 SetNeg() const;

	std::string Str() const;
	void Dump() const;

	friend bool operator==(const Ival64 &lhs, const Ival64 &rhs) {
		return (lhs.nan == rhs.nan) && (lhs.flo == rhs.flo) && (lhs.fhi == rhs.fhi) && (lhs.ilo == rhs.ilo) && (lhs.ihi == rhs.ihi);
	}
};

#endif

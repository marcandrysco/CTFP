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
	static Ival64 Flt(double flo, double fhi, bool nan);

	static Ival64 IntAdd(const Ival64 &lhs, const Ival64 &rhs);

	static Ival64 FltNeg(const Ival64 &ival);
	static Ival64 FltAbs(const Ival64 &ival);
	static Ival64 FltAdd(const Ival64 &lhs, const Ival64 &rhs);

	void FillInt();
	void FillFlt();

	std::string Str() const;
	void Dump() const;
};

#endif

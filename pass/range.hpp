#ifndef RANGE_HPP
#define RANGE_HPP

/*
 * 64-bit fact class
 */
class Range64 {
public:
	std::vector<Ival64> ivals;

	double Lower() const;
	double Upper() const;
	Range64 Below(double bound) const;
	Range64 Above(double bound) const;
	std::string Str() const;
	void Dump() const;

	static Range64 Empty();
	static Range64 All();
	static Range64 Const(double val);

	static Range64 FltAbs(Range64 in);

	static Range64 FltOLT(const Range64 &lhs, const Range64 &rhs);
};

/*
 * generic range class
 */
class Range {
public:
	std::variant<Range64> var;

	double Lower() const;
	double Upper() const;
	Range Below(double bound) const;
	Range Above(double bound) const;
	std::string Str() const;
	void Dump() const;

	Range() {}
	Range(Range64 inner) { var = inner; }
	~Range() {}

	static Range FltAbs64(Range in);

	static Range FltOLT64(const Range &lhs, const Range &rhs);
};

#endif

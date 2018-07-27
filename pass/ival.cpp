#include "inc.hpp"


Ival64 Ival64::SetPos() const {
	if(IsPos())
		return Ival64::Flt(flo, fhi, nan);
	else if(IsNeg())
		return Ival64::Flt(-fhi, -flo, nan);
	else
		return Ival64::Flt(0, fmax(-flo, fhi), nan);
}

Ival64 Ival64::SetNeg() const {
	if(IsNeg())
		return Ival64::Flt(flo, fhi, nan);
	else if(IsPos())
		return Ival64::Flt(-fhi, -flo, nan);
	else
		return Ival64::Flt(fmax(flo, -fhi), 0, nan);
}


/**
 * Create an interval covering the entire space.
 *   &returns: The interval.
 */
Ival64 Ival64::All() {
	Ival64 res;

	res.nan = true;
	res.ilo = 0;
	res.ihi = UINT64_MAX;
	res.flo = -INFINITY;
	res.fhi = INFINITY;

	return res;
}

/**
 * Create an interval between integers.
 *   @ilo: The low integer.
 *   @ihi: The high integer.
 *   &returns: The interval.
 */
Ival64 Ival64::Int(uint64_t ilo, uint64_t ihi) {
	Ival64 res;

	res.ilo = ilo;
	res.ihi = ihi;
	res.FillFlt();

	return res;
}

/**
 * Create a constant, integer interval.
 *   @val: The value.
 *   &returns: The interval.
 */
Ival64 Ival64::IntConst(uint64_t val) {
	return Ival64::Int(val, val);
}

/**
 * Create an interval between floats.
 *   @ilo: The low float.
 *   @ihi: The high float.
 *   @nan: NaN flag.
 *   &returns: The interval.
 */
Ival64 Ival64::Flt(double flo, double fhi, bool nan) {
	Ival64 res;

	res.nan = nan;
	res.flo = flo;
	res.fhi = fhi;
	res.FillInt();

	return res;
}


/**
 * Integer AND.
 *   @lhs: Left-hand side.
 *   @rhs: Right-hand side.
 *   &returns: The result interval.
 */
Ival64 Ival64::IntAnd(const Ival64 &lhs, const Ival64 &rhs) {
	if(lhs.IsValue(0) || rhs.IsValue(0))
		return Ival64::IntConst(0);
	else if(lhs.IsValue(0xFFFFFFFFFFFFFFFF))
		return rhs;
	else if(rhs.IsValue(0xFFFFFFFFFFFFFFFF))
		return lhs;
	else
		return Ival64::All();
}

/**
 * Integer XOR.
 *   @lhs: Left-hand side.
 *   @rhs: Right-hand side.
 *   &returns: The result interval.
 */
Ival64 Ival64::IntXor(const Ival64 &lhs, const Ival64 &rhs) {
	if(lhs.IsConst() && rhs.IsConst())
		return Ival64::IntConst(lhs.ilo ^ rhs.ilo);
	else
		return Ival64::All();
}

/**
 * Integer addition.
 *   @lhs: Left-hand side.
 *   @rhs: Right-hand side.
 *   &returns: The result interval.
 */
Ival64 Ival64::IntAdd(const Ival64 &lhs, const Ival64 &rhs) {
	Ival64 res;
	uint64_t w1, w2, wr;

	w1 = lhs.ihi - lhs.ilo;
	w2 = rhs.ihi - rhs.ilo;
	wr = w1 + w2;
	if((wr < w1) || (wr < w2)) {
		res.ilo = 0;
		res.ihi = UINT64_MAX;
	}
	else {
		res.ilo = lhs.ilo + rhs.ilo;
		res.ihi = lhs.ihi + rhs.ihi;
	}

	res.FillFlt();

	return res;
}


/**
 * Floating-point negation.
 *   @ival: Input interval.
 *   &returns: The result interval.
 */
Ival64 Ival64::FltNeg(const Ival64 &ival) {
	Ival64 res;

	res.flo = -ival.fhi;
	res.fhi = -ival.flo;
	res.FillInt();

	return res;
}

/**
 * Floating-point absolute value.
 *   @ival: Input interval.
 *   &returns: The result interval.
 */
Ival64 Ival64::FltAbs(const Ival64 &ival) {
	if(ival.flo > 0.0)
		return ival;
	else if(ival.fhi < -0.0)
		return Ival64::FltNeg(ival);
	else
		return Ival64::Flt(0.0, fmax(-ival.flo, ival.fhi), ival.nan);
}

/**
 * Floating-point addition.
 *   @lhs: Left-hand side.
 *   @rhs: Right-hand side.
 *   &returns: The result interval.
 */
Ival64 Ival64::FltAdd(const Ival64 &lhs, const Ival64 &rhs) {
	Ival64 res;

	res.flo = lhs.flo + rhs.flo;
	res.fhi = lhs.fhi + rhs.fhi;
	res.nan = lhs.nan || rhs.nan;
	res.FillInt();

	return res;
}


/**
 * Compute the relative complement of two intervals.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The intersction set.
 */
std::vector<Ival64> Ival64::FltRelComp(const Ival64 &lhs, const Ival64 &rhs)
{
	std::vector<Ival64> res;

	if((lhs.fhi < rhs.flo) || (rhs.fhi < lhs.flo))
		res.push_back(lhs);

	if((lhs.flo < rhs.flo) && (lhs.fhi >= rhs.flo))
		res.push_back(Ival64::Flt(lhs.flo, Fact::Prev64(rhs.flo), lhs.nan));

	if((lhs.fhi > rhs.fhi) && (lhs.flo <= rhs.fhi))
		res.push_back(Ival64::Flt(Fact::Next64(rhs.fhi), lhs.fhi, lhs.nan));

	return res;
}


/**
 * Check if the interval is a constant.
 *   &returns: True if constant.
 */
bool Ival64::IsConst() const {
	return ilo == ihi;
}

/**
 * Check if the interval is given constant value.
 *   @val: The value.
 *   &returns: True if is matches.
 */
bool Ival64::IsValue(uint64_t val) const {
	return ((ilo == ihi) && (ilo == val));
}


/**
 * Check if an interval is strictly positive.
 *   &returns: True if positive.
 */
bool Ival64::IsPos() const {
	return !signbit(flo);
}

/**
 * Check if an interval is strictly negative.
 *   &returns: True if negative.
 */
bool Ival64::IsNeg() const {
	return signbit(fhi);
}

/**
 * Check if the interval has a positive value.
 *   &returns: True if possibly positive.
 */
bool Ival64::HasPos() const {
	return nan || !signbit(fhi);
}

/**
 * Check if the interval has a negative value.
 *   &returns: True if possibly negative.
 */
bool Ival64::HasNeg() const {
	return nan || signbit(flo);
}


/**
 * Fill the integer range using the float values.
 */
void Ival64::FillInt() {
	if((signbit(flo) == 0) && (signbit(fhi) == 0) && !nan) {
		memcpy(&ilo, &flo, 8);
		memcpy(&ihi, &fhi, 8);
	}
	else if((signbit(flo) == 1) && (signbit(fhi) == 1) && !nan) {
		memcpy(&ilo, &fhi, 8);
		memcpy(&ihi, &flo, 8);
	}
	else {
		ilo = 0;
		ihi = UINT64_MAX;
	}
}

/**
 * Fill the float range using the integer values.
 */
void Ival64::FillFlt() {
	if(ilo == ihi) {
		memcpy(&flo, &ilo, 8);
		memcpy(&fhi, &ihi, 8);
		nan = isnan(flo);
	}
	else if((ilo >= 0x0) && (ihi <= 0x7ff0000000000000)) {
		nan = false;
		memcpy(&flo, &ilo, 8);
		memcpy(&fhi, &ihi, 8);
	}
	else if((ilo >= 0x0) && (ihi <= 0x7fffffffffffffff)) {
		nan = true;
		fhi = INFINITY;
		memcpy(&flo, &ilo, 8);
	}
	else if((ilo >= 0x8000000000000000) && (ihi <= 0xfff0000000000000)) {
		memcpy(&flo, &ihi, 8);
		memcpy(&fhi, &ilo, 8);
	}
	else if((ilo >= 0x8000000000000000) && (ihi <= 0xffffffffffffffff)) {
		nan = true;
		flo = -INFINITY;
		memcpy(&fhi, &ilo, 8);
	}
	else {
		nan = true;
		flo = -INFINITY;
		fhi = +INFINITY;
	}
}


/**
 * Convert an interval to a string.
 *   &returns: The string.
 */
std::string Ival64::Str() const {
	char str[256];

	if(isnan(flo) && isnan(fhi))
		snprintf(str, sizeof(str), "0x%lx:0x%lx,NaN", ilo, ihi);
	else
		snprintf(str, sizeof(str), "%s0x%lx:0x%lx,%.17e:%.17e", nan ? "NaN," : "", ilo, ihi, flo, fhi);

	return std::string(str);
}

/**
 * Dump an interval to stdout.
 */
void Ival64::Dump() const {
	if(isnan(flo) && isnan(fhi))
		printf("0x%lx:0x%lx,NaN", ilo, ihi);
	else
		printf("%s0x%lx:0x%lx,%.17e:%.17e", nan ? "NaN," : "", ilo, ihi, flo, fhi);
}

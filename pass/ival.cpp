#include "inc.hpp"


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

	return res;
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
	if((ilo >= 0x0) && (ihi <= 0x7ff0000000000000)) {
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

	snprintf(str, sizeof(str), "%s0x%lx:0x%lx,%.17e:%.17e", nan ? "NaN," : "", ilo, ihi, flo, fhi);

	return std::string(str);
}

/**
 * Dump an interval to stdout.
 */
void Ival64::Dump() const {
	printf("%s0x%lx:0x%lx,%.17e:%.17e", nan ? "NaN," : "", ilo, ihi, flo, fhi);
}

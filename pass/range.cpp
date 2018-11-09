#include "inc.hpp"


/** RangeBool class **/

/**
 * Retrieve the string.
 *   &returns: The string.
 */
std::string RangeBool::Str() const {
	if(istrue && isfalse)
		return "either";
	else if(istrue && !isfalse)
		return "true";
	else if(!istrue && isfalse)
		return "false";
	else if(!istrue && !isfalse)
		return "∅";
	else
		__builtin_unreachable();
}


/** RangeF64 class **/

/**
 * Check if the range has a positive value.
 *   &returns: True if possibly positive.
 */
bool RangeF64::HasPos() const {
	if(nan)
		return true;

	for(auto const &ival : ivals) {
		if(ival.HasPos())
			return true;
	}

	return false;
}

/**
 * Check if the range has a negative value.
 *   &returns: True if possibly negative.
 */
bool RangeF64::HasNeg() const {
	if(nan)
		return true;

	for(auto const &ival : ivals) {
		if(ival.HasNeg())
			return true;
	}

	return false;
}

/**
 * Retrieve the lower value from the range.
 *   &returns: The lower value.
 */
double RangeF64::Lower() const {
	double min = DBL_MAX;

	for(auto const &ival : ivals)
		min = fmin(min, ival.lo);

	return min;
}

/**
 * Retrieve the upper value from the range.
 *   &returns: The upper value.
 */
double RangeF64::Upper() const {
	double max = -DBL_MAX;

	for(auto const &ival : ivals)
		max = fmax(max, ival.hi);

	return max;
}

/**
 * Compute a 64-bit range below a bound.
 *   @bound: The bound.
 *   @nan: NaN flag.
 *   &returns: The bounded range.
 */
RangeF64 RangeF64::Below(double bound, bool nan) const {
	RangeF64 res(nan);

	for(auto const &ival : ivals) {
		if(ival.lo < bound)
			res.ivals.push_back(IvalF64(ival.lo, std::fmin(ival.hi, bound)));
	}

	return res;
}

/**
 * Compute a 64-bit range above a bound.
 *   @bound: The bound.
 *   @nan: NaN flag.
 *   &returns: The bounded range.
 */
RangeF64 RangeF64::Above(double bound, bool nan) const {
	RangeF64 res(nan);

	for(auto const &ival : ivals) {
		if(ival.hi > bound)
			res.ivals.push_back(IvalF64(std::fmax(ival.lo, bound), ival.hi));
	}

	return res;
}


/**
 * Split a range to isolate infinities.
 *   &returns: The split range.
 */
RangeF64 RangeF64::Split() const {
	RangeF64 res(nan);
	double lo, hi;
	bool pinf = false, ninf = false;

	for(auto const &ival : ivals) {
		lo = ival.lo;
		hi = ival.hi;

		if(hi == INFINITY) {
			pinf = true;
			hi = DBL_MAX;
		}

		if(lo == -INFINITY) {
			ninf = true;
			lo = -DBL_MAX;
		}

		if(lo <= hi) {
			if((lo < -0.0) && (hi > 0.0)) {
				res.ivals.push_back(IvalF64(lo, -F64MIN));
				res.ivals.push_back(IvalF64(-0.0, 0.0));
				res.ivals.push_back(IvalF64(F64MIN, hi));
			}
			else
				res.ivals.push_back(IvalF64(lo, hi));
		}
	}

	if(pinf)
		res.ivals.push_back(IvalF64::Const(INFINITY));

	if(ninf)
		res.ivals.push_back(IvalF64::Const(-INFINITY));

	return res;
}


/**
 * Simplify a range.
 */
void RangeF64::Simplify() {
	for(auto lhs = ivals.begin(); lhs != ivals.end(); lhs++) {
		auto rhs = lhs + 1;
		while(rhs != ivals.end()) {
			if(IvalF64::Overlap(*lhs, *rhs) || IvalF64::Adjacent(*lhs, *rhs)) {
				lhs->lo = f64min(lhs->lo, rhs->lo);
				lhs->hi = f64max(lhs->hi, rhs->hi);
				rhs = ivals.erase(rhs);
			}
			else
				rhs++;
		}
	}
}


/**
 * Retrieve the string.
 *   &returns: The string.
 */
std::string RangeF64::Str() const {
	std::string str;

	for(auto const &ival : ivals)
		str += ((str.length() > 0) ? ", " : "") + ival.Str();

	if(nan)
		str += (str.length() > 0) ? ", NaN" : "NaN";

	return str;
}


/**
 * Compute the absolute value.
 *   @in: The input range.
 *   &returns: The output range.
 */
RangeF64 RangeF64::Abs(RangeF64 const &in) {
	RangeF64 res(in.nan);

	for(auto const &ival : in.ivals) {
		if(ival.lo > 0.0)
			res.ivals.push_back(ival);
		else if(ival.hi < 0.0)
			res.ivals.push_back(ival.Neg());
		else
			res.ivals.push_back(IvalF64(0.0, fmax(-ival.lo, ival.hi)));
	}

	return res;
}

/**
 * Compute the inverse of an absolute value.
 *   @in: The input.
 *   &returns: The inverse absolute value.
 */
RangeF64 RangeF64::AbsInv(RangeF64 const &in) {
	RangeF64 res(in.nan);

	for(auto const &ival : in.ivals) {
		if((ival.lo > 0.0) || (ival.hi < -0.0)) {
			res.ivals.push_back(IvalF64(ival.lo, ival.hi));
			res.ivals.push_back(IvalF64(-ival.hi, -ival.lo));
		}
		else  {
			double max = fmax(-ival.lo, ival.hi);

			res.ivals.push_back(IvalF64(-max, max));
		}
	}

	return res;
}


/**
 * Compute an addition.
 *   @lhs: The left-hand range.
 *   @rhs: The right-hand range.
 *   &returns: The result range.
 */
RangeF64 RangeF64::Add(RangeF64 const &lhs, RangeF64 const &rhs) {
	RangeF64 res(lhs.nan || rhs.nan);

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals)
			res.ivals.push_back(IvalF64::Add(x, y));
	}

	return res;
}

/**
 * Compute a subtraction.
 *   @lhs: The left-hand range.
 *   @rhs: The right-hand range.
 *   &returns: The result range.
 */
RangeF64 RangeF64::Sub(RangeF64 const &lhs, RangeF64 const &rhs) {
	RangeF64 res(lhs.nan || rhs.nan);

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals)
			res.ivals.push_back(IvalF64::Sub(x, y));
	}

	return res;
}

/**
 * Compute a multiply.
 *   @lhs: The left-hand range.
 *   @rhs: The right-hand range.
 *   &returns: The result range.
 */
RangeF64 RangeF64::Mul(RangeF64 const &lhs, RangeF64 const &rhs) {
	RangeF64 res(lhs.nan || rhs.nan);

	for(auto const &x : lhs.Split().ivals) {
		for(auto const &y : rhs.Split().ivals) {
			if((x.IsZero() && y.IsInf()) || (x.IsInf() && y.IsZero()))
				res.nan = true;
			else
				res.ivals.push_back(IvalF64::Mul(x, y));
		}
	}

	//printf("before: %s\n", res.Str().c_str());
	res.Simplify();
	//printf("after: %s\n", res.Str().c_str());

	return res;
}


/**
 * Compute copysign of a value.
 *   @mag: The magnitude range.
 *   @sign: The sign range.
 *   &returns: The output range.
 */
RangeF64 RangeF64::CopySign(RangeF64 const &mag, RangeF64 const &sign) {
	RangeF64 res(mag.nan);

	if(sign.HasPos()) {
		for(auto const &ival : mag.ivals)
			res.ivals.push_back(ival.SetPos());
	}

	if(sign.HasNeg()) {
		for(auto const &ival : mag.ivals)
			res.ivals.push_back(ival.SetNeg());
	}

	res.Simplify();

	return res;
}

/**
 * Cast a 64-bit integer range to 64-bit float.
 *   @in: The input integer range.
 *   &returns: The output float range.
 */
RangeF64 RangeF64::FromI64(RangeI64 const &in)
{
	double lo, hi;
	RangeF64 res(false);
	static IvalI64 pos(0x0000000000000000, 0x7FF0000000000000);
	static IvalI64 neg(0x8000000000000000, 0xFFF0000000000000);

	for(auto &ival : in.ivals) {
		if(IvalI64::Overlap(ival, IvalI64(0x7FF0000000000001, 0x7FFFFFFFFFFFFFFF)))
			res.nan = true;
		else if(IvalI64::Overlap(ival, IvalI64(0xFFF0000000000001, 0xFFFFFFFFFFFFFFFF)))
			res.nan = true;

		if(IvalI64::Overlap(ival, pos)) {
			IvalI64 inter = IvalI64::Inter(ival, pos);
			memcpy(&lo, &inter.lo, 8);
			memcpy(&hi, &inter.hi, 8);
			res.ivals.push_back(IvalF64(lo, hi));
		}

		if(IvalI64::Overlap(ival, neg)) {
			IvalI64 inter = IvalI64::Inter(ival, neg);
			memcpy(&hi, &inter.lo, 8);
			memcpy(&lo, &inter.hi, 8);
			res.ivals.push_back(IvalF64(lo, hi));
		}
	}

	return res;
}


/** RangeI64 class **/

/**
 * Simplify a range.
 */
void RangeI64::Simplify() {
	for(auto lhs = ivals.begin(); lhs != ivals.end(); lhs++) {
		auto rhs = lhs + 1;
		while(rhs != ivals.end()) {
			if(IvalI64::Overlap(*lhs, *rhs) || IvalI64::Adjacent(*lhs, *rhs)) {
				lhs->lo = std::min<uint64_t>(lhs->lo, rhs->lo);
				lhs->hi = std::max<uint64_t>(lhs->hi, rhs->hi);
				rhs = ivals.erase(rhs);
			}
			else
				rhs++;
		}
	}
}


/**
 * Retrieve the string.
 *   &returns: The string.
 */
std::string RangeI64::Str() const {
	std::string str;

	for(auto const &ival : ivals)
		str += ((str.length() > 0) ? ", " : "") + ival.Str();

	return str;
}


/**
 * Cast a 64-bit float range to 64-bit integer.
 *   @in: The input float range.
 *   &returns: The output integer range.
 */
RangeI64 RangeI64::CastF64(RangeF64 in)
{
	RangeI64 res;

	if(in.nan) {
		res.ivals.push_back(IvalI64(0x7FF0000000000001, 0x7FFFFFFFFFFFFFFF));
		res.ivals.push_back(IvalI64(0xFFF0000000000001, 0xFFFFFFFFFFFFFFFF));
	}

	for(auto const &ival : in.ivals) {
		uint64_t lo, hi;

		memcpy(&lo, &ival.lo, 8);
		memcpy(&hi, &ival.hi, 8);

		if(signbit(ival.hi) == 1)
			res.ivals.push_back(IvalI64(hi, lo));
		else if(signbit(ival.lo) == 0)
			res.ivals.push_back(IvalI64(lo, hi));
		else {
			res.ivals.push_back(IvalI64(0x8000000000000000, lo));
			res.ivals.push_back(IvalI64(0x0000000000000000, hi));
		}
	}

	res.Simplify();

	return res;
}


/**
 * Compute a bitwise AND.
 *   @lhs: The left-hand range.
 *   @rhs: The right-hand range.
 *   &returns: The output range.
 */
RangeI64 RangeI64::And(RangeI64 const &lhs, RangeI64 const &rhs)
{
	RangeI64 res;

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals) {
			if(x.IsConst() && y.IsConst())
				res.ivals.push_back(IvalI64::Const(x.lo & y.lo));
			else if(x.IsZero() || y.IsZero())
				res.ivals.push_back(IvalI64::Const(0));
			else if(x.IsOnes())
				res.ivals.push_back(y);
			else if(y.IsOnes())
				res.ivals.push_back(x);
			else
				res.ivals.push_back(IvalI64::All());
		}
	}

	res.Simplify();

	return res;
}

/**
 * Compute a bitwise XOR.
 *   @lhs: The left-hand range.
 *   @rhs: The right-hand range.
 *   &returns: The output range.
 */
RangeI64 RangeI64::Xor(RangeI64 const &lhs, RangeI64 const &rhs)
{
	RangeI64 res;

	for(auto const &x : lhs.ivals) {
		for(auto const &y : rhs.ivals) {
			if(x.IsConst() && y.IsConst())
				res.ivals.push_back(IvalI64::Const(x.lo ^ y.lo));
			else
				res.ivals.push_back(IvalI64::All());
		}
	}

	return res;
}


/** Range class **/

/**
 * Retrieve the lower 64-bit float value.
 *   &returns: The lower value.
 */
double Range::LowerF64() const {
	if(std::holds_alternative<RangeF64>(var))
		return std::get<RangeF64>(var).Lower();
	else
		fatal("LowerF64 called on non-F64 range.");
}

/**
 * Retrieve the upper 64-bit float value.
 *   &returns: The upper value.
 */
double Range::UpperF64() const {
	if(std::holds_alternative<RangeF64>(var))
		return std::get<RangeF64>(var).Upper();
	else
		fatal("UpperF64 called on non-F64 range.");
}

/**
 * Compute a range below a 64-bit floating-point bound.
 *   @bound: The bound.
 *   @nan: NaN flag.
 *   &returns: The bounded range.
 */
Range Range::BelowF64(double bound, bool nan) const {
	if(std::holds_alternative<RangeF64>(var))
		return std::get<RangeF64>(var).Below(bound, nan);
	else
		fatal("BelowF64 called on non-F64 range.");
}

/**
 * Compute a range above a 64-bit floating-point bound.
 *   @bound: The bound.
 *   @nan: NaN flag.
 *   &returns: The bounded range.
 */
Range Range::AboveF64(double bound, bool nan) const {
	if(std::holds_alternative<RangeF64>(var))
		return std::get<RangeF64>(var).Above(bound, nan);
	else
		fatal("BelowF64 called on non-F64 range.");
}


/**
 * Retrieve the string from the range.
 *   &returns: The string.
 */
std::string Range::Str() const {
	if(std::holds_alternative<RangeBool>(var))
		return std::get<RangeBool>(var).Str();
	else if(std::holds_alternative<RangeF64>(var))
		return std::get<RangeF64>(var).Str();
	else if(std::holds_alternative<RangeI64>(var))
		return std::get<RangeI64>(var).Str();
	else
		fatal("stub");
}

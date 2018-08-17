#include "inc.hpp"




/** Range64 Class **/

/**
 * Insert an interval into the range.
 *   @ival: The interval.
 *   &returns: True if inserted, false if duplicated.
 */
bool Range64::Insert(Ival64 ival) {
	for(auto const &iter : ivals) {
		if(ival == iter)
			return false;
	}

	ivals.push_back(ival);

	return true;
}

/**
 * Insert a set of intervals into the range.
 *   @ival: The vector of intervals.
 */
void Range64::Insert(std::vector<Ival64> ival) {
	for(auto const &iter : ival)
		Insert(iter);
}


/**
 * Check if the range has a positive value.
 *   &returns: True if possibly positive.
 */
bool Range64::HasPos() const {
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
bool Range64::HasNeg() const {
	for(auto const &ival : ivals) {
		if(ival.HasNeg())
			return true;
	}

	return false;
}


/**
 * Retrieve the lower bound of a 64-bit range.
 *   &returns: The lower bound.
 */
double Range64::Lower() const {
	double lower = DBL_MAX;

	for(auto const &ival : ivals)
		lower = fmin(lower, ival.flo);

	return lower;
}

/**
 * Retrieve the upper bound of a 64-bit range.
 *   &returns: The upper bound.
 */
double Range64::Upper() const {
	double upper = -DBL_MAX;

	for(auto const &ival : ivals)
		upper = fmax(upper, ival.fhi);

	return upper;
}

/**
 * Bound a set of intervals below by a bound.
 *   @bound: The bound.
 *   &returns: The bounded range.
 */
Range64 Range64::Below(double bound) const {
	Range64 res;

	for(auto const &ival : ivals) {
		if(ival.flo < bound)
			res.ivals.push_back(Ival64::Flt(ival.flo, std::fmin(ival.fhi, bound), ival.nan));
	}

	return res;
}

/**
 * Bound a set of intervals above by a bound.
 *   @bound: The bound.
 *   &returns: The bounded range.
 */
Range64 Range64::Above(double bound) const {
	Range64 res;

	for(auto const &ival : ivals) {
		if(ival.fhi > bound)
			res.ivals.push_back(Ival64::Flt(std::fmax(ival.flo, bound), ival.fhi, ival.nan));
	}

	return res;
}

/**
 * Create a string format of the 64-bit range.
 *   &returns: The string.
 */
std::string Range64::Str() const {
	std::string str;

	for(auto ival = ivals.begin(); ival != ivals.end(); ival++)
		str += ival->Str() + ",";

	if(str.length() > 0)
		str.erase(str.length() - 1);
	else
		str = "∅";

	return str;
}

/**
 * Dump an 64-bit range to stdout.
 */
void Range64::Dump() const {
	if(ivals.size() > 0) {
		for(auto const &ival : ivals) {
			if(&ival != &*ivals.begin())
				printf(", ");

			ival.Dump();
		}
	}
	else
		printf("∅");
}


/**
 * Compute the AND of two 64-bit ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new range.
 */
Range64 Range64::IntAnd(const Range64 &lhs, const Range64 &rhs) {
	Range64 res;

	for(auto &x: lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(Ival64::IntAnd(x, y));
	}

	return res;
}

/**
 * Compute the xor of two 64-bit ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new range.
 */
Range64 Range64::IntXor(const Range64 &lhs, const Range64 &rhs) {
	Range64 res;

	for(auto &x: lhs.ivals) {
		for(auto &y: rhs.ivals)
			res.ivals.push_back(Ival64::IntXor(x, y));
	}

	return res;
}

/**
 * Compute the next 64-bit range for a floating-point absolute value.
 *   @in: The input range.
 *   &returns: The new range.
 */
Range64 Range64::FltAbs(const Range64 &in) {
	Range64 res;

	for(auto &ival : in.ivals)
		res.ivals.push_back(Ival64::FltAbs(ival));

	return res;
}

/**
 * Compute the FP addition of two 64-bit ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new range.
 */
Range64 Range64::FltAdd(const Range64 &lhs, const Range64 &rhs) {
	Range64 res;

	for(auto &x: lhs.ivals) {
		for(auto &y: rhs.ivals) {
			int exp;
			double min = fmin(fmin(fabs(x.flo), fabs(x.fhi)), fmin(fabs(y.flo), fabs(y.fhi)));

			frexp(min, &exp);
			exp -= 53;
			min = ldexp(1.0, exp);

			if(min >= 0) {
				printf("MIN: %e\n", min);
				res.Insert(
					//Ival64::FltRelComp(
						Ival64::FltAdd(x, y)//,
						//Ival64::Flt(DBL_MIN, min, false)
					//)
				);
			}
			else
				res.Insert(Ival64::FltAdd(x, y));
		}
	}

	return res;
}


/**
 * Compute a 64-bit range for copysign.
 *   @mag: The magnitude.
 *   @sign: The sign.
 *   &returns: The range.
 */
Range64 Range64::FltCopySign(const Range64 &mag, const Range64 &sign) {
	Range64 res;

	if(sign.HasPos()) {
		for(auto const &ival : mag.ivals)
			res.Insert(ival.SetPos());
	}

	if(sign.HasNeg()) {
		for(auto const &ival : mag.ivals)
			res.Insert(ival.SetNeg());
	}

	return res;
}

/**
 * Compute the 64-bit range of an inverted absolute value.
 *   @in: The input range.
 *   &returns: The output ragne.
 */
Range64 Range64::InvFltAbs(const Range64 &in) {
	Range64 res;

	for(auto &ival : in.ivals) {
		if((ival.flo > 0.0) || (ival.fhi < -0.0)) {
			res.ivals.push_back(Ival64::Flt(ival.flo, ival.fhi, ival.nan));
			res.ivals.push_back(Ival64::Flt(-ival.fhi, -ival.flo, ival.nan));
		}
		else  {
			double max = fmax(-ival.flo, ival.fhi);

			res.ivals.push_back(Ival64::Flt(-max, max, ival.nan));
		}
	}

	return res;
}


/**
 * Create 64-bit fact with no values.
 *   &returns: The fact.
 */
Range64 Range64::Empty() {
	return Range64();
}

/**
 * Create a 64-bit fact covering all inputs.
 *   &returns: The fact.
 */
Range64 Range64::All() {
	Range64 fact = Range64();
	fact.ivals.push_back(Ival64::All());

	return fact;
}

/**
 * Create a 64-bit fact of a single value.
 *   @val: The value.
 *   &returns: The fact.
 */
Range64 Range64::Const(double val) {
	Range64 fact = Range64::Empty();
	fact.ivals.push_back(Ival64::Flt(val, val, false));

	return fact;
}

/**
 * Create a 64-bit fact of a single integer value.
 *   @val: The value.
 *   &returns: The fact.
 */
Range64 Range64::Int(uint64_t val) {
	Range64 fact = Range64::Empty();
	fact.ivals.push_back(Ival64::Int(val, val));

	return fact;
}


/** Boolean Range Class **/

/**
 * Dump the boolean range to standard out.
 */
void RangeBool::Dump() const {
	if(istrue && isfalse)
		printf("either");
	else if(istrue && !isfalse)
		printf("true");
	else if(!istrue && isfalse)
		printf("false");
	else if(!istrue && !isfalse)
		printf("neither");
}


/**
 * Create an empty boolean range.
 *   &returns: The range.
 */
RangeBool RangeBool::Empty() {
	return RangeBool(false, false);
}

/**
 * Create a constant boolean range.
 *   @val: The constant value.
 *   &returns: The range.
 */
RangeBool RangeBool::Const(bool val) {
	return RangeBool(val, !val);
}


/** Range Class **/

/**
 * Retrieve the lower bound of a range.
 *   &returns: The lower bound.
 */
double Range::Lower() const {
	if(std::holds_alternative<Range64>(var))
		return std::get<Range64>(var).Lower();
	else
		__builtin_unreachable();
}

/**
 * Retrieve the upper bound of a range.
 *   &returns: The upper bound.
 */
double Range::Upper() const {
	if(std::holds_alternative<Range64>(var))
		return std::get<Range64>(var).Upper();
	else
		__builtin_unreachable();
}

/**
 * Bound a range below by a bound.
 *   @bound: The bound.
 *   &returns: The bounded range.
 */
Range Range::Below(double bound) const {
	if(std::holds_alternative<Range64>(var))
		return std::get<Range64>(var).Below(bound);
	else
		__builtin_unreachable();
}

/**
 * Bound a range above by a bound.
 *   @bound: The bound.
 *   &returns: The bounded range.
 */
Range Range::Above(double bound) const {
	if(std::holds_alternative<Range64>(var))
		return std::get<Range64>(var).Above(bound);
	else
		__builtin_unreachable();
}

/**
 * Retrieve a string description of the range.
 *   &returns: The string.
 */
std::string Range::Str() const {
	if(std::holds_alternative<Range64>(var))
		return std::get<Range64>(var).Str();
	else
		__builtin_unreachable();
}

/**
 * Dump an range to stdout.
 */
void Range::Dump() const {
	if(std::holds_alternative<Range64>(var))
		std::get<Range64>(var).Dump();
	else if(std::holds_alternative<RangeBool>(var))
		std::get<RangeBool>(var).Dump();
	else
		__builtin_unreachable();
}


/**
 * Insert an interval into the range.
 *   @ival: The interval.
 *   &returns: True if inserted, false if duplicated.
 */
bool Range::Insert64(Ival64 ival) {
	if(std::holds_alternative<Range64>(var))
		return std::get<Range64>(var).Insert(ival);
	else if(std::holds_alternative<RangeBool>(var))
		fatal("stub");
		//std::get<RangeBool>(var).Insert(ival);
	else
		__builtin_unreachable();
}


/**
 * Compute the next range for a 64-bit floating-point absolute value.
 *   @in: The input range.
 *   &returns: The new range.
 */
Range Range::FltAbs64(const Range &in) {
	if(std::holds_alternative<Range64>(in.var))
		return Range64::FltAbs(std::get<Range64>(in.var));
	else
		fatal("FltAbs64 applied to invalid range.");
}

/**
 * Compute the next range for a 64-bit FP add.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new range.
 */
Range Range::FltAdd64(const Range &lhs, const Range &rhs) {
	if(std::holds_alternative<Range64>(lhs.var) && std::holds_alternative<Range64>(rhs.var))
		return Range64::FltAdd(std::get<Range64>(lhs.var), std::get<Range64>(rhs.var));
	else
		fatal("FltAdd64 applied to invalid range.");
}

/**
 * Compute the next range for a 64-bit floating-point copy sign.
 *   @mag: The magnitude.
 *   @sign: The sign.
 *   &returns: The new range.
 */
Range Range::FltCopySign64(const Range &mag, const Range &sign) {
	if(std::holds_alternative<Range64>(mag.var) && std::holds_alternative<Range64>(sign.var))
		return Range64::FltCopySign(std::get<Range64>(mag.var), std::get<Range64>(sign.var));
	else
		fatal("FltCopySign64 applied to invalid range.");
}

/**
 * Compute the AND of two 64-bit ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new range.
 */
Range Range::IntAnd64(const Range &lhs, const Range &rhs) {
	if(std::holds_alternative<Range64>(lhs.var) && std::holds_alternative<Range64>(rhs.var))
		return Range64::IntAnd(std::get<Range64>(lhs.var), std::get<Range64>(rhs.var));
	else
		fatal("IntAnd applied to invalid range.");
}

/**
 * Compute the xor of two 64-bit ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new range.
 */
Range Range::Xor64(const Range &lhs, const Range &rhs) {
	if(std::holds_alternative<Range64>(lhs.var) && std::holds_alternative<Range64>(rhs.var))
		return Range64::IntXor(std::get<Range64>(lhs.var), std::get<Range64>(rhs.var));
	else
		fatal("Xor applied to invalid range.");
}


/**
 * Compute the range of an inverted absolute value.
 *   @in: The input range.
 *   &returns: The output ragne.
 */
Range Range::InvFltAbs64(const Range &in) {
	if(std::holds_alternative<Range64>(in.var))
		return Range64::InvFltAbs(std::get<Range64>(in.var));
	else
		fatal("FltAbs64 applied to invalid range.");
}


Range64 FltRelComp(const Range64 &lhs, const Range64 &rhs) {
	return lhs;
}

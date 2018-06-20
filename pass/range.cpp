#include "inc.hpp"


/** Range64 Class **/

/**
 * Retrieve the lower bound of a 64-bit range.
 *   &returns: The lower bound.
 */
double Range64::Lower() const {
	double lower = DBL_MAX;

	for(auto ival = ivals.begin(); ival != ivals.end(); ival++)
		lower = fmin(lower, ival->flo);

	return lower;
}

/**
 * Retrieve the upper bound of a 64-bit range.
 *   &returns: The upper bound.
 */
double Range64::Upper() const {
	double upper = -DBL_MAX;

	for(auto ival = ivals.begin(); ival != ivals.end(); ival++)
		upper = fmax(upper, ival->fhi);

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
				printf("\n");

			ival.Dump();
		}
	}
	else
		printf("∅");
}


/**
 * Compute the next 64-bit fact for a floating-point absolute value.
 *   @in: The input fact.
 *   &returns: The new fact.
 */
Range64 Range64::FltAbs(Range64 in) {
	for(auto &ival : in.ivals)
		ival = Ival64::FltAbs(ival);

	return in;
}

/**
 * Compute the 64-bit range for a ordered less-than.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The range.
 */
Range64 Range64::FltOLT(const Range64 &lhs, const Range64 &rhs) {
	return lhs;
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
	else
		__builtin_unreachable();
}


/**
 * Compute the next range for a 64-bit floating-point absolute value.
 *   @in: The input range.
 *   &returns: The new range.
 */
Range Range::FltAbs64(Range in) {
	if(std::holds_alternative<Range64>(in.var))
		return Range64::FltAbs(std::get<Range64>(in.var));
	else
		fatal("FltAbs64 applied to invalid range.");
}


/**
 * Compute the range for a ordered less-than.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The range.
 */
Range Range::FltOLT64(const Range &lhs, const Range &rhs) {
	if(std::holds_alternative<Range64>(lhs.var) && std::holds_alternative<Range64>(rhs.var))
		return lhs;
	else
		fatal("FltOLT64 applied to invalid range.");
}

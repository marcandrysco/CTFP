#include "inc.hpp"

/**
 * Check if a value is undefined.
 *   @in: The input range.
 *   &returns: True if undefined.
 */
bool IsUndef1(const Range &in) {
	return std::holds_alternative<RangeUndef>(in.var);
}

/**
 * Check if either side is undefined.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: True if undefined.
 */
bool IsUndef2(const Range &lhs, const Range &rhs) {
	return std::holds_alternative<RangeUndef>(lhs.var) || std::holds_alternative<RangeUndef>(rhs.var);
}

template<class T> bool IsA(const Range &in) {
	return std::holds_alternative<T>(in.var);
}

template<class T> bool IsPair(const Range &lhs, const Range &rhs) {
	return std::holds_alternative<T>(lhs.var) && std::holds_alternative<T>(rhs.var);
}


/**
 * Check if a value is a 64-bit float.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: True if a 64-bit float.
 */
bool IsF64(const Range &in) {
	return std::holds_alternative<RangeVecF64>(in.var);
}

/**
 * Check if a pair are 64-bit floats.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: True if 64-bit floats.
 */
bool IsF64Pair(Range const &lhs, Range const &rhs) {
	return IsF64(lhs) && IsF64(rhs);
}


/** RangeBool class **/

/**
 * Convert a range to a string.
 *   &returns: The string.
 */
std::string RangeBool::Str() const {
	if(istrue && isfalse)
		return "true|false";
	else if(istrue)
		return "true";
	else if(isfalse)
		return "false";
	else
		return "∅";
}


/** RangeVecBool class **/

/**
 * Convert a range to a string.
 *   &returns: The string.
 */
std::string RangeVecBool::Str() const {
	if(scalars.size() == 1)
		return scalars[0].Str();

	std::string ret;

	for(const auto &scalar : scalars)
		ret += ((ret.size() > 0) ? ", " : "") + scalar.Str();

	return std::string("<" + ret + ">");
}


/** Range class **/

/**
 * Range constructor using a type.
 *   @type: The type.
 *   &construct: The range.
 */
Range::Range(Type type) {
	if((type.kind == Kind::Flt) && (type.width == 64))
		var = RangeVecF64::All(type.count);
	else
		var = RangeUndef();
}


/**
 * Check if a range contains subnormal numbers.
 *   @val: The value.
 *   &returns: True the value is in the interval.
 */
bool Range::HasSubnorm() const {
	if(std::holds_alternative<RangeVecF64>(var))
		return std::get<RangeVecF64>(var).HasSubnorm();
	else if(std::holds_alternative<RangeUndef>(var))
		return true;
	else
		return false;
}


/**
 * Convert a range to a string.
 *   &returns: The string.
 */
std::string Range::Str() const {
	if(std::holds_alternative<RangeUndef>(var))
		return "undef";
	else if(std::holds_alternative<RangeVecBool>(var))
		return std::get<RangeVecBool>(var).Str();
	else if(std::holds_alternative<RangeVecI64>(var))
		return std::get<RangeVecI64>(var).Str();
	else if(std::holds_alternative<RangeVecF64>(var))
		return std::get<RangeVecF64>(var).Str();
	else
		fatal("Invalid range type.");
}

/**
 * Cast an integer to float.
 *   @in: The input.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::ItoF(const Range &in, Type type) {
	if(IsUndef1(in))
		return Range(type);
	
	if(std::holds_alternative<RangeVecF64>(in.var))
		return Range(std::get<RangeVecF64>(in.var));
	else if(std::holds_alternative<RangeVecI64>(in.var))
		return Range(RangeVecF64::FromI64(std::get<RangeVecI64>(in.var)));
	else
		fatal("Invalid cast.");
}

/**
 * Cast a float to integer.
 *   @in: The input.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::FtoI(const Range &in, Type type) {
	if(IsUndef1(in))
		return Range(type);
	
	if(std::holds_alternative<RangeVecI64>(in.var))
		return Range(std::get<RangeVecI64>(in.var));
	else if(std::holds_alternative<RangeVecF64>(in.var))
		return Range(RangeVecI64::FromF64(std::get<RangeVecF64>(in.var)));
	else
		fatal("Invalid cast.");
}

/**
 * Add two ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Add(const Range &lhs, const Range &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(type);

	if(std::holds_alternative<RangeVecI64>(lhs.var) && std::holds_alternative<RangeVecI64>(rhs.var))
		fatal("stub"); // return RangeVecI64::Add(std::get<RangeVecI64>(lhs), std::get<RangeVecI64>(rhs));
	else if(std::holds_alternative<RangeVecF64>(lhs.var) && std::holds_alternative<RangeVecF64>(rhs.var))
		return RangeVecF64::Add(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
	else
		fatal("Invalid addition.");
}

/**
 * Subtract two ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Sub(const Range &lhs, const Range &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(type);

	if(std::holds_alternative<RangeVecI64>(lhs.var) && std::holds_alternative<RangeVecI64>(rhs.var))
		fatal("stub"); // return RangeVecI64::Sub(std::get<RangeVecI64>(lhs), std::get<RangeVecI64>(rhs));
	else if(std::holds_alternative<RangeVecF64>(lhs.var) && std::holds_alternative<RangeVecF64>(rhs.var))
		return RangeVecF64::Sub(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
	else
		fatal("Invalid subtraction.");
}

/**
 * Multiply two ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Mul(const Range &lhs, const Range &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(type);

	if(std::holds_alternative<RangeVecI64>(lhs.var) && std::holds_alternative<RangeVecI64>(rhs.var))
		fatal("stub"); // return RangeVecI64::Mul(std::get<RangeVecI64>(lhs), std::get<RangeVecI64>(rhs));
	else if(std::holds_alternative<RangeVecF64>(lhs.var) && std::holds_alternative<RangeVecF64>(rhs.var))
		return RangeVecF64::Mul(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var));
	else
		fatal("Invalid.");
}


/**
 * And two ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::And(const Range &lhs, const Range &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(type);

	if(IsPair<RangeVecI64>(lhs, rhs))
		return RangeVecI64::And(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
	else
		fatal("Invalid and. %ld %ld", lhs.var.index(), rhs.var.index());
}

/**
 * Or two ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Or(const Range &lhs, const Range &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(type);

	if(IsPair<RangeVecI64>(lhs, rhs))
		return RangeVecI64::Or(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
	else
		fatal("Invalid or.");
}

/**
 * Xor two ranges together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Xor(const Range &lhs, const Range &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(type);

	if(IsPair<RangeVecI64>(lhs, rhs))
		return RangeVecI64::Xor(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
	else
		fatal("Invalid xor.");
}


/**
 * Comparison (OGT) on two ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::CmpOGT(Range const &lhs, Range const &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(RangeUndef());

	if(IsF64Pair(lhs, rhs))
		return Range(RangeVecF64::CmpOGT(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
	else
		fatal("Invalid comparison (OGT).");
}


/**
 * Select values base on a condition.
 *   @cond: The condition.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Select(Range const& cond, Range const& lhs, Range const& rhs, Type type) {
	if(IsUndef1(cond))
		return Range(type);

	if(!IsA<RangeVecBool>(cond)) {
		fatal("Invalid select. %zd", cond.var.index());
	}

	if(IsPair<RangeVecF64>(lhs, rhs))
		return Range(RangeVecF64::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
	else if(IsPair<RangeVecI64>(lhs, rhs))
		return Range(RangeVecI64::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var)));
	else if(IsPair<RangeVecBool>(lhs, rhs))
		return Range(type);
	else
		fatal("Invalid select. 2");
}

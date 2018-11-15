#include "inc.hpp"


/**
 * Check if either side is undefined.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: True if undefined.
 */
bool IsUndef2(const Range &lhs, const Range &rhs) {
	return (std::holds_alternative<RangeUndef>(lhs.var)) || (std::holds_alternative<RangeUndef>(rhs.var));
}


/** Range Class **/

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
	else if(std::holds_alternative<RangeVecI64>(var))
		fatal("stub");
	else if(std::holds_alternative<RangeVecF64>(var))
		return std::get<RangeVecF64>(var).Str();
	else
		fatal("Invalid range type.");
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
		fatal("Invalid subtraction.");
}

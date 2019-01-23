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


/**
 * Check if a range is a given type.
 *   @in: The input range.
 *   &returns: True if is the given class.
 */
template<class T> bool IsA(const Range &in) {
	return std::holds_alternative<T>(in.var);
}

/**
 * Check if a pair of ranges are  given type.
 *   @lhs: The left-hand range.
 *   @rhs: The right-hand range.
 *   &returns: True if is the given class.
 */
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


/**
 * Check if every elements of the range must be true.
 *   &returns: True if must be true.
 */
bool RangeVecBool::IsTrue() const {
	bool f = true;

	for(uint32_t i = 0; i < scalars.size(); i++) 
		f &= scalars[i].IsTrue();

	return f;
}

/**
 * Check if every elements of the range must be false.
 *   &returns: True if must be false.
 */
bool RangeVecBool::IsFalse() const {
	bool f = true;

	for(uint32_t i = 0; i < scalars.size(); i++) 
		f &= scalars[i].IsFalse();

	return f;
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
	if(IsA<RangeUndef>(*this))
		return "undef";
	else if(IsA<RangeVecBool>(*this))
		return std::get<RangeVecBool>(var).Str();
	else if(IsA<RangeVecI32>(*this))
		return std::get<RangeVecI32>(var).Str();
	else if(IsA<RangeVecI64>(*this))
		return std::get<RangeVecI64>(var).Str();
	else if(IsA<RangeVecF32>(*this))
		return std::get<RangeVecF32>(var).Str();
	else if(IsA<RangeVecF64>(*this))
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
	else if(IsA<RangeVecF32>(in))
		return Range(std::get<RangeVecF32>(in.var));
	else if(IsA<RangeVecF64>(in))
		return Range(std::get<RangeVecF64>(in.var));
	else if(IsA<RangeVecI32>(in))
		return Range(RangeVecF32::FromInt<uint32_t>(std::get<RangeVecI32>(in.var)));
	else if(IsA<RangeVecI64>(in))
		return Range(RangeVecF64::FromInt<uint64_t>(std::get<RangeVecI64>(in.var)));
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
	else if(IsA<RangeVecI32>(in))
		return Range(std::get<RangeVecI32>(in.var));
	else if(IsA<RangeVecI64>(in))
		return Range(std::get<RangeVecI64>(in.var));
	else if(IsA<RangeVecF32>(in))
		return Range(RangeVecI32::FromFlt<float>(std::get<RangeVecF32>(in.var)));
	else if(IsA<RangeVecF64>(in))
		return Range(RangeVecI64::FromFlt<double>(std::get<RangeVecF64>(in.var)));
	else
		fatal("Invalid cast.");
}

/**
 * Absolute value of a range.
 *   @in: The input range.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::Abs(Range const& in, Type type) {
	if(IsUndef1(in))
		return Range(type);
	else if(IsA<RangeVecF32>(in))
		return Range(RangeVecF32::Abs(std::get<RangeVecF32>(in.var)));
	else if(IsA<RangeVecF64>(in))
		return Range(RangeVecF64::Abs(std::get<RangeVecF64>(in.var)));
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
	else if(IsPair<RangeVecF32>(lhs, rhs))
		return RangeVecF32::Add(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
	else if(IsPair<RangeVecF64>(lhs, rhs))
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
	else if(IsPair<RangeVecF32>(lhs, rhs))
		return RangeVecF32::Sub(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
	else if(IsPair<RangeVecF64>(lhs, rhs))
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
	else if(IsPair<RangeVecF32>(lhs, rhs))
		return RangeVecF32::Mul(std::get<RangeVecF32>(lhs.var), std::get<RangeVecF32>(rhs.var));
	else if(IsPair<RangeVecF64>(lhs, rhs))
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
	else if(IsPair<RangeVecBool>(lhs, rhs))
		return RangeVecBool::And(std::get<RangeVecBool>(lhs.var), std::get<RangeVecBool>(rhs.var));
	else if(IsPair<RangeVecI32>(lhs, rhs))
		return RangeVecI32::And(std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var));
	else if(IsPair<RangeVecI64>(lhs, rhs))
		return RangeVecI64::And(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
	else
		fatal("Invalid and. (%ld %ld)", lhs.var.index(), rhs.var.index());
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
	else if(IsPair<RangeVecBool>(lhs, rhs))
		return RangeVecBool::Or(std::get<RangeVecBool>(lhs.var), std::get<RangeVecBool>(rhs.var));
	else if(IsPair<RangeVecI32>(lhs, rhs))
		return RangeVecI32::Or(std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var));
	else if(IsPair<RangeVecI64>(lhs, rhs))
		return RangeVecI64::Or(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
	else
		fatal("Invalid or. (%ld %ld)", lhs.var.index(), rhs.var.index());
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
	else if(IsPair<RangeVecBool>(lhs, rhs))
		return RangeVecBool::Xor(std::get<RangeVecBool>(lhs.var), std::get<RangeVecBool>(rhs.var));
	else if(IsPair<RangeVecI32>(lhs, rhs))
		return RangeVecI32::Xor(std::get<RangeVecI32>(lhs.var), std::get<RangeVecI32>(rhs.var));
	else if(IsPair<RangeVecI64>(lhs, rhs))
		return RangeVecI64::Xor(std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var));
	else
		fatal("Invalid xor. (%ld %ld)", lhs.var.index(), rhs.var.index());
}


/**
 * Comparison (OLT) on two ranges.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result range.
 */
Range Range::CmpOLT(Range const &lhs, Range const &rhs, Type type) {
	if(IsUndef2(lhs, rhs))
		return Range(RangeUndef());

	if(IsF64Pair(lhs, rhs))
		return Range(RangeVecF64::CmpOLT(std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
	else
		fatal("Invalid comparison (OLT).");
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
	else if(IsUndef2(lhs, rhs))
		return Range(RangeUndef());

	if(!IsA<RangeVecBool>(cond))
		fatal("Invalid select (%zd).", cond.var.index());

	if(IsPair<RangeVecF64>(lhs, rhs))
		return Range(RangeVecF64::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecF64>(lhs.var), std::get<RangeVecF64>(rhs.var)));
	else if(IsPair<RangeVecI64>(lhs, rhs))
		return Range(RangeVecI64::Select(std::get<RangeVecBool>(cond.var), std::get<RangeVecI64>(lhs.var), std::get<RangeVecI64>(rhs.var)));
	else if(IsPair<RangeVecBool>(lhs, rhs))
		return Range(type);
	else
		fatal("Invalid select (%zd, %zd).", lhs.var.index(), rhs.var.index());
}

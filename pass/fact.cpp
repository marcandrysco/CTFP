#include "inc.hpp"


/** Fact class **/

/**
 * Propagate facts backwards.
 */
void Fact::InvProp() {
	switch(op) {
	case Op::ConstI64:
	case Op::ConstF64:
		break;

	case Op::AbsF64:
		args[0]->vars = vars;
		args[0]->ranges.clear();

		for(auto &range : ranges) {
			if(std::holds_alternative<RangeF64>(range.var))
				args[0]->ranges.push_back(RangeF64::AbsInv(std::get<RangeF64>(range.var)));
			else
				fatal("AbsF64 must be applied to RangeF64.");
		}

		break;

	default:
		fatal("stub %d", op);
	}
}

/**
 * Retrieve the lower 64-bit float value.
 *   &returns: The lower value.
 */
double Fact::LowerF64() const {
	double min = DBL_MAX;

	for(auto const &range : ranges)
		min = fmin(min, range.LowerF64());

	return min;
}

/**
 * Retrieve the upper 64-bit float value.
 *   &returns: The lower value.
 */
double Fact::UpperF64() const {
	double max = -DBL_MAX;

	for(auto const &range : ranges)
		max = fmax(max, range.UpperF64());

	return max;
}


/**
 * Retrieve the variable index limit.
 *   &returns: The limit.
 */
uint64_t Fact::Limit() const
{
	return 1 << vars.size();
}

/**
 * Retrieve the index of a variable.
 *   @var: The variable.
 *   &returns: The index, or negative zero if not found.
 */
int32_t Fact::Index(const llvm::Value *var) const {
	for(uint32_t i = 0; i < vars.size(); i++) {
		if(vars[i] == var)
			return i;
	}

	return -1;
}

/**
 * Given a set of variables an index, retrieve the range it maps to.
 *   @vars: The variable array.
 *   @idx: The index.
 *   &returns: The range.
 */
Range &Fact::Map(const std::vector<const llvm::Value *> &vars, uint64_t idx) {
	uint64_t out = 0;

	for(uint32_t i = 0; i < vars.size(); i++) {
		int32_t k = Index(vars[i]);
		if((k >= 0) && ((idx & (1 << i)) != 0))
			out |= 1 << k;
	}

	assert(out < ranges.size());

	return ranges[out];
}


/**
 * Retrieve the string for the fact.
 *   &returns: The string.
 */
std::string Fact::Str() const {
	if(ranges.size() > 1) {
		std::string str = "";

		unsigned int i = 0;
		for(auto const &iter : ranges) {
			str += "    ";

			unsigned int k = 0;
			for(auto var : vars) 
				str += llvm_name(var) + std::string(((1 << k++) & i) ? "✔" : "✘");

			i++;
			str += " " + iter.Str() + "\n";
		}

		return str;
	}
	else
		return "    " + ranges.front().Str() + "\n";
}

/**
 * Dump the fact to standard out.
 */
void Fact::Dump() const {
	printf("%s", Str().data());
}


/**
 * Compute a 64-bit float absolute value.
 *   @in: The input fact.
 *   @out: The output fact.
 */
Fact Fact::AbsF64(Fact &in) {
	Fact res(Op::AbsF64, std::vector<Fact *>{ &in }, in.vars);

	for(auto const &range : in.ranges) {
		if(std::holds_alternative<RangeF64>(range.var))
			res.ranges.push_back(RangeF64::Abs(std::get<RangeF64>(range.var)));
		else
			fatal("AbsF64 must be applied to RangeF64.");
	}

	return res;
}

/**
 * Compute a 64-bit float addition.
 *   @lhs: The left-hand side.
 *   @nhs: The right-hand side.
 *   @var: The variable.
 *   &returns: The result fact.
 */
Fact Fact::AddF64(Fact &lhs, Fact &rhs, const llvm::Value *var) {
	Fact res(Op::AddF64, std::vector<Fact *>{ &lhs, &rhs, }, Fact::Cross(lhs.vars, rhs.vars));

	for(uint64_t i = 0; i < res.Limit(); i++) {
		Range &x = lhs.Map(res.vars, i);
		Range &y = rhs.Map(res.vars, i);

		if(!std::holds_alternative<RangeF64>(x.var) || !std::holds_alternative<RangeF64>(y.var))
			fatal("AddF64 must be applied to RangeF64.");

		res.ranges.push_back(RangeF64::Add(std::get<RangeF64>(x.var), std::get<RangeF64>(y.var)));
	}

	return res;
}

/**
 * Compute a 64-bit float subtraction.
 *   @lhs: The left-hand side.
 *   @nhs: The right-hand side.
 *   @var: The variable.
 *   &returns: The result fact.
 */
Fact Fact::SubF64(Fact &lhs, Fact &rhs, const llvm::Value *var) {
	Fact res(Op::SubF64, std::vector<Fact *>{ &lhs, &rhs, }, Fact::Cross(lhs.vars, rhs.vars));

	for(uint64_t i = 0; i < res.Limit(); i++) {
		Range &x = lhs.Map(res.vars, i);
		Range &y = rhs.Map(res.vars, i);

		if(!std::holds_alternative<RangeF64>(x.var) || !std::holds_alternative<RangeF64>(y.var))
			fatal("SubF64 must be applied to RangeF64.");

		res.ranges.push_back(RangeF64::Sub(std::get<RangeF64>(x.var), std::get<RangeF64>(y.var)));
	}

	return res;
}

/**
 * Compute a 64-bit float addition
 *   @lhs: The left-hand side.
 *   @nhs: The right-hand side.
 *   @var: The variable.
 *   &returns: The result fact.
 */
Fact Fact::MulF64(Fact &lhs, Fact &rhs, const llvm::Value *var) {
	Fact res(Op::MulF64, std::vector<Fact *>{ &lhs, &rhs, }, Fact::Cross(lhs.vars, rhs.vars));

	for(uint64_t i = 0; i < res.Limit(); i++) {
		Range &x = lhs.Map(res.vars, i);
		Range &y = rhs.Map(res.vars, i);

		if(!std::holds_alternative<RangeF64>(x.var) || !std::holds_alternative<RangeF64>(y.var))
			fatal("MulF64 must be applied to RangeF64.");

		res.ranges.push_back(RangeF64::Mul(std::get<RangeF64>(x.var), std::get<RangeF64>(y.var)));
	}

	return res;
}

/**
 * Compute a 64-bit float ordered greater than.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @var: The variable.
 *   &returns: The fact.
 */
Fact Fact::CmpOltF64(Fact &lhs, Fact &rhs, const llvm::Value *var) {
	Fact res(Op::CmpOltF64, std::vector<Fact *>{ &lhs, &rhs }, var);

	res.ranges.push_back(Range(RangeBool::Const(false)));
	res.ranges.push_back(Range(RangeBool::Const(true)));

	unsigned int len;
	double rlo = rhs.LowerF64(), rhi = rhs.UpperF64();
	double llo = lhs.LowerF64(), lhi = lhs.UpperF64();

	lhs.vars.push_back(var);
	len = lhs.ranges.size();
	for(unsigned int i = 0; i < len; i++) {
		lhs.ranges.push_back(lhs.ranges[i].BelowF64(rhi, false));
		lhs.ranges[i] = lhs.ranges[i].AboveF64(Fact::Next64(rlo), true);
	}
	lhs.InvProp();

	rhs.vars.push_back(var);
	len = rhs.ranges.size();
	for(unsigned int i = 0; i < len; i++) {
		rhs.ranges.push_back(rhs.ranges[i].AboveF64(Fact::Prev64(llo), true));
		rhs.ranges[i] = rhs.ranges[i].BelowF64(lhi, false);
	}
	rhs.InvProp();

	return res;
}

/**
 * Compute a 64-bit float ordered less than.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @var: The variable.
 *   &returns: The fact.
 */
Fact Fact::CmpOgtF64(Fact &lhs, Fact &rhs, const llvm::Value *var) {
	Fact res(Op::CmpOltF64, std::vector<Fact *>{ &lhs, &rhs }, var);

	res.ranges.push_back(Range(RangeBool::Const(false)));
	res.ranges.push_back(Range(RangeBool::Const(true)));

	unsigned int len;
	double rlo = rhs.LowerF64(), rhi = rhs.UpperF64();
	double llo = lhs.LowerF64(), lhi = lhs.UpperF64();

	lhs.vars.push_back(var);
	len = lhs.ranges.size();
	for(unsigned int i = 0; i < len; i++) {
		lhs.ranges.push_back(lhs.ranges[i].AboveF64(rhi, false));
		lhs.ranges[i] = lhs.ranges[i].BelowF64(Fact::Prev64(rlo), true);
	}
	lhs.InvProp();

	rhs.vars.push_back(var);
	len = rhs.ranges.size();
	for(unsigned int i = 0; i < len; i++) {
		rhs.ranges.push_back(rhs.ranges[i].BelowF64(Fact::Next64(llo), true));
		rhs.ranges[i] = rhs.ranges[i].AboveF64(lhi, false);
	}
	rhs.InvProp();

	return res;
}

/**
 * Computer a 64-bit copysign call.
 *   @msg: The magnitude fact.
 *   @sign: The sign fact.
 *   &returns: The result fact.
 */
Fact Fact::CopySignF64(Fact &mag, Fact &sign)
{
	Fact res(Op::CopySignF64, std::vector<Fact *>{ &mag, &sign }, Fact::Cross(mag.vars, sign.vars));

	for(uint64_t i = 0; i < res.Limit(); i++) {
		Range &x = mag.Map(res.vars, i);
		Range &y = sign.Map(res.vars, i);

		if(!std::holds_alternative<RangeF64>(x.var) || !std::holds_alternative<RangeF64>(y.var))
			fatal("CopySignF64 must be applied to RangeF64.");

		res.ranges.push_back(RangeF64::CopySign(std::get<RangeF64>(x.var), std::get<RangeF64>(y.var)));
	}

	return res;
}

/**
 * Compute a 64-bit integer AND.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The fact.
 */
Fact Fact::AndI64(Fact &lhs, Fact &rhs) {
	Fact res(Op::AndI64, std::vector<Fact *>{ &lhs, &rhs }, Fact::Cross(lhs.vars, rhs.vars));

	for(uint64_t i = 0; i < res.Limit(); i++) {
		Range &x = lhs.Map(res.vars, i);
		Range &y = rhs.Map(res.vars, i);

		if(!std::holds_alternative<RangeI64>(x.var) || !std::holds_alternative<RangeI64>(y.var))
			fatal("AndI64 must be applied to RangeI64.");

		res.ranges.push_back(RangeI64::And(std::get<RangeI64>(x.var), std::get<RangeI64>(y.var)));
	}

	return res;
}

/**
 * Compute a 64-bit integer XOR.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The fact.
 */
Fact Fact::XorI64(Fact &lhs, Fact &rhs) {
	Fact res(Op::XorI64, std::vector<Fact *>{ &lhs, &rhs });

	res.vars = Fact::Cross(lhs.vars, rhs.vars);

	for(uint64_t i = 0; i < res.Limit(); i++) {
		Range &x = lhs.Map(res.vars, i);
		Range &y = rhs.Map(res.vars, i);

		if(!std::holds_alternative<RangeI64>(x.var) || !std::holds_alternative<RangeI64>(y.var))
			fatal("XorI64 must be applied to RangeI64.");

		res.ranges.push_back(RangeI64::Xor(std::get<RangeI64>(x.var), std::get<RangeI64>(y.var)));
	}

	return res;
}

/**
 * Compute a 64-bit float select.
 *   @cond: The conditional fact.
 *   @ontrue: The on true fact.
 *   @onfalse: The on false fact.
 *   &returns: The selected fact.
 */
Fact Fact::SelectI64(Fact &cond, Fact &ontrue, Fact &onfalse) {
	Fact res(Op::SelectI64, std::vector<Fact *>{ &cond });
	res.vars = cond.vars;

	for(auto const &range : cond.ranges) {
		if(!std::holds_alternative<RangeBool>(range.var))
			fatal("SelectI64 must be applied to RangeBool.");

		RangeBool const &get = std::get<RangeBool>(range.var);

		if(get.istrue) {
			for(auto const &iter : ontrue.ranges)
				res.ranges.push_back(iter);
		}
		
		if(get.isfalse) {
			for(auto const &iter : onfalse.ranges)
				res.ranges.push_back(iter);
		}
	}

	return res;
}

/**
 * Compute a 64-bit cast float to integer.
 *   @in: The input fact.
 *   &returns: The output fact.
 */
Fact Fact::CastF64toI64(Fact &in) {
	Fact res(Op::CastF64toI64, std::vector<Fact *>{ &in }, in.vars);

	for(auto const &range : in.ranges) {
		if(!std::holds_alternative<RangeF64>(range.var))
			fatal("CastF64toI64 must be applied to RangeF64.");

		res.ranges.push_back(RangeI64::CastF64(std::get<RangeF64>(range.var)));
	}

	return res;
}

/**
 * Compute a 64-bit cast integer to float.
 *   @in: The input fact.
 *   &returns: The output fact.
 */
Fact Fact::CastI64toF64(Fact &in) {
	Fact res(Op::CastI64toF64, std::vector<Fact *>{ &in }, in.vars);

	for(auto const &range : in.ranges) {
		if(!std::holds_alternative<RangeI64>(range.var))
			fatal("CastI64toF64 must be applied to RangeI64.");

		res.ranges.push_back(RangeF64::FromI64(std::get<RangeI64>(range.var)));
	}

	return res;
}


/**
 * Compute the cross-product of variables.
 *   @lhs: The left vector.
 *   @rhs: The right vector.
 *   &returns: The summed vector.
 */
std::vector<const llvm::Value *> Fact::Cross(std::vector<const llvm::Value *> const &lhs, std::vector<const llvm::Value *> const &rhs) {
	std::vector<const llvm::Value *> res(lhs);

	for(auto const &var : rhs) {
		if(std::find(lhs.begin(), lhs.end(), var) == lhs.end())
			res.push_back(var);
	}

	return res;
}

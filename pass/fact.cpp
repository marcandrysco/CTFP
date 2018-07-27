#include "inc.hpp"


/**
 * Compute the sum of variables.
 *   @lhs: The left vector.
 *   @rhs: The right vector.
 *   &returns: The summed vector.
 */
std::vector<llvm::Value *> vars_sum(const std::vector<llvm::Value *> &lhs, const std::vector<llvm::Value *> &rhs) {
	std::vector<llvm::Value *> res(lhs);

	for(auto const &var : rhs) {
		if(std::find(lhs.begin(), lhs.end(), var) == lhs.end())
			res.push_back(var);
	}

	return res;
}


/** Fact Class **/

/**
 * Compute the lower bound of a fact.
 *   &returns: The lower bound.
 */
double Fact::Lower() const {
	double min = INFINITY;

	for(auto const &range : ranges)
		min = fmin(min, range.Lower());

	return min;
}

/**
 * Compute the upper bound of a fact.
 *   &returns: The upper bound.
 */
double Fact::Upper() const {
	double max = -INFINITY;

	for(auto const &range : ranges)
		max = fmax(max, range.Upper());

	return max;
}

/**
 * Retrieve a string description of the fact.
 *   &returns: The string.
 */
std::string Fact::Str() const {
	std::string ret;

	for(auto const &iter : ranges)
		ret += "    " + iter.Str() + "\n";

	return ret;
}

/**
 * Dump a fact to stdout.
 */
void Fact::Dump() const {
	if(ranges.size() == 1) {
		printf("    ");
		ranges.front().Dump();
		printf("\n");
	}
	else {
		unsigned int i = 0;
		for(auto const &iter : ranges) {
			printf("    ");

			unsigned int k = 0;
			for(auto var : vars) 
				printf("%s%s ", llvm_name(var).c_str(), ((1 << k++) & i) ? "✔" : "✘");

			iter.Dump();
			printf("\n");

			i++;
		}
	}
}


/**
 * Propagate facts backwards.
 */
void Fact::InvProp() {
	switch(op) {
	case Fact::FConst:
	case Fact::IConst:
		break;

	case Fact::FAbs64:
		args[0]->vars = vars;
		args[0]->ranges.clear();

		for(auto &range : ranges)
			args[0]->ranges.push_back(Range::InvFltAbs64(range));

		break;

	default:
		fatal("stub %d", op);
	}
}

/**
 * Compute the next fact for a 64-bit floating-point addition.
 *   @lhs: The left-hand side.
 *   &returns: The new fact.
 */
Fact Fact::FltAdd64(Fact &lhs, Fact &rhs) {
	Fact res(FAdd64);

	res.vars = Fact::Cross(lhs.vars, rhs.vars);
	for(uint64_t i = 0; i < res.Limit(); i++) {
		res.ranges.push_back(Range::FltAdd64(
			lhs.Map(res.vars, i),
			rhs.Map(res.vars, i)
		));
	}

	return res;
}

/**
 * Compute the next fact for a 64-bit floating-point absolute value.
 *   @in: The input fact.
 *   &returns: The new fact.
 */
Fact Fact::FltAbs64(Fact &in) {
	Fact out(FAbs64);
	out.args.push_back(&in);

	for(auto &iter : in.ranges)
		out.ranges.push_back(Range::FltAbs64(iter));

	return out;
}

/**
 * Compute the next fact for a 64-bit copysign call.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new fact.
 */
Fact Fact::FltCopySign64(Fact &lhs, Fact &rhs) {
	Fact res(CopySign64);

	res.vars = Fact::Cross(lhs.vars, rhs.vars);
	for(uint64_t i = 0; i < res.Limit(); i++) {
		res.ranges.push_back(Range::FltCopySign64(
			lhs.Map(res.vars, i),
			rhs.Map(res.vars, i)
		));
	}

	return res;
}

/**
 * Compute the next fact for a 64-bit AND.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new fact.
 */
Fact Fact::IntAnd64(Fact &lhs, Fact &rhs) {
	Fact res(IAnd64);

	res.vars = Fact::Cross(lhs.vars, rhs.vars);
	for(uint64_t i = 0; i < res.Limit(); i++) {
		res.ranges.push_back(Range::IntAnd64(
			lhs.Map(res.vars, i),
			rhs.Map(res.vars, i)
		));
	}

	return res;
}

/**
 * Compute the next fact for a 64-bit xor.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   &returns: The new fact.
 */
Fact Fact::IntXor64(Fact &lhs, Fact &rhs) {
	Fact res(IXor64);

	res.vars = Fact::Cross(lhs.vars, rhs.vars);
	for(uint64_t i = 0; i < res.Limit(); i++) {
		res.ranges.push_back(Range::Xor64(
			lhs.Map(res.vars, i),
			rhs.Map(res.vars, i)
		));
	}

	return res;
}

/**
 * Compute a ordered-less-than 64-bit floating-point comparison.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @var: The variable.
 *   &returns: The fact.
 */
Fact Fact::FltOLT64(Fact &lhs, Fact &rhs, llvm::Value *var) {
	Fact res;
	unsigned int len;
	double rlo = rhs.Lower(), rhi = rhs.Upper();
	double llo = lhs.Lower(), lhi = lhs.Upper();

	lhs.vars.push_back(var);
	len = lhs.ranges.size();
	for(unsigned int i = 0; i < len; i++) {
		lhs.ranges.push_back(lhs.ranges[i].Below(rhi));
		lhs.ranges[i] = lhs.ranges[i].Above(Fact::Next64(rlo));
	}
	lhs.InvProp();

	rhs.vars.push_back(var);
	len = rhs.ranges.size();
	for(unsigned int i = 0; i < len; i++) {
		rhs.ranges.push_back(rhs.ranges[i].Above(Fact::Prev64(llo)));
		rhs.ranges[i] = rhs.ranges[i].Below(lhi);
	}
	rhs.InvProp();

	res.vars.push_back(var);
	res.ranges.push_back(RangeBool::Const(false));
	res.ranges.push_back(RangeBool::Const(true));

	return res;
}

Fact Fact::Select(Fact &cond, Fact &lhs, Fact &rhs, llvm::Value *var) {
	Fact res(Sel);
	res.vars = cond.vars;

	for(auto const &range : cond.ranges) {
		if(!std::holds_alternative<RangeBool>(range.var))
			fatal("Cannot select on a non-bool range.");

		RangeBool const &get = std::get<RangeBool>(range.var);

		if(get.istrue) {
			for(auto const &iter : lhs.ranges)
				res.ranges.push_back(iter);
		}
		
		if(get.isfalse) {
			for(auto const &iter : rhs.ranges)
				res.ranges.push_back(iter);
		}
	}

	return res;
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
Range &Fact::Map(const std::vector<llvm::Value *> &vars, uint64_t idx) {
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
 * Compute the cross-product of variables.
 *   @lhs: The left vector.
 *   @rhs: The right vector.
 *   &returns: The summed vector.
 */
std::vector<llvm::Value *> Fact::Cross(const std::vector<llvm::Value *> &lhs, const std::vector<llvm::Value *> &rhs) {
	std::vector<llvm::Value *> res(lhs);

	for(auto const &var : rhs) {
		if(std::find(lhs.begin(), lhs.end(), var) == lhs.end())
			res.push_back(var);
	}

	return res;
}

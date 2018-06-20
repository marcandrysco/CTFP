#include "inc.hpp"


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

	for(auto iter : ranges)
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
		for(auto iter : ranges) {
			printf("    ");
			iter.Dump();
			printf("\n");
		}
	}
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
 * Compute the sum of variables.
 *   @lhs: The left vector.
 *   @rhs: The right vector.
 *   &returns: The summed vector.
 */
std::vector<void *> vars_sum(const std::vector<void *> &lhs, const std::vector<void *> &rhs) {
	std::vector<void *> res(lhs);

	for(auto const &var : rhs) {
		if(std::find(lhs.begin(), lhs.end(), var) == lhs.end())
			res.push_back(var);
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
Fact Fact::FltOLT64(Fact &lhs, Fact &rhs, void *var) {
	Fact res;

	if(lhs.vars.empty() && rhs.vars.empty()) {
		unsigned int len;

		rhs.vars.push_back(var);
		len = rhs.ranges.size();
		for(unsigned int i = 0; i < len; i++) {
			lhs.ranges.push_back(lhs.ranges[i].Above(Fact::Prev64(rhs.Lower())));
			lhs.ranges[i] = lhs.ranges[i].Below(rhs.Upper());
		}

		lhs.vars.push_back(var);
		len = lhs.ranges.size();
		for(unsigned int i = 0; i < len; i++) {
			rhs.ranges[i] = rhs.ranges[i].Above(Fact::Next64(lhs.Lower()));
			rhs.ranges.push_back(rhs.ranges[i].Below(lhs.Lower()));
		}
	}
	else {
		res.vars = vars_sum(lhs.vars, rhs.vars);
		fatal("stub");
	}

	return res;
}

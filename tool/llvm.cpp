#include "llvm.hpp"

#include <float.h>
#include <cmath>
#include <set>
#include <vector>
#include <unordered_set>
#include <unordered_map>


using namespace llvm;


#define FLT_NORM_MIN    1.17549435082228751e-38
#define FLT_NORM_MAX    3.40282346638528860e+38
#define FLT_SUBNORM_MIN 1.40129846432481707e-45
#define FLT_SUBNORM_MAX 1.17549421069244108e-38
#define FLT_ADD_MIN     9.86076072751547216e-32
#define FLT_MUL_MIN     1.08420217248550443e-19
#define FLT_DIV_MAX     9.22337203685477581e+18
#define DBL_NORM_MIN    2.22507385850720138e-308
#define DBL_NORM_MAX    1.79769313486231571e+308
#define DBL_SUBNORM_MIN 4.94065645841246544e-324
#define DBL_SUBNORM_MAX 2.22507385850720089e-308
#define DBL_ADD_MIN     -4.94065645841246544e-324
#define DBL_MUL_MIN     1.49166814624004135e-154
#define DBL_DIV_MAX     6.70390396497129855e+153


/**
 * Check if a type has a float base type.
 *   @type: The type.
 *   &returns: True if float.
 */
bool isfloat(Type *type)
{
	if(type->isVectorTy())
		return cast<VectorType>(type)->getElementType()->isFloatTy();
	else 
		return type->isFloatTy();
}

/**
 * Check if a type is a double base type.
 *   @type: The type.
 *   &returns: True if double.
 */
bool isdouble(Type *type)
{
	if(type->isVectorTy())
		return cast<VectorType>(type)->getElementType()->isDoubleTy();
	else 
		return type->isDoubleTy();
}

/**
 * Check if a type is a 80-bit FP type.
 *   @type: The type.
 *   &returns: True if 80-bit FP type.
 */
bool isfp80(Type *type)
{
	if(type->isVectorTy())
		return cast<VectorType>(type)->getElementType()->isX86_FP80Ty();
	else 
		return type->isX86_FP80Ty();
}

/**
 * Get the width of a type.
 *   @type: The type.
 *   &returns: The width.
 */
unsigned int getwidth(Type *type)
{
	if(type->isVectorTy())
		return cast<VectorType>(type)->getNumElements();
	else
		return 1;
}


#if 0

class Range {
public:
	double lo, hi;

	Range(double _lo, double _hi) {
		lo = _lo;
		hi = _hi;
	}

	static Range subfloat(double sign) {
		return Range(std::copysign(nextafterf(0.0, INFINITY), sign), std::copysign(nextafterf(FLT_MIN, -INFINITY), sign));
	}

	static Range subdouble(double sign) {
		return Range(std::copysign(nextafter(0.0, INFINITY), sign), std::copysign(nextafter(DBL_MIN, -INFINITY), sign));
	}

	bool operator<(const Range &cmp) const {
		if(lo < cmp.lo)
			return true;
		else if(lo > cmp.lo)
			return false;
		else
			return hi < cmp.hi;
	}

	bool safefloat() {
		return !overlap(*this, Range::subfloat(1.0)) && !overlap(*this, Range::subfloat(-1.0));
	}

	bool safedouble() {
		return !overlap(*this, Range::subdouble(1.0)) && !overlap(*this, Range::subdouble(-1.0));
	}

	static bool overlap(const Range &left, const Range &right) {
		return (left.lo <= right.hi) && (right.lo <= left.hi);
	}
};

class Fact {
public:
	/*
	 * nan and ranges
	 */
	bool nan;
	std::vector<Range> ranges;

	/*
	 * construction/destructors
	 */
	Fact() { nan = false; }
	~Fact() { }

	/**
	 * Create a fact with no ranges.
	 *   &returns: The fact.
	 */
	static Fact none() {
		return Fact();
	}

	/**
	 * Create a face with a single value.
	 *   @val: The value.
	 *   &returns: The fact.
	 */
	static Fact single(double val) {
		Fact res;

		res.nan = false;
		res.insert(Range(val, val));

		return res;
	};

	/**
	 * Create a fact with everything. ranges.
	 *   &returns: The fact.
	 */
	static Fact all() {
		Fact res;

		res.nan = true;
		res.insert(Range(-INFINITY, INFINITY));

		return res;
	}

	/**
	 * Create a fact for a signed integer.
	 *   &returns: The fact.
	 */
	static Fact sint() {
		Fact res;

		res.nan = false;
		res.insert(Range(-INFINITY, -1.0));
		res.insert(Range(0.0, 0.0));
		res.insert(Range(1.0, INFINITY));

		return res;
	}

	/**
	 * Creat a fact for an unsigned integer.
	 *   &returns: The fact.
	 */
	static Fact uint() {
		Fact res;

		res.nan = false;
		res.insert(Range(0.0, 0.0));
		res.insert(Range(1.0, INFINITY));

		return res;
	}


	/**
	 * Insert a range into the fact.
	 *   @range: The range.
	 */
	void insert(const Range &range) {
		ranges.push_back(range);

		if(ranges.size() > 16) {
			double lo = ranges[0].lo;
			double hi = ranges[0].hi;

			for(int i = 1; i < ranges.size(); i++) {
				lo = fmin(lo, ranges[i].lo);
				hi = fmin(hi, ranges[i].hi);
			}

			ranges.clear();
			ranges.push_back(Range(lo, hi));
		}
	}

	static Fact join(const Fact &left, const Fact &right) {
		Fact res = Fact::none();

		for(auto r = left.ranges.begin(); r != left.ranges.end(); r++)
			res.insert(*r);

		for(auto r = right.ranges.begin(); r != right.ranges.end(); r++)
			res.insert(*r);

		return res;
	}

	/**
	 * Add two facts together.
	 *   @left: The left fact.
	 *   @right: The right fact.
	 *   &returns: The new fact.
	 */
	static Fact add(const Fact &left, const Fact &right) {
		Fact res = Fact::none();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++)
				res.insert(Range(l->lo + r->lo, l->hi + r->hi));
		}

		return res;
	}

	/**
	 * Create a fact from subtraction.
	 *   @left: The left fact.
	 *   @right: The right fact.
	 *   &returns: The new fact.
	 */
	static Fact sub(const Fact &left, const Fact &right) {
		Fact res = Fact::none();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++)
				res.insert(Range(l->lo - r->lo, l->hi - r->hi));
		}

		return res;
	}

	/**
	 * Create a fact from multiplication.
	 *   @left: The left fact.
	 *   @right: The right fact.
	 *   &returns: The new fact.
	 */
	static Fact mul(const Fact &left, const Fact &right) {
		Fact res = Fact::none();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++) {
				double a = l->lo * r->lo;
				double b = l->lo * r->hi;
				double c = l->hi * r->lo;
				double d = l->hi * r->hi;

				res.insert(Range(fmin(fmin(a, b), fmin(c, d)), fmax(fmax(a, b), fmax(c, d))));
			}
		}

		return res;
	}

	/**
	 * Create a fact from squaring an input.
	 *   @in: The input.
	 *   &returns: The fact.
	 */
	static Fact square(const Fact &in) {
		Fact res = Fact::none();

		for(auto r = in.ranges.begin(); r != in.ranges.end(); r++) {
			double a = r->lo * r->lo;
			double b = r->hi * r->hi;
			double lo = fmin(a, b);
			double hi = fmax(a, b);

			res.insert(Range(((r->lo * r->hi) < 0.0) ? 0.0 : lo, hi));
		}

		return res;
	}

	static Fact div(const Fact &left, const Fact &right) {
		Fact res = Fact::none();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++) {
				if((r->lo <= 0.0) && (r->hi >= 0)) {
					res.nan = true;
				}
				else {
					double a = l->lo / r->lo;
					double b = l->lo / r->hi;
					double c = l->hi / r->lo;
					double d = l->hi / r->hi;

					res.insert(Range(fmin(fmin(a, b), fmin(c, d)), fmax(fmax(a, b), fmax(c, d))));
				}
			}
		}

		return res;
	}


	/**
	 * Check if the fact is safe for floats.
	 *   &returns: True if safe.
	 */
	bool safefloat() {
		bool safe = true;

		for(auto r = ranges.begin(); r != ranges.end(); r++)
			safe &= r->safefloat();

		return safe;
	}

	/**
	 * Check if the fact is safe for doubles.
	 *   &returns: True if safe.
	 */
	bool safedouble() {
		bool safe = true;

		for(auto r = ranges.begin(); r != ranges.end(); r++)
			safe &= r->safedouble();

		return safe;
	}

	void dump() {
		for(auto r = ranges.begin(); r != ranges.end(); r++)
			fprintf(stderr, "%.4e:%.4e, ", r->lo, r->hi);

		fprintf(stderr, "%s\n", safefloat() ? "safe" : "unsafe");
	}
};




class Analysis {
public:
	std::unordered_map<Value *, Fact> facts;

	/**
	 * Check if a fact exists.
	 *   @value: The value.
	 *   &returns: True if exists.
	 */
	bool exists(Value *value)
	{
		return facts.find(value) != facts.end();
	}

	/**
	 * Get a fact about a value. If the value is not found, the fact is
	 * set to everything.
	 *   @value: The value.
	 *   &returns: The fact.
	 */
	Fact get(Value *value) {
		auto find = facts.find(value);
		if(find != facts.end())
			return find->second;

		if(isa<ConstantFP>(value)) {
			double flt;

			if(value->getType() == Type::getFloatTy(value->getContext()))
				flt = cast<ConstantFP>(value)->getValueAPF().convertToFloat(); 
			else if(value->getType() == Type::getDoubleTy(value->getContext()))
				flt = cast<ConstantFP>(value)->getValueAPF().convertToDouble(); 
			else
				return facts[value] = Fact::all();

			return facts[value] = Fact::single(flt);
		}
		else
			return facts[value] = Fact::all();
	}

	/**
	 * Set a fact corresponding to a value.
	 *   @value: The value.
	 *   @fact: The fact.
	 */
	void set(Value *value, Fact fact) {
		facts[value] = fact;
	}
};


#endif



class Fact {
public:
	Value *m_value;

	Fact(Value *value) {
		m_value = value;
	}
};

class FloatRange {
public:
	float m_lo, m_hi;

	FloatRange(float lo, float hi) {
		m_lo = lo;
		m_hi = hi;
	}

	~FloatRange() {
	}
};

class FloatFact : Fact {
public:
	std::vector<FloatRange> ranges;

	FloatFact(Value *value) : Fact(value) { }
	~FloatFact();
};

class BoolFact : Fact {
public:
	bool m_true, m_false;

	BoolFact(Value *value) : Fact(value) { }
	~BoolFact();
};

/**
 * Range analysis class.
 */
class Analysis {
public:
	/**
	 * Member variables.
	 *   @m_facts: The value to facts mapping.
	 */
	std::unordered_map<Value *, Fact> m_facts;

	/*
	 * default constructor/destructor
	 */
	Analysis() { };
	~Analysis() { };

	/**
	 * Analyze a block.
	 *   @block: The block.
	 */
	void block(BasicBlock *block) {
		for(auto iter = block->begin(); iter != block->end(); iter++)
			value(&*iter);
		
	}

	/**
	 * Analyze a value.
	 *   @value: The value.
	 */
	void value(Value *value) {
		if(isa<ConstantFP>(value)) {
		}
		else if(isa<Instruction>(value)) {
			Instruction *inst = cast<Instruction>(value);

			switch(inst->getOpcode()) {
			case Instruction::FAdd:
				break;
			}
		}
	}

	Fact *get(Value *value) {
		return nullptr;
	}
};


struct CTFP : public FunctionPass {
	static char ID;

	CTFP() : FunctionPass(ID) {
		repl = 0;
		skip = 0;
	}

	~CTFP() {
		/*
		unsigned int a = 0, b = 0;
		FILE *file;
		
		file = fopen("ctfp.stats", "r");
		if(file != NULL) {
			fscanf(file, "%u %u\n", &a, &b);
			fclose(file);
		}

		a += repl;
		b += skip;

		file = fopen("ctfp.stats", "w");
		if(file != NULL) {
			fprintf(file, "%u %u\n", a, b);
			fclose(file);
		}
		*/
	}

	/**
	 * Member variables.
	 *   @repl, skip: The number of replacements and skips.
	 */
	unsigned int repl, skip;


	void insert(Instruction *inst, const char *id) {
		Module *mod = inst->getParent()->getParent()->getParent();
		LLVMContext &ctx = mod->getContext();

		Function *func = mod->getFunction(id);
		if(func == NULL)
			fprintf(stderr, "Missing CTFP function '%s'.\n", id), abort();

		std::vector<Value *> args;

		if(isa<CallInst>(inst)) {
			CallInst *call = cast<CallInst>(inst);
			for(unsigned int i = 0; i < call->getNumArgOperands(); i++) {
				Value *op = inst->getOperand(i);
				Type *arg = func->getFunctionType()->getParamType(i);

				if(op->getType() == arg)
					args.push_back(op);
				else
					fprintf(stderr, "Mismatched types. %d %d %s\n", i, inst->getNumOperands(), inst->getOpcodeName()), op->getType()->dump(), fprintf(stderr, "::\n"), func->getFunctionType()->dump(), exit(1);
			}
		}
		else {
			for(unsigned int i = 0; i < inst->getNumOperands(); i++) {
				Value *op = inst->getOperand(i);
				Type *arg = func->getFunctionType()->getParamType(i);

				if(op->getType() == arg) {
					args.push_back(op);
				}
				else if(op->getType()->getPointerTo() == arg) {
					fprintf(stderr, "Error\n"), abort();
					AllocaInst *alloc = new AllocaInst(op->getType());
					alloc->setAlignment(32);
					alloc->insertBefore(&*inst->getParent()->getParent()->front().getFirstInsertionPt());

					StoreInst *store = new StoreInst(op, alloc);
					store->setAlignment(32);
					store->insertBefore(inst);

					args.push_back(alloc);

					assert(op->getType()->getPointerTo() == alloc->getType());
				}
				else if((op->getType() == VectorType::get(Type::getFloatTy(ctx), 2)) && arg->isDoubleTy()) {
					fprintf(stderr, "Error\n"), abort();
					CastInst *cast = CastInst::Create(Instruction::BitCast, op, Type::getDoubleTy(ctx));
					cast->insertBefore(inst);

					args.push_back(cast);
				}
				else
					fprintf(stderr, "Mismatched types. %d %d %s\n", i, inst->getNumOperands(), inst->getOpcodeName()), op->getType()->dump(), fprintf(stderr, "::\n"), func->getFunctionType()->dump(), exit(1);
			}
		}

		CallInst *call = CallInst::Create(func, args);
		call->insertBefore(inst);

		if(func->getReturnType() == inst->getType()) {
			inst->replaceAllUsesWith(call);
		}
		else if((inst->getType() == VectorType::get(Type::getFloatTy(ctx), 2)) && func->getReturnType()->isDoubleTy()) {
			fprintf(stderr, "Error\n"), abort();
			CastInst *cast = CastInst::Create(Instruction::BitCast, call, VectorType::get(Type::getFloatTy(ctx), 2));
			cast->insertBefore(inst);

			inst->replaceAllUsesWith(cast);
		}
		else
			fprintf(stderr, "Mismatched types.\n"), func->getReturnType()->dump(), inst->getType()->dump(), inst->dump(), exit(1);

		for(unsigned int i = 0; i < inst->getNumOperands(); i++) {
			Value *op = inst->getOperand(i);
			Type *arg = func->getFunctionType()->getParamType(i);
			if(op->getType()->getPointerTo() == arg) {
				AttributeSet set = call->getAttributes();
				std::vector<unsigned int> indices = { i + 1 };
				set = set.addAttribute(ctx, indices, Attribute::getWithAlignment(ctx, 32));
				set = set.addAttribute(ctx, i + 1, Attribute::NonNull);
				set = set.addAttribute(ctx, i + 1, Attribute::ByVal);
				call->setAttributes(set);
			}
		}

		inst->eraseFromParent();

		InlineFunctionInfo info;
		bool suc = InlineFunction(call, info);
		assert(suc == true);
	}

	virtual bool runOnFunction(Function &func) {
		if(func.getName().str().find("ctfp_add") == 0)
			return false;
		else if(func.getName().str().find("ctfp_sub") == 0)
			return false;
		else if(func.getName().str().find("ctfp_mul") == 0)
			return false;
		else if(func.getName().str().find("ctfp_div") == 0)
			return false;
		else if(func.getName().str().find("ctfp_sqrt") == 0)
			return false;
		LLVMContext &ctx = func.getContext();

		Module *mod = func.getParent();
		if(mod->getFunction("ctfp_add1_f1") == nullptr) {
			SMDiagnostic err;
			if(getenv("CTFP_DIR") == nullptr)
				fprintf(stderr, "Missing 'CTFP_DIR' variable.\n"), abort();

			std::string path = std::string(getenv("CTFP_DIR")) + std::string("/ctfp.bc");
			std::unique_ptr<Module> parse = parseIRFile(path, err, ctx);
			if(parse == nullptr)
				fprintf(stderr, "Failed to load CTFP bitcode (%s).\n", path.c_str()), abort();

			if(Linker::linkModules(*mod, std::move(parse)))
				fprintf(stderr, "Link failed.\n"), abort();
		}

		for(auto block = func.begin(); block != func.end(); block++) {
			auto iter = block->begin();
			while(iter != block->end()) {
				char type, id[32];
				std::string name = "";
				Instruction *inst = &*iter++;

				if(inst->getOpcode() == Instruction::FAdd)
					name = "add";
				else if(inst->getOpcode() == Instruction::FSub)
					name = "sub";
				else if(inst->getOpcode() == Instruction::FMul)
					name = "mul";
				else if(inst->getOpcode() == Instruction::FDiv)
					name = "div";
				else if(inst->getOpcode() == Instruction::Call) {
					CallInst *call = cast<CallInst>(inst);
					Function *func = call->getCalledFunction();
					if(func != nullptr) {
						static std::vector<std::string> list {
							"acos",        "acosf",       "acosh",         "acoshf",            "acoshl",         "acosl",         "asin",       "asinf",      "asinh",       "asinhf",      "asinhl",
							"asinl",       "atan2",       "atan2f",        "atan2l",            "atan",           "atanf",         "atanh",      "atanhf",     "atanhl",      "atanl",       "cbrt",
							"cbrtf",       "cbrtl",       "ceil",          "ceilf",             "ceill",          "copysign",      "copysignf",  "copysignl",  "__cos",       "cos",         "__cosdf",
							"cosf",        "cosh",        "coshf",         "coshl",             "__cosl",         "cosl",          "erf",        "erff",       "erfl",        "exp10",       "exp10f",
							"exp10l",      "exp2",        "exp2f",         "exp2l",             "exp",            "expf",          "expl",       "expm1",      "expm1f",      "expm1l",      "__expo2",
							"__expo2f",    "fabs",        "fabsf",         "fabsl",             "fdim",           "fdimf",         "fdiml",      "finite",     "finitef",     "floor",       "floorf",
							"floorl",      "fma",         "fmaf",          "fmal",              "fmax",           "fmaxf",         "fmaxl",      "fmin",       "fminf",       "fminl",       "fmod",
							"fmodf",       "fmodl",       "__fpclassify",  "__fpclassifyf",     "__fpclassifyl",  "frexp",         "frexpf",     "frexpl",     "hypot",       "hypotf",      "hypotl",
							"ilogb",       "ilogbf",      "ilogbl",        "__invtrigl",        "j0",             "j0f",           "j1",         "j1f",        "jn",          "jnf",         "ldexp",
							"ldexpf",      "ldexpl",      "lgamma",        "lgammaf",           "lgammaf_r",      "lgammal",       "lgamma_r",   "llrint",     "llrintf",     "llrintl",     "llround",
							"llroundf",    "llroundl",    "log10",         "log10f",            "log10l",         "log1p",         "log1pf",     "log1pl",     "log2",        "log2f",       "log2l",
							"logb",        "logbf",       "logbl",         "log",               "logf",           "logl",          "lrint",      "lrintf",     "lrintl",      "lround",      "lroundf",
							"lroundl",     "modf",        "modff",         "modfl",             "nan",            "nanf",          "nanl",       "nearbyint",  "nearbyintf",  "nearbyintl",  "nextafter",
							"nextafterf",  "nextafterl",  "nexttoward",    "nexttowardf",       "nexttowardl",    "__polevll",     "pow",        "powf",       "powl",        "remainder",   "remainderf",
							"remainderl",  "__rem_pio2",  "__rem_pio2f",   "__rem_pio2_large",  "__rem_pio2l",    "remquo",        "remquof",    "remquol",    "rint",        "rintf",       "rintl",
							"round",       "roundf",      "roundl",        "scalb",             "scalbf",         "scalbln",       "scalblnf",   "scalblnl",   "scalbn",      "scalbnf",     "scalbnl",
							"__signbit",   "__signbitf",  "__signbitl",    "signgam",           "significand",    "significandf",  "__sin",      "sin",        "sincos",      "sincosf",     "sincosl",
							"__sindf",     "sinf",        "sinh",          "sinhf",             "sinhl",          "__sinl",        "sinl",       "sqrt",       "sqrtf",       /*"sqrtl",*/       "__tan",
							"tan",         "__tandf",     "tanf",          "tanh",              "tanhf",          "tanhl",         "__tanl",     "tanl",       "tgamma",      "tgammaf",
							"tgammal",     "trunc",       "truncf",        "truncl",
						};

						if(func->getName() == "sqrt") {
							insert(inst, "ctfp_sqrt1_d1");
						}
						else if(func->getName() == "sqrtf") {
							insert(inst, "ctfp_sqrt1_f1");
						}
						else {
							auto find = std::find(std::begin(list), std::end(list), func->getName());
							if(find != std::end(list)) {
								std::string ctfp = "ctfp_" + *find;
								call->setCalledFunction(mod->getOrInsertFunction(ctfp, func->getFunctionType()));
								//printf("special! %s\n", func->getName().data());
							}
						}
					}
				}

				if(name == "")
					continue;

				if(isfloat(inst->getType()))
					type = 'f';
				else if(isdouble(inst->getType()))
					type = 'd';
				else if(isfp80(inst->getType()))
					continue;
				else {
					printf("Unhandled type\n");

					continue;
				}

				const char *ver = getenv("CTFP_VER");
				if(ver == NULL)
					fprintf(stderr, "Missing CTFP version.\n"), abort();
				else if((strcmp(ver, "1") != 0) && (strcmp(ver, "2") != 0) && (strcmp(ver, "3") != 0))
					fprintf(stderr, "Invalid CTFP version.\n"), abort();

				sprintf(id, "ctfp_%s%s_%c%u", name.c_str(), ver, type, getwidth(inst->getType()));
				insert(inst, id);
			}
		}

		return true;
	}
};

char CTFP::ID = 0;
RegisterPass<CTFP> X("ctfp", "Constant Time Floating-Point");

static void registerCTFP(const PassManagerBuilder &, legacy::PassManagerBase &PM) {
    PM.add(new CTFP());
}
static RegisterStandardPasses RegisterCTFP(PassManagerBuilder::EP_OptimizerLast, registerCTFP);

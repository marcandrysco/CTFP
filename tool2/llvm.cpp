#include <float.h>
#include <cmath>
#include <set>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <llvm/Pass.h>
#include <llvm/IR/Function.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Linker/Linker.h>
#include <llvm/IR/DiagnosticInfo.h>
#include <llvm/IR/CFG.h>

using namespace llvm;


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


struct CTFP : public FunctionPass {
	static char ID;

	CTFP() : FunctionPass(ID) {
		repl = 0;
		skip = 0;
	}

	~CTFP() {
		printf("repl: %u\n", repl);
		printf("skip: %u\n", skip);
	}

	/**
	 * Member variables.
	 *   @repl, skip: The number of replacements and skips.
	 */
	unsigned int repl, skip;


	void insert(Instruction *inst, const char *id, Analysis &analysis) {
		Module *mod = inst->getParent()->getParent()->getParent();
		LLVMContext &ctx = mod->getContext();

		if(analysis.get(inst).safefloat())
			skip++;
		else
			repl++;

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
		Analysis analysis;

		for(auto block = func.begin(); block != func.end(); block++) {
			for(auto inst = block->begin(); inst != block->end(); inst++) {
				Use *ops = inst->getOperandList();

				switch(inst->getOpcode()) {
				case Instruction::FAdd:
					analysis.set(&*inst, Fact::add(analysis.get(inst->getOperand(0)), analysis.get(inst->getOperand(1))));
					break;

				case Instruction::FSub:
					analysis.set(&*inst, Fact::sub(analysis.get(inst->getOperand(0)), analysis.get(inst->getOperand(1))));
					break;

				case Instruction::FMul:
					if(ops[0] == ops[1])
						analysis.set(&*inst, Fact::square(analysis.get(ops[0])));
					else
						analysis.set(&*inst, Fact::mul(analysis.get(ops[0]), analysis.get(ops[1])));
					break;

				case Instruction::FDiv:
					analysis.set(&*inst, Fact::div(analysis.get(inst->getOperand(0)), analysis.get(inst->getOperand(1))));
					break;

				case Instruction::SIToFP:
					analysis.set(&*inst, Fact::sint());
					break;

				case Instruction::UIToFP:
					analysis.set(&*inst, Fact::uint());
					break;
				}
			}
		}

		LLVMContext &ctx = func.getContext();

		printf("func: %s\n", func.getName().str().data());

		Module *mod = func.getParent();
		if(mod->getFunction("ctfp_add1_f1") == nullptr) {
			SMDiagnostic err;
			std::string root = getenv("CTFP_DIR");
			if(root.c_str() == nullptr)
				fprintf(stderr, "Missing 'CTFP_DIR' variable.\n"), abort();

			std::string path = root + std::string("/ctfp.bc");
			std::unique_ptr<Module> parse = parseIRFile(path, err, ctx);
			if(parse == nullptr)
				fprintf(stderr, "Failed to load CTFP bitcode (%s).\n", path.c_str()), abort();

			if(Linker::linkModules(*mod, std::move(parse)))
				fprintf(stderr, "Link failed.\n"), abort();
		}

		for(auto block = func.begin(); block != func.end(); block++) {
			auto iter = block->begin();
			while(iter != block->end()) {
				Instruction *inst = &*iter++;

				switch(inst->getOpcode()) {
				case Instruction::FAdd:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_add1_f1", analysis);
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_add1_d1", analysis);
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_add1_f2", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_add1_d2", analysis);
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_add1_f4", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_add1_d4", analysis);
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fadd%lu\n", type->getNumElements());
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FSub:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_sub1_f1", analysis);
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_sub1_d1", analysis);
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_sub1_f2", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_sub1_d2", analysis);
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_sub1_f4", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_sub1_d4", analysis);
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fsub%lu\n", type->getNumElements());
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FMul:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_mul1_f1", analysis);
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_mul1_d1", analysis);
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul1_f2", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul1_d2", analysis);
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul1_f4", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul1_d4", analysis);
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fmul%lu\n", type->getNumElements());
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FDiv:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_div1_f1", analysis);
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_div1_d1", analysis);
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_div1_f2", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_div1_d2", analysis);
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_div1_f4", analysis);
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_div1_d4", analysis);
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fdiv\n");
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::Call:
					if(isa<CallInst>(inst)) {
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
								"__sindf",     "sinf",        "sinh",          "sinhf",             "sinhl",          "__sinl",        "sinl",       "sqrt",       "sqrtf",       "sqrtl",       "__tan",
								"tan",         "__tandf",     "tanf",          "tanh",              "tanhf",          "tanhl",         "__tanl",     "tanl",       "tgamma",      "tgammaf",
								"tgammal",     "trunc",       "truncf",        "truncl",
							};

							if(func->getName() == "sqrt") {
								call->dump();
								insert(inst, "ctfp_sqrt1_d1", analysis);
							}
							else if(func->getName() == "sqrtf") {
								call->dump();
								insert(inst, "ctfp_sqrt1_f1", analysis);
							}
							else {
								auto find = std::find(std::begin(list), std::end(list), func->getName());
								if(find != std::end(list)) {
									std::string ctfp = "ctfp_" + *find;
									call->setCalledFunction(mod->getOrInsertFunction(ctfp, func->getFunctionType()));
									printf("special! %s\n", func->getName().data());
								}
							}
						}
					}
				}
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

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

	bool operator<(const Range &cmp) const {
		if(lo < cmp.lo)
			return true;
		else if(lo > cmp.lo)
			return false;
		else
			return hi < cmp.hi;
	}
};

class Fact {
public:
	std::vector<Range> ranges;
	
	static Fact all() {
		Fact res;

		res.insert(Range(-INFINITY, INFINITY));

		return res;
	}

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
		Fact res = all();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++)
				res.insert(Range(l->lo + r->lo, l->hi + r->hi));
		}

		return res;
	}

	static Fact sub(const Fact &left, const Fact &right) {
		Fact res = all();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++)
				res.insert(Range(l->lo - r->lo, l->hi - r->hi));
		}

		return res;
	}

	static Fact mul(const Fact &left, const Fact &right) {
		Fact res = all();

		for(auto l = left.ranges.begin(); l != left.ranges.end(); l++) {
			for(auto r = right.ranges.begin(); r != right.ranges.end(); r++) {
				double a, b, c, d;

				a = l->lo * r->lo;
				b = l->lo * r->hi;
				c = l->hi * r->lo;
				d = l->hi * r->hi;

				res.insert(Range(fmin(fmin(a, b), fmin(c, d)), fmax(fmax(a, b), fmax(c, d))));
			}
		}

		return res;
	}

	static Fact div(const Fact &left, const Fact &right) {
		return Fact::all();
	}
};

class Analysis {
public:
	std::unordered_map<Instruction *, Fact> facts;

	Fact get(Instruction *inst) {
		auto find = facts.find(inst);
		if(find != facts.end())
			return find->second;

		return facts[inst] = Fact::all();
	}

	void set(Instruction *inst, Fact fact) {
		facts[inst] = fact;
	}
};


struct CTFP : public FunctionPass {
	static char ID;

	CTFP() : FunctionPass(ID) { }

	int numT = 0;
	void insert(Instruction *inst, const char *id) {
		Module *mod = inst->getParent()->getParent()->getParent();

		Function *func = mod->getFunction(id);
		if(func == NULL) fprintf(stderr, "Missing CTFP function '%s'.\n", id), abort();

		LLVMContext &ctx = func->getContext();

		if(func == nullptr) printf("missing  %s\n", id);
		if(func == nullptr) return; // TODO: remove
		assert(func != nullptr);

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
				switch(inst->getOpcode()) {
				case Instruction::FAdd:
					analysis.set(&*inst, Fact::add(analysis.get(inst->getOperand(0)), analysis.get(inst->getOperand(1))));
					break;

				case Instruction::FSub:
					break;

				case Instruction::FMul:
					break;

				case Instruction::FDiv:
					break;
				}
			}
		}


		LLVMContext &ctx = func.getContext();

		if(func.getName().str().find("ctfp_") == 0)
			return false;

		Module *mod = func.getParent();
		if(func.getParent()->getFunction("ctfp_add1_f1") == nullptr) {
			SMDiagnostic err;
			std::unique_ptr<Module> parse = parseIRFile("/data/ctfp/tool2/ctfp.bc", err, ctx);
			assert(parse != nullptr);

			if(Linker::linkModules(*mod, std::move(parse)))
				fprintf(stderr, "Link failed.\n"), exit(1);
		}
		for(auto block = func.begin(); block != func.end(); block++) {
			auto iter = block->begin();
			while(iter != block->end()) {
				Instruction *inst = &*iter++;

				switch(inst->getOpcode()) {
				case Instruction::FAdd:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_add1_f1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_add1_d1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_add1_f2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_add1_d2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_add1_f4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_add1_d4");
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
						insert(inst, "ctfp_sub1_f1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_sub1_d1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_sub1_f2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_sub1_d2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_sub1_f4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_sub1_d4");
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
						insert(inst, "ctfp_mul1_f1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_mul1_d1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul1_f2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul1_d2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul1_f4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul1_d4");
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
						insert(inst, "ctfp_div1_f1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_div1_d1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_div1_f2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_div1_d2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_div1_f4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_div1_d4");
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fdiv%lu\n", type->getNumElements());
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
								insert(inst, "ctfp_sqrt1_d1");
							}
							else if(func->getName() == "sqrtf") {
								call->dump();
								insert(inst, "ctfp_sqrt1_f1");
							}
							else {
								auto find = std::find(std::begin(list), std::end(list), func->getName());
								if(find != std::end(list))
									printf("special! %s\n", func->getName().data());
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

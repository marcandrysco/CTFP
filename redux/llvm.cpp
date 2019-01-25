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

#include <float.h>
#include <regex>
#include <cmath>
#include <set>
#include <vector>
#include <unordered_set>
#include <unordered_map>


using namespace llvm;


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

struct CTFP : public FunctionPass {
	static char ID;

	CTFP() : FunctionPass(ID) {
		repl = 0;
		skip = 0;
	}

	~CTFP() {
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
					AllocaInst *alloc = new AllocaInst(op->getType(), 0);
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
				AttributeList set = call->getAttributes();
				set = set.addAttribute(ctx, i + 1, Attribute::getWithAlignment(ctx, 32));
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
		LLVMContext &ctx = func.getContext();

		if(func.getName().str().find("ctfp_restrict_") == 0)
			return false;
		else if(func.getName().str().find("ctfp_full_") == 0)
			return false;
		else if(func.getName().str().find("ctfp_fast_") == 0)
			return false;

		Module *mod = func.getParent();
		if(mod->getFunction("ctfp_restrict_add_f32v4") == nullptr) {
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
				char id[16];
				int bits, width;
				std::string name = "", sel = "";
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
							insert(inst, "ctfp_restrict_sqrt_f64v1");
						}
						else if(func->getName() == "sqrtf") {
							insert(inst, "ctfp_restrict_sqrt_f32v1");
						}
						else if(func->getName() == "llvm.sqrt.f32") {
							insert(inst, "ctfp_restrict_sqrt_f32v1");
						}
						else if(func->getName() == "llvm.sqrt.f32v2") {
							insert(inst, "ctfp_restrict_sqrt_f32v2");
						}
						else if(func->getName() == "llvm.sqrt.f32v4") {
							insert(inst, "ctfp_restrict_sqrt_f32v4");
						}
						else if(func->getName() == "llvm.sqrt.f32v8") {
							insert(inst, "ctfp_restrict_sqrt_f32v8");
						}
						else if(func->getName() == "llvm.sqrt.f32v16") {
							insert(inst, "ctfp_restrict_sqrt_f32v16");
						}
						else if(func->getName() == "llvm.sqrt.f64") {
							insert(inst, "ctfp_restrict_sqrt_f64v1");
						}
						else if(func->getName() == "llvm.sqrt.f64v2") {
							insert(inst, "ctfp_restrict_sqrt_f64v2");
						}
						else if(func->getName() == "llvm.sqrt.f64v4") {
							insert(inst, "ctfp_restrict_sqrt_f64v4");
						}
						else if(func->getName() == "llvm.sqrt.f64v8") {
							insert(inst, "ctfp_restrict_sqrt_f64v8");
						}
						else {
							auto find = std::find(std::begin(list), std::end(list), func->getName());
							if(find != std::end(list)) {
								std::string ctfp = "ctfp_" + *find;
								call->setCalledFunction(mod->getOrInsertFunction(ctfp, func->getFunctionType()));
							}
						}
					}
				}

				if(name == "")
					continue;

				if(isfloat(inst->getType()))
					bits = 32;
				else if(isdouble(inst->getType()))
					bits = 64;
				else if(isfp80(inst->getType()))
					continue;
				else {
					printf("Unhandled type\n");
					continue;
				}

				const char *ver = getenv("CTFP_VER");
				if(ver == NULL)
					fprintf(stderr, "Missing CTFP version.\n"), abort();
				else if(strcmp(ver, "1") == 0)
					sel = "restrict";
				else if(strcmp(ver, "2") == 0)
					sel = "full";
				else if(strcmp(ver, "3") == 0)
					sel = "fast";
				else
					fprintf(stderr, "Invalid CTFP version.\n"), abort();

				std::string extra = "";
				width = getwidth(inst->getType());
				if((bits == 32) && (width == 1))
					extra = "_hack";
				else if((bits == 64) && (width == 1))
					extra = "_hack";

				sprintf(id, "ctfp_%s_%s_f%dv%d%s", sel.c_str(), name.c_str(), bits, width, extra.c_str());
				insert(inst, id);
			}
		}

		{
			auto iter = mod->begin();

			while(iter != mod->end()) {
				Function *func = &*iter++;

				std::string name = func->getName().str();
				if(regex_match(name, std::regex("^ctfp_restrict_.*$")))
					func->eraseFromParent();
				else if(regex_match(name, std::regex("^ctfp_full_.*$")))
					func->eraseFromParent();
				else if(regex_match(name, std::regex("^ctfp_fast_.*$")))
					func->eraseFromParent();
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

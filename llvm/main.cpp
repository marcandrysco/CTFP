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

using namespace llvm;

struct CTFP : public FunctionPass {
	static char ID;

	CTFP() : FunctionPass(ID) { }

	void insert(Instruction *inst, const char *op) {
		Module *mod = inst->getParent()->getParent()->getParent();
		Function *func = mod->getFunction(op);

		if(func == nullptr) printf("missing  %s\n", op);
		if(func == nullptr) return; // TODO: remove
		assert(func != nullptr);

		std::vector<Value *> args;
		IRBuilder<> builder(inst);

		for(unsigned int i = 0; i < inst->getNumOperands(); i++)
			args.push_back(inst->getOperand(i));

		CallInst *call = builder.CreateCall(func, args);
		inst->replaceAllUsesWith(call);
		inst->eraseFromParent();

		InlineFunctionInfo info;
		bool suc = InlineFunction(call, info);
		assert(suc == true);
	}

	virtual bool runOnFunction(Function &func) {
		LLVMContext &ctx = func.getContext();

		if(func.getName().str().find("ctfp_") == 0)
			return false;

		Module *mod = func.getParent();
		if(func.getParent()->getFunction("ctfp_dbl_mul_1") == nullptr) {
			SMDiagnostic err;
			std::unique_ptr<Module> parse = parseIRFile("/data/ctfp/lib/ctfp.ll", err, ctx);
			assert(mod != nullptr);

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
						insert(inst, "ctfp_add_f_1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_add_d_1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul_f_2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul_d_2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_add_f_4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_add_d_4");
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fmul%lu", type->getNumElements());
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FSub:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_sub_f_1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_sub_d_1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_sub_f_2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_sub_d_2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								printf("ctfp_sub_f_4");
							else if(type->getElementType()->isDoubleTy())
								printf("ctfp_sub_d_4");
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fmul%lu", type->getNumElements());
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FMul:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_flt_mul_1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_dbl_mul_1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul_f_2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul_d_2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_mul_f_4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_mul_d_4");
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fmul%lu", type->getNumElements());
						}
					}
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FDiv:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_flt_div_1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_dbl_div_1");
					else if(inst->getType()->isVectorTy()) {
						VectorType *type = cast<VectorType>(inst->getType());
						switch(type->getNumElements()) {
						case 2:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_div_f_2");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_div_d_2");
							else
								printf("Unhandled type\n");

							break;

						case 4:
							if(type->getElementType()->isFloatTy())
								insert(inst, "ctfp_div_f_4");
							else if(type->getElementType()->isDoubleTy())
								insert(inst, "ctfp_div_d_4");
							else
								printf("Unhandled type\n");

							break;

						default:
							printf("Unhandled fmul%lu", type->getNumElements());
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
								"exp", "expf", "exp10", "exp10f", "exp2", "exp2f",
									"log", "logf", "log10", "log10f", "log2", "log2f",
									"sin", "sinf", "cos", "cosf", "tan", "tanf",
									"pow", "powf",
									"gamma", "gammaf",
							};

							if(func->getName() == "sqrt")
								insert(inst, "ctfp_sqrt_d_1");
							else if(func->getName() == "sqrtf")
								insert(inst, "ctfp_sqrt_f_1");
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

		return false;
	}
};

char CTFP::ID = 0;
RegisterPass<CTFP> X("ctfp", "Constant Time Floating-Point");

static void registerCTFP(const PassManagerBuilder &, legacy::PassManagerBase &PM) {
    PM.add(new CTFP());
}
static RegisterStandardPasses RegisterCTFP(PassManagerBuilder::EP_OptimizerLast, registerCTFP);

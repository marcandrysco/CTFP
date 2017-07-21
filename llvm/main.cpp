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
		assert(func != nullptr);

		std::vector<Value *> args;
		IRBuilder<> builder(inst);

		args.push_back(inst->getOperand(0));
		args.push_back(inst->getOperand(1));

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
				case Instruction::FMul:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_flt_mul_1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_dbl_mul_1");
					else
						fprintf(stderr, "Unknown type!\n");

					break;

				case Instruction::FDiv:
					if(inst->getType()->isFloatTy())
						insert(inst, "ctfp_flt_div_1");
					else if(inst->getType()->isDoubleTy())
						insert(inst, "ctfp_dbl_div_1");
					else
						fprintf(stderr, "Unknown type!\n");

					break;
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
static RegisterStandardPasses RegisterCTFP(PassManagerBuilder::EP_EarlyAsPossible, registerCTFP);

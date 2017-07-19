#include <unordered_map>
#include <llvm/Pass.h>
#include <llvm/IR/Function.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/IR/DiagnosticInfo.h>

using namespace llvm;

struct CTFP : public BasicBlockPass {
	static char ID;
	LLVMContext ctx;
	std::unique_ptr<Module> mod;

	BasicBlock *ctfp_dbl_mul1, *ctfp_dbl_add_1;

	static void replace(Instruction *inst, BasicBlock *block) {
		IRBuilder<> builder(inst);
		std::unordered_map<Value *, Value *> map;

		for(auto src = block->begin(); src != block->end(); src++) {
			if(src->getOpcode() == Instruction::Ret) {
				auto ret = map.find(cast<ReturnInst>(&*src)->getReturnValue());
				assert(ret != map.end());

				inst->replaceAllUsesWith(ret->second);
			}
			else {
				Instruction *add = src->clone();
				builder.Insert(add);

				for(unsigned int i = 0; i < add->getNumOperands(); i++) {
					Argument *arg = dyn_cast<Argument>(add->getOperand(i));
					if(arg != nullptr)
						add->setOperand(i, inst->getOperand(arg->getArgNo()));
					else {
						auto ret = map.find(add->getOperand(i));
						if(ret != map.end())
							add->setOperand(i, ret->second);
					}
				}

				map[&*src] = add;
			}
		}
	}

	CTFP() : BasicBlockPass(ID) {
		SMDiagnostic err;
		mod = parseIRFile("/data/ctfp/lib/ctfp.ll", err, ctx);
		assert(mod != nullptr);

		Function *func;

		func = mod->getFunction("ctfp_dbl_mul_1");
		assert(func != nullptr);
		assert(func->size() == 1);
		ctfp_dbl_mul1 = &*func->begin();

		func = mod->getFunction("ctfp_dbl_add_1");
		assert(func != nullptr);
		assert(func->size() == 1);
		ctfp_dbl_add_1 = &*func->begin();
	}

	virtual bool runOnBasicBlock(BasicBlock &block) {
		//LLVMContext &ctx = block.getContext();

		auto iter = block.begin();
		while(iter != block.end()) {
			Instruction *inst = &*iter++;

			switch(inst->getOpcode()) {
			case Instruction::FAdd:
				if(inst->getType()->isFloatTy()) {
				}
				else if(inst->getType()->isDoubleTy()) {
					replace(inst, ctfp_dbl_add_1);
				}
				else
					fprintf(stderr, "Unknown type!\n");

				break;

			case Instruction::FSub:
				if(inst->getType()->isFloatTy()) {
				}
				else if(inst->getType()->isDoubleTy()) {
				}
				else
					fprintf(stderr, "Unknown type!\n");

				break;

			case Instruction::FMul:
				if(inst->getType()->isFloatTy()) {
				}
				else if(inst->getType()->isDoubleTy())
					replace(inst, ctfp_dbl_mul1);
					/*
					std::vector<Value *> args;
					IRBuilder<> builder(inst);

					args.push_back(inst->getOperand(0));
					args.push_back(inst->getOperand(1));

					inst->replaceAllUsesWith(builder.CreateCall(dbl_mul_1, args));
					 */
				else
					fprintf(stderr, "Unknown type!\n");

				break;

			case Instruction::FDiv:
				if(inst->getType()->isFloatTy()) {
				}
				else if(inst->getType()->isDoubleTy()) {
				}
				else
					fprintf(stderr, "Unknown type!\n");

				break;
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

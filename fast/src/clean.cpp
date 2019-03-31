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

#include <regex>

/*
 * just use the llvm namespace
 */
using namespace llvm;

struct CTFP : public ModulePass {
	static char ID;

	CTFP() : ModulePass(ID) {
	}

	~CTFP() {
	}

	virtual bool runOnModule(Module &module) {
		auto iter = module.begin();

		while(iter != module.end()) {
			Function *func = &*iter++;

			std::string name = func->getName().str();
			if(regex_match(name, std::regex("^ctfp_.*_[0-9]+$")))
				func->eraseFromParent();
		}

		return true;
	}
};

char CTFP::ID = 0;
RegisterPass<CTFP> X("ctfp-clean", "Constant Time Floating-Point Cleanup");

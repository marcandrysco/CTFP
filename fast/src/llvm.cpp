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

#include "../ival/inc.hpp"


/*
 * local declarations
 */
bool ctfp_func(llvm::Function &func);
void ctfp_block(llvm::BasicBlock& block, Pass& pass);
void ctfp_protect(llvm::Instruction *inst, unsigned int i, double safe);


/**
 * Run CTFP on a function.
 *   @func: The function.
 *   &returns: True if modified.
 */
bool ctfp_func(llvm::Function& func) {
	Pass pass;

	if(func.getName().str().find("ctfp_restrict_") == 0)
		return false;
	else if(func.getName().str().find("ctfp_full_") == 0)
		return false;
	else if(func.getName().str().find("ctfp_fast_") == 0)
		return false;

	int i = 0;
	for(auto &arg : func.args()) {
		if(arg.getName() == "")
			arg.setName("a" + std::to_string(i++));

		Range range;
		Type type = Pass::GetType(arg);

		switch(type.kind) {
		case Kind::Unk:
			range = Range(RangeUnk());
			break;

		case Kind::Int:
			if(type.width == 32)
				range = Range(RangeVecI32(RangeI32::All()));
			else if(type.width == 64)
				range = Range(RangeVecI64(RangeI64::All()));

			break;

		case Kind::Flt:
			if(type.width == 32)
				range = Range(RangeVecF32(RangeF32::All()));
			else if(type.width == 64)
				range = Range(RangeVecF64(RangeF64::All()));

			break;
		}

		pass.map[&arg] = range;
		std::cout << "arg " << arg.getName().data() << "\n    " << range.Str() << "\n";
	}

	for(llvm::BasicBlock &block : func)
		ctfp_block(block, pass);

	return true;
}

static const float addmin32 = 9.86076131526264760e-32f;
static const double addmin64 = 2.00416836000897278e-292;
static const float mulmin32 = 1.08420217248550443e-19f;
static const double mulmin64 = 1.49166814624004135e-154;
static const float safemin32 = 5.960464477539063e-8f;
static const double safemin64 = 1.1102230246251565e-16;
//static const float safemax32 = 16777216.0f;
//static const double safemax64 = 9007199254740992.0;

/**
 * Run CTFP on a block.
 *   @block: The block.
 *   @pass: The pass.
 *   &returns: True if modified.
 */
void ctfp_block(llvm::BasicBlock& block, Pass& pass) {
	auto iter = block.begin();

	std::cout << block.getName().data() << ":\n";
	while(iter != block.end()) {
		llvm::Instruction *inst = &*iter++;
		Info info = Pass::GetInfo(*inst);

		if(((info.op == Op::Add) || (info.op == Op::Sub)) && (info.type.kind == Kind::Flt) && (info.type.width == 32)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(addmin32)) {
				Range safe = std::get<RangeVecF32>(pass.map[lhs].var).Protect(safemin32);
				ctfp_protect(inst, 0, safemin32);
				printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(addmin32)) {
				Range safe = std::get<RangeVecF32>(pass.map[rhs].var).Protect(safemin32);
				ctfp_protect(inst, 1, safemin32);
				printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}
		else if(((info.op == Op::Add) || (info.op == Op::Sub)) && (info.type.kind == Kind::Flt) && (info.type.width == 64)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(addmin64)) {
				Range safe = std::get<RangeVecF64>(pass.map[lhs].var).Protect(safemin64);
				ctfp_protect(inst, 0, safemin64);
				printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(addmin64)) {
				Range safe = std::get<RangeVecF64>(pass.map[rhs].var).Protect(safemin64);
				ctfp_protect(inst, 1, safemin64);
				printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}
		else if((info.op == Op::Mul) && (info.type.kind == Kind::Flt) && (info.type.width == 32)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(mulmin32)) {
				Range safe = std::get<RangeVecF32>(pass.map[lhs].var).Protect(safemin32);
				ctfp_protect(inst, 0, safemin32);
				printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(mulmin32)) {
				Range safe = std::get<RangeVecF32>(pass.map[rhs].var).Protect(safemin32);
				ctfp_protect(inst, 1, safemin32);
				printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}
		else if((info.op == Op::Mul) && (info.type.kind == Kind::Flt) && (info.type.width == 64)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(mulmin64)) {
				Range safe = std::get<RangeVecF64>(pass.map[lhs].var).Protect(safemin64);
				ctfp_protect(inst, 0, safemin64);
				printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(mulmin64)) {
				Range safe = std::get<RangeVecF64>(pass.map[rhs].var).Protect(safemin64);
				ctfp_protect(inst, 1, safemin64);
				printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}

		pass.Proc(*inst);

		inst->print(llvm::outs());
		std::cout << "\n";

		auto fact = pass.map.find(inst);
		if(fact != pass.map.end())
			printf("    %s\n", fact->second.Str().data());
		else
			printf("    missing\n");
	}
}

/**
 * Protect an instruction operand.
 *   @inst: The instruction.
 *   @i: The operand index.
 *   @safe: The safe value.
 */
void ctfp_protect(llvm::Instruction *inst, unsigned int i, double safe) {

	llvm::Value *op = inst->getOperand(i);
	llvm::LLVMContext &ctx = inst->getContext();
	llvm::Module *mod = inst->getParent()->getParent()->getParent();

	llvm::Type *cast;
	llvm::Constant *zero, *ones;
	std::string post;

	if(inst->getType()->isFloatTy()) {
		post = ".f32";
		cast = llvm::Type::getInt32Ty(ctx);
		zero = llvm::ConstantInt::get(cast, 0);
		ones = llvm::ConstantInt::get(cast, 0xFFFFFFFF);
	}
	else if(inst->getType()->isDoubleTy()) {
		post = ".f64";
		cast = llvm::Type::getInt64Ty(ctx);
		zero = llvm::ConstantInt::get(cast, 0);
		ones = llvm::ConstantInt::get(cast, 0xFFFFFFFFFFFFFFFF);
	}
	else if(inst->getType()->isVectorTy()) {
		uint32_t cnt = inst->getType()->getVectorNumElements();

		if(inst->getType()->getScalarType()->isFloatTy()) {
			post = ".f32";
			cast = llvm::Type::getInt32Ty(ctx);
			zero = llvm::ConstantInt::get(cast, 0);
			ones = llvm::ConstantInt::get(cast, 0xFFFFFFFF);
		}
		else if(inst->getType()->getScalarType()->isDoubleTy()) {
			post = ".f64";
			cast = llvm::Type::getInt64Ty(ctx);
			zero = llvm::ConstantInt::get(cast, 0);
			ones = llvm::ConstantInt::get(cast, 0xFFFFFFFFFFFFFFFF);
		}
		else
			fatal("Invalid type.");

		post = post + "v" + std::to_string(cnt);
		cast = llvm::VectorType::get(cast, cnt);
		zero = llvm::ConstantVector::getSplat(cnt, zero);
		ones = llvm::ConstantVector::getSplat(cnt, ones);
	}
	else
		fatal("Invalid type.");

	llvm::Constant *fabs = mod->getOrInsertFunction("llvm.fabs" + post, llvm::FunctionType::get(op->getType(), { op->getType() } , false));
	llvm::Instruction *abs = llvm::CallInst::Create(llvm::cast<llvm::Function>(fabs)->getFunctionType(), fabs, { op }, "", inst);

	llvm::CmpInst *cmp = llvm::FCmpInst::Create(llvm::Instruction::OtherOps::FCmp, llvm::CmpInst::FCMP_OLT, abs, llvm::ConstantFP::get(op->getType(), safe), "", inst);
	llvm::SelectInst *sel = llvm::SelectInst::Create(cmp, zero, ones, "", inst);
	llvm::CastInst *toint = llvm::CastInst::CreateBitOrPointerCast(op, cast, "", inst);
	llvm::BinaryOperator *mask = llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::And, toint, sel, "", inst);
	llvm::CastInst *tofp = llvm::CastInst::CreateBitOrPointerCast(mask, op->getType(), "", inst);

	llvm::Constant *copysign = mod->getOrInsertFunction("llvm.copysign" + post, llvm::FunctionType::get(op->getType(), { op->getType(), op->getType() }, false));
	llvm::Instruction *done = llvm::CallInst::Create(llvm::cast<llvm::Function>(copysign)->getFunctionType(), copysign, { tofp, op }, "", inst);

	inst->setOperand(i, done);
}


/*
 * CTFP registration
 */
namespace {
	using namespace llvm;

	struct CTFP : public FunctionPass {
		static char ID;

		CTFP() : FunctionPass(ID) {
		}

		~CTFP() {
		}

		virtual bool runOnFunction(Function &func) {
			return ctfp_func(func);
		}
	};

	char CTFP::ID = 0;
	RegisterPass<CTFP> X("ctfp", "Constant Time Floating-Point");

	static void registerCTFP(const PassManagerBuilder &, legacy::PassManagerBase &PM) {
	    PM.add(new CTFP());
	}
	static RegisterStandardPasses RegisterCTFP(PassManagerBuilder::EP_OptimizerLast, registerCTFP);
}

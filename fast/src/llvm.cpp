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
void ctfp_replace(llvm::Instruction *inst, const char *id);

void ctfp_cleanup(llvm::Module& mod);


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

	llvm::Module *mod = func.getParent();
	if(mod->getFunction("ctfp_restrict_add_f32v4") == nullptr) {
		llvm::SMDiagnostic err;
		const char *dir = getenv("CTFP_DIR");
		if(dir == nullptr)
			//dir = "../redux";
			fprintf(stderr, "Missing 'CTFP_DIR' variable.\n"), abort();

		std::string path = std::string(dir) + std::string("/ctfp.bc");
		std::unique_ptr<llvm::Module> parse = llvm::parseIRFile(path, err, func.getContext());
		if(parse == nullptr)
			fprintf(stderr, "Failed to load CTFP bitcode (%s).\n", path.c_str()), abort();

		if(llvm::Linker::linkModules(*mod, std::move(parse)))
			fprintf(stderr, "Link failed.\n"), abort();
	}

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
	}

	for(llvm::BasicBlock &block : func)
		ctfp_block(block, pass);

	ctfp_cleanup(*func.getParent());

	return true;
}


/**
 * Cleanup the leftover CTFP functions.
 *   @mod: The module.
 */
void ctfp_cleanup(llvm::Module& mod)
{
	auto iter = mod.begin();

	while(iter != mod.end()) {
		llvm::Function *func = &*iter++;

		std::string name = func->getName().str();
		if(regex_match(name, std::regex("^ctfp_restrict_.*$")))
			func->eraseFromParent();
		else if(regex_match(name, std::regex("^ctfp_full_.*$")))
			func->eraseFromParent();
		else if(regex_match(name, std::regex("^ctfp_fast_.*$")))
			func->eraseFromParent();
	}
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

	while(iter != block.end()) {
		llvm::Instruction *inst = &*iter++;
		Info info = Pass::GetInfo(*inst);

		if(((info.op == Op::Add) || (info.op == Op::Sub)) && (info.type.kind == Kind::Flt) && (info.type.width == 32)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(addmin32)) {
				Range safe = pass.map[lhs].Protect(info.type, safemin32);
				ctfp_protect(inst, 0, safemin32);
				//printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(addmin32)) {
				Range safe = pass.map[rhs].Protect(info.type, safemin32);
				ctfp_protect(inst, 1, safemin32);
				//printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}
		else if(((info.op == Op::Add) || (info.op == Op::Sub)) && (info.type.kind == Kind::Flt) && (info.type.width == 64)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(addmin64)) {
				Range safe = pass.map[lhs].Protect(info.type, safemin64);
				ctfp_protect(inst, 0, safemin64);
				//printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(addmin64)) {
				Range safe = pass.map[rhs].Protect(info.type, safemin64);
				ctfp_protect(inst, 1, safemin64);
				//printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}
		else if((info.op == Op::Mul) && (info.type.kind == Kind::Flt) && (info.type.width == 32)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(mulmin32)) {
				Range safe = pass.map[lhs].Protect(info.type, safemin32);
				ctfp_protect(inst, 0, safemin32);
				//printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(mulmin32)) {
				Range safe = pass.map[rhs].Protect(info.type, safemin32);
				ctfp_protect(inst, 1, safemin32);
				//printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}
		else if((info.op == Op::Mul) && (info.type.kind == Kind::Flt) && (info.type.width == 64)) {
			llvm::Value *lhs = inst->getOperand(0);
			if(!pass.GetRange(lhs).IsSafe(mulmin64)) {
				Range safe = pass.map[lhs].Protect(info.type, safemin64);
				ctfp_protect(inst, 0, safemin64);
				//printf("Protect!\n");
				pass.map[inst->getOperand(0)] = safe;
			}

			llvm::Value *rhs = inst->getOperand(1);
			if(!pass.GetRange(rhs).IsSafe(mulmin64)) {
				Range safe = pass.map[rhs].Protect(info.type, safemin64);
				ctfp_protect(inst, 1, safemin64);
				//printf("Protect!\n");
				pass.map[inst->getOperand(1)] = safe;
			}
		}


		//pass.Proc(*inst);
		//pass.map[iter - 1] = pass.map[inst];

		const char *op = nullptr;

		switch(info.op) {
		case Op::Add: op = "add"; break;
		case Op::Sub: op = "sub"; break;
		case Op::Mul: op = "mul"; break;
		case Op::Div: op = "div"; break;
		case Op::Sqrt: op = "sqrt"; break;
		default: break;
		}

		if(op != nullptr) {
			llvm::Use *use = &*inst->use_begin();
			Range range = pass.map[inst];
			ctfp_replace(inst, (std::string("ctfp_fast_") + op + "_f" + std::to_string(info.type.width) + "v" + std::to_string(info.type.count)).data());
			pass.map[use->get()] = range;
		}

		if(0) {
			inst->print(llvm::outs());
			std::cout << "\n";

			auto fact = pass.map.find(inst);
			if(fact != pass.map.end())
				printf("    %s\n", fact->second.Str().data());
			else
				printf("    missing\n");
		}
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

using namespace llvm;

void ctfp_replace(Instruction *inst, const char *id) {
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
			llvm::Type *arg = func->getFunctionType()->getParamType(i);

			if(op->getType() == arg)
				args.push_back(op);
			else
				fprintf(stderr, "Mismatched types. %d %d %s\n", i, inst->getNumOperands(), inst->getOpcodeName()), op->getType()->dump(), fprintf(stderr, "::\n"), func->getFunctionType()->dump(), exit(1);
		}
	}
	else {
		for(unsigned int i = 0; i < inst->getNumOperands(); i++) {
			Value *op = inst->getOperand(i);
			llvm::Type *arg = func->getFunctionType()->getParamType(i);

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
			else if((op->getType() == VectorType::get(llvm::Type::getFloatTy(ctx), 2)) && arg->isDoubleTy()) {
				fprintf(stderr, "Error\n"), abort();
				CastInst *cast = CastInst::Create(Instruction::BitCast, op, llvm::Type::getDoubleTy(ctx));
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
	else if((inst->getType() == VectorType::get(llvm::Type::getFloatTy(ctx), 2)) && func->getReturnType()->isDoubleTy()) {
		fprintf(stderr, "Error\n"), abort();
		CastInst *cast = CastInst::Create(Instruction::BitCast, call, VectorType::get(llvm::Type::getFloatTy(ctx), 2));
		cast->insertBefore(inst);

		inst->replaceAllUsesWith(cast);
	}
	else
		fprintf(stderr, "Mismatched types.\n"), func->getReturnType()->dump(), inst->getType()->dump(), inst->dump(), exit(1);

	for(unsigned int i = 0; i < inst->getNumOperands(); i++) {
		Value *op = inst->getOperand(i);
		llvm::Type *arg = func->getFunctionType()->getParamType(i);
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

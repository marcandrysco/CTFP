#include "inc.hpp"


/*
 * Pass class
 */
class Pass {
public:
	Pass() { }
	~Pass() { }

	std::map<const llvm::Value *, Fact> map;

	Fact& Get(llvm::Value *value);

	void Dump(llvm::Function const& func) const;
};


/*
 * Fact class
 */
class Fact {
public:
	Range range;

	Fact() { range = RangeUndef(); }
	Fact(Range _range) { range = _range; }
	~Fact() { };

	bool HasSubnorm() const { return range.HasSubnorm(); }

	static Fact ItoF(Fact const& in, Type type);
	static Fact FtoI(Fact const& in, Type type);

	static Fact Add(Fact const& lhs, Fact const& rhs, Type type);
	static Fact Sub(Fact const& lhs, Fact const& rhs, Type type);
	static Fact Mul(Fact const& lhs, Fact const& rhs, Type type);

	static Fact And(Fact const& lhs, Fact const& rhs, Type type);
	static Fact Or(Fact const& lhs, Fact const& rhs, Type type);
	static Fact Xor(Fact const& lhs, Fact const& rhs, Type type);

	static Fact CmpOGT(Fact const& lhs, Fact const& rhs, Type type);

	static Fact Select(Fact const& cond, Fact const& lhs, Fact const& rhs, Type type);
};


/*
 * Instruction info class
 */
class Info {
public:
	Op op;
	Type type;

	Info(Op _op, Type _type) { op = _op; type = _type; }
};


/*
 * local declarations
 */
Info llvm_info(llvm::Instruction const& inst);
Type llvm_type(llvm::Value const& val);
Op llvm_op(llvm::Instruction const& inst);


/**
 * Optimize using basic interval arithmetic.
 *   @func: The function to optimize.
 */
void OptIval(llvm::Function &func) {
	Pass pass;

	uint32_t part = 0, full = 0, total = 0;
	FILE *fp = fopen("STATS", "r");
	if(fp != NULL) {
		if(fscanf(fp, "%u\n%u\n%u\n", &full, &part, &total) < 0);
		fclose(fp);
	}

	for(auto &arg : func.args()) {
		Range range;
		Type type = llvm_type(arg);

		switch(type.kind) {
		case Kind::Unk:
			range = Range(RangeUndef());
			break;

		case Kind::Int:
			if(type.width == 64)
				range = Range(RangeVecI64::All(type.count));

			break;

		case Kind::Flt:
			if(type.width == 64)
				range = Range(RangeVecF64::All(type.count));

			break;
		}

		pass.map[&arg] = Fact(Range(RangeF64::All()));
	}

	for(auto &block : func) {
		for(auto &inst : block) {
			Fact *in, *lhs, *rhs;
			Info info = llvm_info(inst);

			switch(info.op) {
			case Op::Add:
				lhs = &pass.Get(inst.getOperand(0));
				rhs = &pass.Get(inst.getOperand(1));
				pass.map[&inst] = Fact::Add(*lhs, *rhs, info.type);

				if(!lhs->HasSubnorm() && !rhs->HasSubnorm() && !pass.map[&inst].HasSubnorm()) full++;
				if(!lhs->HasSubnorm() || !rhs->HasSubnorm()) part++;
				total++;

				break;

			case Op::Sub:
				lhs = &pass.Get(inst.getOperand(0));
				rhs = &pass.Get(inst.getOperand(1));
				pass.map[&inst] = Fact::Sub(*lhs, *rhs, info.type);

				if(!lhs->HasSubnorm() && !rhs->HasSubnorm() && !pass.map[&inst].HasSubnorm()) full++;
				if(!lhs->HasSubnorm() || !rhs->HasSubnorm()) part++;
				total++;

				break;

			case Op::Mul:
				lhs = &pass.Get(inst.getOperand(0));
				rhs = &pass.Get(inst.getOperand(1));
				pass.map[&inst] = Fact::Mul(*lhs, *rhs, info.type);

				if(!lhs->HasSubnorm() && !rhs->HasSubnorm() && !pass.map[&inst].HasSubnorm()) full++;
				if(!lhs->HasSubnorm() || !rhs->HasSubnorm()) part++;
				total++;

				break;

			case Op::And:
				pass.map[&inst] = Fact::And(pass.Get(inst.getOperand(0)), pass.Get(inst.getOperand(1)), info.type);
				break;

			case Op::Or:
				pass.map[&inst] = Fact::Or(pass.Get(inst.getOperand(0)), pass.Get(inst.getOperand(1)), info.type);
				break;

			case Op::Xor:
				pass.map[&inst] = Fact::Xor(pass.Get(inst.getOperand(0)), pass.Get(inst.getOperand(1)), info.type);
				break;

			case Op::CmpOGT:
				pass.map[&inst] = Fact::CmpOGT(pass.Get(inst.getOperand(0)), pass.Get(inst.getOperand(1)), info.type);
				break;

			case Op::Select:
				pass.map[&inst] = Fact::Select(pass.Get(inst.getOperand(0)), pass.Get(inst.getOperand(1)), pass.Get(inst.getOperand(2)), info.type);
				break;

			case Op::ItoF:
				in = &pass.Get(inst.getOperand(0));
				pass.map[&inst] = Fact::ItoF(*in, info.type);
				break;

			case Op::FtoI:
				in = &pass.Get(inst.getOperand(0));
				pass.map[&inst] = Fact::FtoI(*in, info.type);
				break;

			default:
				break;
			}
		}
	}

	fp = fopen("STATS", "w");
	if(fp != NULL) {
		fprintf(fp, "%u\n%u\n%u\n", full, part, total);
		fclose(fp);
	}

	//printf("STATS %s: %u/%u/%u\n", func.getName().data(), full, part, total);
	pass.Dump(func);
}


/**
 * Retrieve the operation info for an instruction.
 *   @inst: The instruction.
 *   &returns: The info.
 */
Info llvm_info(llvm::Instruction const& inst) {
	Op op = llvm_op(inst);

	if((inst.getOpcode() == llvm::Instruction::ICmp) || (inst.getOpcode() == llvm::Instruction::FCmp))
		return Info(op, llvm_type(*inst.getOperand(0)));
	else if(inst.getOpcode() == llvm::Instruction::Select)
		return Info(op, llvm_type(*inst.getOperand(1)));
	else if(op != Op::Unk)
		return Info(op, llvm_type(inst));
	else
		return Info(op, Type());
}

/**
 * Retrieve the type for a value.
 *   @inst: The instruction.
 *   &returns: The operation.
 */
Type llvm_type(llvm::Value const& val) {
	if(val.getType()->isFloatTy())
		return Type(Kind::Flt, 32);
	else if(val.getType()->isDoubleTy())
		return Type(Kind::Flt, 64);
	else
		return Type();
}

/**
 * Retrieve the operation for an instruction.
 *   @inst: The instruction.
 *   &returns: The operation.
 */
Op llvm_op(llvm::Instruction const& inst) {
	switch(inst.getOpcode()) {
	case llvm::Instruction::FAdd:
		return Op::Add;

	case llvm::Instruction::FSub:
		return Op::Sub;

	case llvm::Instruction::FMul:
		return Op::Mul;

	case llvm::Instruction::And:
		return Op::And;

	case llvm::Instruction::Or:
		return Op::Or;

	case llvm::Instruction::Xor:
		return Op::Xor;

	case llvm::Instruction::Select:
		return Op::Select;

	case llvm::Instruction::BitCast:
		if(inst.getType()->isIntegerTy(64) && inst.getOperand(0)->getType()->isDoubleTy())
			return Op::FtoI;
		else if(inst.getType()->isDoubleTy() && inst.getOperand(0)->getType()->isIntegerTy(64))
			return Op::ItoF;
		else
			return Op::Unk;

	case llvm::Instruction::FCmp:
		switch(llvm::cast<llvm::FCmpInst>(&inst)->getPredicate()) {
		case llvm::CmpInst::FCMP_OLT: return Op::CmpOLT; break;
		case llvm::CmpInst::FCMP_OGT: return Op::CmpOGT; break;
		default: return Op::Unk;
		}

	default:
		return Op::Unk;
	}
}

struct CtfpOpt : public llvm::FunctionPass {
	static char ID;
	CtfpOpt() : llvm::FunctionPass(ID) {}

	bool runOnFunction(llvm::Function &func) override {
		OptIval(func);
		return false;
	}
};

char CtfpOpt::ID = 0;
static llvm::RegisterPass<CtfpOpt> X("ctfp-opt", "CtfpOpt", false, false);

#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>

static void registerCTFP2(const llvm::PassManagerBuilder &, llvm::legacy::PassManagerBase &PM) {
    PM.add(new CtfpOpt());
}
static llvm::RegisterStandardPasses RegisterCTFP(llvm::PassManagerBuilder::EP_OptimizerLast, registerCTFP2);


/** Pass Class **/

/**
 * Dump the set of facts from a function.
 */
void Pass::Dump(llvm::Function const& func) const {
	for(auto &block : func) {
		std::cout << block.getName().data() << ":\n";
		for(auto &inst : block) {
			inst.print(llvm::outs());
			std::cout << "\n";

			auto fact = map.find(&inst);
			if(fact != map.end())
				printf("    %s\n", fact->second.range.Str().data());
			else
				printf("    missing\n");
		}
	}
}

/**
 * Given a value, retrieve the associated fact.
 *   @value: The value.
 *   &returns: The fact.
 */
Fact& Pass::Get(llvm::Value *value) {
	auto find = map.find(value);
	if(find != map.end())
		return find->second;

	if(llvm::isa<llvm::ConstantFP>(value)) {
		llvm::ConstantFP *fp = llvm::cast<llvm::ConstantFP>(value);

		if(value->getType()->isFloatTy())
			map[value] = Fact(); //TODO
		else if(value->getType()->isDoubleTy())
			map[value] = Range::ConstF64(fp->getValueAPF().convertToDouble());
		else
			map[value] = Fact(); //TODO

		return map[value];
	}
	else if(llvm::isa<llvm::ConstantInt>(value)) {
		llvm::ConstantInt *ival = llvm::cast<llvm::ConstantInt>(value);

		if(value->getType()->isIntegerTy(32))
			map[value] = Fact(); //TODO
		else if(value->getType()->isIntegerTy(64))
			map[value] = Range::ConstI64(ival->getZExtValue());
		else
			map[value] = Fact(); //TODO

		return map[value];
	}
	else
		return map[value] = Fact();
}


/** Fact Class **/

/**
 * Cast an integer to float.
 *   @in: The input.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::ItoF(Fact const& in, Type type) {
	return Fact(Range::ItoF(in.range, type));
}

/**
 * Cast a float to integer.
 *   @in: The input.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::FtoI(Fact const& in, Type type) {
	return Fact(Range::FtoI(in.range, type));
}

/**
 * Add two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Add(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::Add(lhs.range, rhs.range, type));
}

/**
 * Subtract two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Sub(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::Sub(lhs.range, rhs.range, type));
}

/**
 * Multiply two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Mul(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::Mul(lhs.range, rhs.range, type));
}


/**
 * And two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::And(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::And(lhs.range, rhs.range, type));
}

/**
 * Or two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Or(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::Or(lhs.range, rhs.range, type));
}

/**
 * Xor two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Xor(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::Xor(lhs.range, rhs.range, type));
}


/**
 * Comparison (OGT) on two facts.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::CmpOGT(Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::CmpOGT(lhs.range, rhs.range, type));
}


/**
 * Select values base on a condition.
 *   @cond: The condition.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Select(Fact const& cond, Fact const& lhs, Fact const& rhs, Type type) {
	return Fact(Range::Select(cond.range, lhs.range, rhs.range, type));
}

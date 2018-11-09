#include "inc.hpp"


/*
 * Pass class
 */
class Pass {
public:
	Pass() { }
	~Pass() { }

	std::map<const llvm::Value *, Fact> map;

	void Dump(llvm::Function const &func) const;
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

	static Fact Add(Fact const &lhs, Fact const &rhs, Type type);
	static Fact Sub(Fact const &lhs, Fact const &rhs, Type type);
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
				range = Range(RangeVecI64::All(type.count));

			break;
		}

		pass.map[&arg] = Fact(Range(RangeF64::All()));
	}

	for(auto &block : func) {
		for(auto &inst : block) {
			Info info = llvm_info(inst);

			switch(info.op) {
			case Op::Add:
				pass.map[&inst] = Fact::Add(pass.map[inst.getOperand(0)], pass.map[inst.getOperand(1)], info.type);
				break;

			case Op::Sub:
				pass.map[&inst] = Fact::Sub(pass.map[inst.getOperand(0)], pass.map[inst.getOperand(1)], info.type);
				break;

			default:
				break;
			}
		}
	}

	pass.Dump(func);
}


/**
 * Retrieve the operation info for an instruction.
 *   @inst: The instruction.
 *   &returns: The info.
 */
Info llvm_info(llvm::Instruction const& inst) {
	return Info(llvm_op(inst), llvm_type(*inst.getOperand(0)));
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
	case llvm::Instruction::FAdd: return Op::Add;
	case llvm::Instruction::FSub: return Op::Sub;
	default: return Op::Unk;
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


/** Pass Class **/

/**
 * Dump the set of facts from a function.
 */
void Pass::Dump(llvm::Function const &func) const {
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


/** Fact Class **/

/**
 * Add two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Add(Fact const &lhs, Fact const &rhs, Type type) {
	return Fact(Range::Add(lhs.range, rhs.range, type));
}

/**
 * Subtract two facts together.
 *   @lhs: The left-hand side.
 *   @rhs: The right-hand side.
 *   @type: The type.
 *   &returns: The result fact.
 */
Fact Fact::Sub(Fact const &lhs, Fact const &rhs, Type type) {
	return Fact(Range::Sub(lhs.range, rhs.range, type));
}

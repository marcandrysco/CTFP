#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>

#include "inc.hpp"


/*
 * local declarations
 */
static llvm::LLVMContext llvm_ctx;

static std::unique_ptr<llvm::Module> llvm_load(const char *path);


/**
 * Main entry function.
 *   @argc: The number of arguments.
 *   @argv: The argument array.
 *   &returns: The code.
 */
int main(int argc, char **argv)
{
	setbuf(stdout, NULL);
	setbuf(stderr, NULL);

	//printf("%s\n", IvalF64::Mul(IvalF64(-0, -INFINITY), IvalF64(-1, -DBL_MIN)).Str().c_str());
	//printf("max: %e\n", f64min(-1, -INFINITY));
	//return 0;

	std::unique_ptr<llvm::Module> mod = llvm_load("test2.ll");
	for(auto func = mod->begin(); func != mod->end(); func++) {
		int idx = 0;

		if(func->size() != 1)
			continue;

		for(auto &block : *func) {
			for(auto &inst : block) {
				if(!inst.hasName())
					inst.setName("v" + std::to_string(idx++));
			}
		}

		Pass pass;
		pass.Run(*func, std::vector<Range>{ Range(RangeF64::Normal()), Range(RangeF64::Normal()) });
		pass.Dump(*func);

		break;
	}

	return 0;
}


/**
 * Load a module from a path.
 *   @path: The path.
 *   &returns: The module.
 */
static std::unique_ptr<llvm::Module> llvm_load(const char *path)
{
	llvm::SMDiagnostic err;
	std::unique_ptr<llvm::Module> mod;

	mod = parseIRFile(path, err, llvm_ctx);
	if(mod == nullptr) {
		llvm::raw_fd_ostream stream(STDERR_FILENO, false);
		err.print("llvm", stream);
		fatal("Cannot open '%s'. %s", path, err.getMessage().data());
	}

	return mod;
}

/**
 * Retrieve the string name.
 *   @value: The value.
 *   &returns: The string.
 */
std::string llvm_name(llvm::Value const *value)
{
	return value->getName().data();
}


/**
 * Print a fatal error and terminate.
 *   @file: The file.
 *   @line: The line.
 *   @fmt: The format string.
 *   @...: The printf-style arguments.
 *   &noreturn
 */
void dbg_fatal(const char *file, unsigned long line, const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	fprintf(stderr, "%s:%lu: ", file, line);
	vfprintf(stderr, fmt, args);
	fprintf(stderr, "\n");
	va_end(args);

	abort();
}


/** Pass class **/

/**
 * Run the pass on a function.
 *   @func: The function.
 *   @args: The initial arguments.
 */
void Pass::Run(const llvm::Function &func, std::vector<Range> const &args) {
	int i = 0;
	for(auto const &arg : func.args())
		map[&arg] = Fact(Op::ConstF64, std::vector<Fact *>{}, args[i++]);

	for(auto const &inst : func.front()) {
		Inst(inst);
		printf("----------------\n");
		Dump(func);
	}
}

/**
 * Process a single instruction.
 *   @inst: The instruction.
 */
void Pass::Inst(const llvm::Instruction &inst) {
	auto info = Info(inst);

	switch(info.first) {
	case Op::None:
		break;

	case Op::AbsF64:
		map[&inst] = Fact::AbsF64(*info.second[0]);
		break;

	case Op::CmpOltF64:
		map[&inst] = Fact::CmpOltF64(*info.second[0], *info.second[1], &inst);
		break;

	case Op::CmpOgtF64:
		map[&inst] = Fact::CmpOgtF64(*info.second[0], *info.second[1], &inst);
		break;

	case Op::CopySignF64:
		map[&inst] = Fact::CopySignF64(*info.second[0], *info.second[1]);
		break;

	case Op::AddF64:
		map[&inst] = Fact::AddF64(*info.second[0], *info.second[1], &inst);
		break;

	case Op::SubF64:
		map[&inst] = Fact::SubF64(*info.second[0], *info.second[1], &inst);
		break;

	case Op::MulF64:
		map[&inst] = Fact::MulF64(*info.second[0], *info.second[1], &inst);
		break;

	case Op::AndI64:
		map[&inst] = Fact::AndI64(*info.second[0], *info.second[1]);
		break;

	case Op::XorI64:
		map[&inst] = Fact::XorI64(*info.second[0], *info.second[1]);
		break;

	case Op::SelectI64:
		map[&inst] = Fact::SelectI64(*info.second[0], *info.second[1], *info.second[2]);
		break;

	case Op::CastF64toI64:
		map[&inst] = Fact::CastF64toI64(*info.second[0]);
		break;

	case Op::CastI64toF64:
		map[&inst] = Fact::CastI64toF64(*info.second[0]);
		break;

	default:
		fatal("stub");
	}
}

/**
 * Dump a function with its facts.
 *   @func: The function.
 */
void Pass::Dump(const llvm::Function &func) const {
	for(auto const &arg : func.args()) {
		arg.print(llvm::outs(), false);
		printf("\n");

		if(map.find(&arg) != map.end())
			map.find(&arg)->second.Dump();
	}

	for(auto const &inst : func.front()) {
		inst.print(llvm::outs(), false);
		printf("\n");

		if(map.find(&inst) != map.end())
			map.find(&inst)->second.Dump();
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

		if(value->getType()->isFloatTy()) {
			fatal("stub"); // float val = 
		}
		else if(value->getType()->isDoubleTy())
			map[value] = Fact(Op::ConstF64, std::vector<Fact *>{}, RangeF64::Const(fp->getValueAPF().convertToDouble()));
		else
			fatal("Unknown type.");

		return map[value];
	}
	else if(llvm::isa<llvm::ConstantInt>(value)) {
		llvm::ConstantInt *ival = llvm::cast<llvm::ConstantInt>(value);

		if(value->getType()->isIntegerTy(32))
			fatal("stub"); // float val = 
		else if(value->getType()->isIntegerTy(64))
			map[value] = Fact(Op::ConstI64, std::vector<Fact *>{}, RangeI64::Const(ival->getZExtValue()));
		else
			fatal("Unknown type.");

		return map[value];
	}

	fatal("Cannot retrieve fact for parameter.");
}

/**
 * For an instruction, retrieve the operation and arguments vector.
 *   @inst: The instruction.
 *   &returns: The operation and argument pair.
 */
std::pair<Op, std::vector<Fact *>> Pass::Info(const llvm::Instruction &inst) {
	static std::vector<std::pair<const char *, Op>> funcs = {
		{ "llvm.fabs.f32", Op::AbsF32 },
		{ "llvm.fabs.f64", Op::AbsF64 },
		{ "llvm.copysign.f32", Op::CopySignF32 },
		{ "llvm.copysign.f64", Op::CopySignF64 },
	};

	Op op;
	std::vector<Fact *> args;

	bool dbl = inst.getOperand(0)->getType()->isDoubleTy() || inst.getOperand(0)->getType()->isIntegerTy(64);

	unsigned int nargs = inst.getNumOperands();
	if(inst.getOpcode() == llvm::Instruction::Call)
		nargs--;

	for(unsigned int i = 0; i < nargs; i++)
		args.push_back(&Get(inst.getOperand(i)));
	
	switch(inst.getOpcode()) {
	case llvm::Instruction::BitCast:
		if(inst.getOperand(0)->getType()->isIntegerTy(64) && inst.getType()->isDoubleTy())
			op = Op::CastI64toF64;
		else if(inst.getOperand(0)->getType()->isDoubleTy() && inst.getType()->isIntegerTy(64))
			op = Op::CastF64toI64;
		else
			fatal("Unhandled cast.");

		break;

	case llvm::Instruction::FAdd:
		op = (dbl ? Op::AddF64 : Op::AddF32);
		break;

	case llvm::Instruction::FSub:
		op = (dbl ? Op::SubF64 : Op::SubF32);
		break;

	case llvm::Instruction::FMul:
		op = (dbl ? Op::MulF64 : Op::MulF32);
		break;

	case llvm::Instruction::And: op = (dbl ? Op::AndI64 : Op::AndI32); break;
	case llvm::Instruction::Xor: op = (dbl ? Op::XorI64 : Op::XorI32); break;
	case llvm::Instruction::FCmp:
		{
			const llvm::FCmpInst *fcmp = llvm::cast<llvm::FCmpInst>(&inst);

			switch(fcmp->getPredicate()) {
			case llvm::CmpInst::FCMP_OLT: op = (dbl ? Op::CmpOltF64 : Op::CmpOltF32); break;
			case llvm::CmpInst::FCMP_OGT: op = (dbl ? Op::CmpOgtF64 : Op::CmpOgtF32); break;
			default: fatal("Unhandled predicate.");
			}
		}
		break;

	case llvm::Instruction::Call:
		{
			const llvm::CallInst *call = llvm::cast<llvm::CallInst>(&inst);
			std::string id = call->getCalledFunction()->getName().str();

			auto find = std::find_if(funcs.begin(), funcs.end(), [id](std::pair<const char *,Op> &val) -> bool { return id == val.first; });
			if(find == std::end(funcs))
				fatal("Unknown function '%s'.", id.c_str());

			op = find->second;
		}
		break;

	case llvm::Instruction::Select:
		if(inst.getType()->isIntegerTy(32))
			op = Op::SelectI32;
		else if(inst.getType()->isIntegerTy(64))
			op = Op::SelectI64;
		else
			fatal("Select on unhandled type.");

		break;

	default:
		fatal("stub");
	}

	return std::pair<Op, std::vector<Fact *>>(op, args);
}

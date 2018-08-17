#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>

#include "inc.hpp"


/*
 * local declarations
 */
static llvm::LLVMContext llvm_ctx;

static std::unique_ptr<llvm::Module> llvm_load(const char *path);
int llvm_info(llvm::Instruction &inst, std::vector<llvm::Value *> &args);


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

	std::unique_ptr<llvm::Module> mod = llvm_load("test.ll");
	for(auto func = mod->begin(); func != mod->end(); func++) {
		if(func->size() != 1)
			continue;

		Pass pass(&*func);

		pass.Run();
		//pass.Dump();
		break;
		//go(*func);
	}

	//double v = -INFINITY;
	//uint64_t u;
	//memcpy(&u, &v, 8);
	//printf("hi! %016lx\n", u);

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
 * Run the pass.
 */
void Pass::Run() {
	unsigned int idx = 1;

	for(auto &arg : func->args())
		map[&arg] = Fact(Fact::FConst, Range64::All());

	for(auto &inst : func->front()) {
		if(!inst.hasName())
			inst.setName("v" + std::to_string(idx++));

		auto info = Info(inst);

		switch(info.first) {
		case Fact::Mov:
			Add(&inst, *info.second[0]);
			break;

		case Fact::FConst:
		case Fact::IConst:
			fatal("Invalid instruction type.");

		case Fact::IAnd32: fatal("stub"); break;
		case Fact::IXor32: fatal("stub"); break;
		case Fact::FAdd32: fatal("stub"); break;
		case Fact::FAbs32: fatal("stub"); break;
		case Fact::CopySign32: fatal("stub"); break;

		case Fact::IAnd64:
			Add(&inst, Fact::IntAnd64(*info.second[0], *info.second[1]));
			break;

		case Fact::IXor64:
			Add(&inst, Fact::IntXor64(*info.second[0], *info.second[1]));
			break;

		case Fact::FAdd64: 
			Add(&inst, Fact::FltAdd64(*info.second[0], *info.second[1]));
			Dump();
			printf("here!\n");
			exit(0);
			break;

		case Fact::FAbs64:
			Add(&inst, Fact::FltAbs64(*info.second[0]));
			break;

		case Fact::FOlt32:
			fatal("stub");

		case Fact::FOlt64:
			Dump();
			Add(&inst, Fact::FltOLT64(*info.second[0], *info.second[1], &inst));
			break;

		case Fact::CopySign64:
			Add(&inst, Fact::FltCopySign64(*info.second[0], *info.second[1]));
			break;

		case Fact::Sel:
			Add(&inst, Fact::Select(*info.second[0], *info.second[1], *info.second[2], &inst));
			break;
		}

		if(info.first == Fact::FOlt64) {
		}
	}
}

/**
 * Add a value-fact pair to the pass.
 *   @value: The value.
 *   @fact: The fact.
 */
void Pass::Add(llvm::Value *value, const Fact &fact) {
	map[value] = fact;
}



/**
 * Given a value, retrieve the associated fact.
 *   @value: The value.
 *   &returns: The fact.
 */
Fact &Pass::Get(llvm::Value *value) {
	auto find = map.find(value);
	if(find != map.end())
		return find->second;

	if(llvm::isa<llvm::ConstantFP>(value)) {
		llvm::ConstantFP *fp = llvm::cast<llvm::ConstantFP>(value);

		if(value->getType()->isFloatTy()) {
			fatal("stub"); // float val = 
		}
		else if(value->getType()->isDoubleTy())
			map[value] = Fact(Fact::FConst, Range64::Const(fp->getValueAPF().convertToDouble()));
		else
			fatal("Unknown type.");

		return map[value];
	}
	else if(llvm::isa<llvm::ConstantInt>(value)) {
		llvm::ConstantInt *ival= llvm::cast<llvm::ConstantInt>(value);

		if(value->getType()->isIntegerTy(32))
			fatal("stub"); // float val = 
		else if(value->getType()->isIntegerTy(64)) {
			map[value] = Fact(Fact::IConst, Range64::Int(ival->getZExtValue()));
		}
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
std::pair<Fact::Op, std::vector<Fact *>> Pass::Info(llvm::Instruction &inst) {
	static std::vector<std::pair<const char *,Fact::Op>> funcs = {
		{ "llvm.fabs.f32", Fact::FAbs32 },
		{ "llvm.fabs.f64", Fact::FAbs64 },
		{ "llvm.copysign.f32", Fact::CopySign32 },
		{ "llvm.copysign.f64", Fact::CopySign64 },
	};

	Fact::Op op;
	std::vector<Fact *> args;

	bool dbl = inst.getOperand(0)->getType()->isDoubleTy() || inst.getOperand(0)->getType()->isIntegerTy(64);

	unsigned int nargs = inst.getNumOperands();
	if(inst.getOpcode() == llvm::Instruction::Call)
		nargs--;

	for(unsigned int i = 0; i < nargs; i++)
		args.push_back(&Get(inst.getOperand(i)));
	
	switch(inst.getOpcode()) {
	case llvm::Instruction::BitCast: op = Fact::Mov; break;
	case llvm::Instruction::And: op = (dbl ? Fact::IAnd64 : Fact::IAnd32); break;
	case llvm::Instruction::Xor: op = (dbl ? Fact::IXor64 : Fact::IXor32); break;
	case llvm::Instruction::FAdd: op = (dbl ? Fact::FAdd64 : Fact::FAdd32); break;
	case llvm::Instruction::FCmp:
		{
			llvm::FCmpInst *fcmp = llvm::cast<llvm::FCmpInst>(&inst);

			switch(fcmp->getPredicate()) {
			case llvm::CmpInst::FCMP_OLT: op = (dbl ? Fact::FOlt64 : Fact::FOlt32); break;
			default: fatal("Unhandled predicate.");
			}
		}
		break;

	case llvm::Instruction::Call:
		{
			llvm::CallInst *call = llvm::cast<llvm::CallInst>(&inst);
			std::string id = call->getCalledFunction()->getName().str();

			auto find = std::find_if(funcs.begin(), funcs.end(), [id](std::pair<const char *,Fact::Op> &val) -> bool { return id == val.first; });
			if(find == std::end(funcs))
				fatal("Unknown function '%s'.", id.c_str());

			op = find->second;
		}
		break;

	case llvm::Instruction::Select:
		op = Fact::Sel;
		break;
	}

	return std::pair<Fact::Op, std::vector<Fact *>>(op, args);

}


/**
 * Dump the pass information to stdout.
 */
void Pass::Dump() const {
	for(auto &arg : func->args()) {
		arg.print(llvm::outs(), false);
		printf("\n");

		if(map.find(&arg) != map.end())
			map.find(&arg)->second.Dump();
	}

	for(auto &inst : func->front()) {
		inst.print(llvm::outs(), false);
		printf("\n");

		if(map.find(&inst) != map.end())
			map.find(&inst)->second.Dump();
	}
}


/**
 * Retrieve the string name.
 *   @value: The value.
 *   &returns: The string.
 */
std::string llvm_name(llvm::Value *value)
{
	return value->getName().data();
}

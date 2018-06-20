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
 * Retrieve a fact from a value.
 *   @value: The value.
 *   @map: The value to fact map.
 *   &returns: The fact.
 */
Fact &getfact(llvm::Value *value, std::map<llvm::Value *,Fact> &map) {
	auto find = map.find(value);
	if(find != map.end())
		return find->second;

	if(llvm::isa<llvm::ConstantFP>(value)) {
		llvm::ConstantFP *fp = llvm::cast<llvm::ConstantFP>(value);

		if(value->getType()->isFloatTy()) {
			fatal("stub"); // float val = 
		}
		else if(value->getType()->isDoubleTy())
			map[value] = Fact(Range64::Const(fp->getValueAPF().convertToDouble()));
		else
			fatal("Unknown type.");

		return map[value];
	}

	fatal("Cannot retrieve fact for parameter.");
}

/*
 * instruction type definitions
 */
#define MSK64   (0x0100)
#define FADD32  (0x0001)
#define FSUB32  (0x0002)
#define FABS32  (0x0008)
#define FOLT32  (0x0010)
#define FADD64  (FADD32 | MSK64)
#define FSUB64  (FSUB32 | MSK64)
#define FABS64  (FABS32 | MSK64)
#define FOLT64  (FOLT32 | MSK64)

/*
 * list of handled functions
 */
static std::vector<std::pair<const char *,int>> funcs = {
	{ "llvm.fabs.f32", FABS32 },
	{ "llvm.fabs.f64", FABS64 }
};


void olt(const Fact &lhs, const Fact &rhs)
{
	printf("really olt\n");
	exit(0);
}

void go(llvm::Function &func)
{
	class Pass pass(&func);

	assert(func.size() == 1);

	std::map<llvm::Value *,Fact> map;
	printf("func: %s\n", func.getName().data());

	for(auto arg = func.arg_begin(); arg != func.arg_end(); arg++) {
		map[&*arg] = Fact(Range64::All());
	}

	llvm::BasicBlock &block = func.front();
	for(auto inst = block.begin(); inst != block.end(); inst++) {
		Fact out;
		std::vector<llvm::Value *> args;
		int code = llvm_info(*inst, args);

		inst->print(llvm::outs(), false); printf("\n");

		switch(code) {
		case FADD32:
		case FSUB32:
		case FABS32:
		case FOLT32:
		case FADD64:
		case FSUB64:
			//printf("%s\n", map[args[0]];
			printf("stub!!!");
			exit(0);

		case FABS64:
			out = Fact::FltAbs64(getfact(args[0], map));
			map[&*inst] = out;
			break;

		case FOLT64:
			out = Fact::FltOLT64(getfact(args[0], map), getfact(args[1], map), &*inst);

			printf("------\n");
			for(auto &iter : block) {
				//for(auto iter = block.begin(); iter != block.end(); iter++) {
				iter.print(llvm::outs(), false); printf("\n");
				printf("%s", map[&iter].Str().c_str());
				if(&iter == &*inst) break;
			}

			printf("ok");
			exit(0);
			map[&*inst] = out;
			break;

		default:
			fatal("Unknown code.");
		}

		printf("    %s\n", out.Str().c_str());
	}
}

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
 * Retrieve the required information about an instruction.
 *   @inst: The instruction.
 *   @args: The argument vector.
 *   &returns: The instruction code.
 */
int llvm_info(llvm::Instruction &inst, std::vector<llvm::Value *> &args)
{
	int mask = inst.getOperand(0)->getType()->isDoubleTy() ? MSK64 : 0;
	unsigned int i, nargs = inst.getNumOperands();

	if(inst.getOpcode() == llvm::Instruction::Call)
		nargs--;

	for(i = 0; i < nargs; i++)
		args.push_back(inst.getOperand(i));

	switch(inst.getOpcode()) {
	case llvm::Instruction::FAdd: return FADD32 | mask;
	case llvm::Instruction::FSub: return FSUB32 | mask;
	case llvm::Instruction::FCmp:
		{
			llvm::FCmpInst *fcmp = llvm::cast<llvm::FCmpInst>(&inst);

			switch(fcmp->getPredicate()) {
			case llvm::CmpInst::FCMP_OLT: return FOLT32 | mask;
			default: fatal("Unhandled predicate.");
			}
		}

	case llvm::Instruction::Call:
		{
			llvm::CallInst *call = llvm::cast<llvm::CallInst>(&inst);
			std::string id = call->getCalledFunction()->getName().str();

			auto find = std::find_if(funcs.begin(), funcs.end(), [id](std::pair<const char *,int> &val) -> bool { return id == val.first; });
			if(find == std::end(funcs))
				fatal("Unknown function '%s'.", id.c_str());

			return find->second;
		}

	default:
		fatal("stub");
	}

	return -1;
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
		map[&arg] = Fact(Range64::All());

	for(auto &inst : func->front()) {
		if(!inst.hasName())
			inst.setName("v" + idx);

		Fact out;
		std::vector<llvm::Value *> args;
		int code = llvm_info(inst, args);

		switch(code) {
		case FADD32:
		case FSUB32:
		case FABS32:
		case FOLT32:
		case FADD64:
		case FSUB64:
			printf("stub!!!");
			exit(0);

		case FABS64:
			out = Fact::FltAbs64(getfact(args[0], map));
			break;

		case FOLT64:
			out = Fact::FltOLT64(getfact(args[0], map), getfact(args[1], map), &inst);

			Dump();
			exit(0);
			break;

		default:
			fatal("Unknown code.");
		}

		map[&inst] = out;
	}
}

/**
 * Add a value-fact pair to the pass.
 *   @value: The value.
 *   @fact: The fact.
 */
void Pass::Add(llvm::Value *value, Fact &fact) {
	map[value] = fact;
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

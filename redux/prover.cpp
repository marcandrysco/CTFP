#include <stdarg.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

#include <map>
#include <vector>

#include <z3.h>


/*
 * local declarations
 */
static llvm::LLVMContext llvm_ctx;
static Z3_context z3;
static Z3_solver solver;

static std::unique_ptr<llvm::Module> llvm_load(const char *fmt, ...);

#define getstr(v) (llvm_str(v).c_str())

static void fatal(const char *str, ...);


std::string llvm_str(llvm::Value *value)
{
	if(llvm::isa<llvm::ConstantInt>(value)) {
		llvm::ConstantInt *ival = llvm::cast<llvm::ConstantInt>(value);
		uint32_t bits = ival->getZExtValue();

		char buf[32];
		sprintf(buf, "#x%08x", bits);

		return std::string(buf);
	}
	else if(llvm::isa<llvm::ConstantFP>(value)) {
		llvm::ConstantFP *fp = llvm::cast<llvm::ConstantFP>(value);

		float val = fp->getValueAPF().convertToFloat();
		uint32_t bits;
		memcpy(&bits, &val, 4);

		char buf[32];
		sprintf(buf, "#x%08x", bits);

		return std::string(buf);
	}
	else
		return value->getName().str();
}

void z3_eq(Z3_ast a, Z3_ast b)
{
	Z3_solver_assert(z3, solver, Z3_mk_fpa_eq(z3, a, Z3_mk_fpa_abs(z3, b)));
}

const char *prelude =
	"(set-logic QF_FPBV)\n"
	"\n"
	"(define-sort Int32 () (_ BitVec 32))\n"
	"(define-sort Int64 () (_ BitVec 64))\n"
	"\n"
	"(define-fun to_fp_32 ((a Int32)) Float32\n"
	"	((_ to_fp 8 24) a)\n"
	")\n"
	"\n"
	"(define-fun fp_copysign_f32 ((a Float32) (b Float32)) Float32\n"
  	"	(to_fp_32 (bvor\n"
	"		(bvand (to_ieee_bv a) #x7fffffff)\n"
	"		(bvand (to_ieee_bv b) #x80000000))\n"
	"	)\n"
	")\n"
	"\n"
	;


void gofile(const char *path)
{
	FILE *pipe;
	char buf[256];

	std::string cmd = std::string("z3 ") + path;
	pipe = popen(cmd.c_str(), "r");

	fgets(buf, sizeof(buf), pipe);
	if(strcmp(buf, "sat\n") == 0) {
		printf("sat\n");
		while(fgets(buf, sizeof(buf), pipe))
			fputs(buf, stdout);
	}
	else if(strcmp(buf, "unsat\n") == 0) {
		printf("verified\n");
	}
	else {
		printf("error\n");
		while(fgets(buf, sizeof(buf), pipe))
			fputs(buf, stdout);
	}

	fclose(pipe);
}

/**
 * Main entry point.
 */
int main()
{
	setbuf(stdout, NULL);
	setbuf(stderr, NULL);

	std::unique_ptr<llvm::Module> mod = llvm_load("foo.ll");



	for(auto func = mod->begin(); func != mod->end(); func++) {
		/* there is no function body, skip */
		if(func->size() == 0)
			continue;

		/* all ctfp functions must be one basic block */
		std::string fn = func->getName().str();
		if(func->size() != 1)
			fatal("Function '%s' has more than one basic block.", fn.c_str());

		llvm::MDNode *node = func->getMetadata(fn);
		if(node == nullptr)
			fatal("Function '%s' missing metadata.");

		if(node->getNumOperands() != 2)
			fatal("Function '%s' must have a pre- and post- condition.");

		printf("%p : %d\n", node, node->getNumOperands());
		for(auto op = node->op_begin(); op != node->op_end(); op++) {
			llvm::MDString *str = llvm::dyn_cast<llvm::MDString>(op->get());
			if(0)printf(":: %s\n", str->getString().str().c_str());
		}
		//func->getMetadata();
		//llvm::dyn_cast<llvm::ValueAsMetadata>(&*func);
		printf("fn: %s\n", fn.c_str());
	
		/* write to the target smt2 file */
		std::string path = fn + std::string(".smt2");
		FILE *file = fopen(path.c_str(), "w");
		assert(file != nullptr);

		fprintf(file, "%s\n", prelude);

		/* write arguments as constants */
		auto block = func->begin();
		for(auto arg = func->arg_begin(); arg != func->arg_end(); arg++)
			fprintf(file, "(declare-const %s Float32)\n", arg->getName().str().c_str());

		/* give names to all instructions */
		int idx = 1;
		for(auto inst = block->begin(); inst != block->end(); inst++) {
			if(!inst->hasName())
				inst->setName("r" + std::to_string(idx++));
		}

		/* each instruction translates to an assert */
		for(auto inst = block->begin(); inst != block->end(); inst++) {
			switch(inst->getOpcode()) {
			/* and instruction */
			case llvm::Instruction::And:
				fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
				fprintf(file, "(assert (= %s (bvand %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)));
				break;

			/* or instruction */
			case llvm::Instruction::Or:
				fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
				fprintf(file, "(assert (= %s (bvor %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)));
				break;

			/* xor instruction */
			case llvm::Instruction::Xor:
				fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
				fprintf(file, "(assert (= %s (bvxor %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)));
				break;

			/* add instruction */
			case llvm::Instruction::FAdd:
				fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
				fprintf(file, "(assert (= %s (fp.add RNE %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)));
				break;

			/* return instruction */
			case llvm::Instruction::Select:
				fprintf(file, "(declare-const %s Int32)\n", getstr(&*inst));
				fprintf(file, "(assert (= %s (ite %s %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)), getstr(inst->getOperand(2)));
				break;

			/* bitcast instruction */
			case llvm::Instruction::BitCast:
				{
					llvm::BitCastInst *cast = llvm::cast<llvm::BitCastInst>(inst);

					fprintf(file, "(declare-const %s Int32)\n", getstr(&*inst));
					if(cast->getSrcTy()->isIntegerTy(32) && cast->getDestTy()->isFloatTy())
						fprintf(file, "(assert (= %s ((_ to_fp 8 24) %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)));
					else if(cast->getSrcTy()->isFloatTy() && cast->getDestTy()->isIntegerTy(32))
						fprintf(file, "(assert (= %s (to_ieee_bv %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)));
					else
						fatal("Unhandled bitcast.");
				}
				//fprintf(file, "(declare-const %s Int32)\n", getstr(&*inst));
				//fprintf(file, "(assert (= %s (ite %s %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)), getstr(inst->getOperand(2)));
				break;

			/* return instruction */
			case llvm::Instruction::Ret:
				fprintf(file, "(declare-const ret Float32)\n");
				fprintf(file, "(assert (= ret %s))", inst->getOperand(0)->getName().str().c_str());
				break;

			/* float comparison */
			case llvm::Instruction::FCmp:
				{
					const char *op;
					llvm::FCmpInst *cmp = llvm::cast<llvm::FCmpInst>(inst);

					switch(cmp->getPredicate()) {
					case llvm::CmpInst::FCMP_OLT: op = "fp.lt"; break;
					default: fatal("Unhandled conditional.\n");
					}

					fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
					fprintf(file, "(assert (= %s (%s %s %s)))\n", getstr(&*inst), op, getstr(inst->getOperand(0)), getstr(inst->getOperand(1)));
				}

				break;

			/* call instruction, depends on what we are calling */
			case llvm::Instruction::Call:
				{
					llvm::CallInst *call = llvm::cast<llvm::CallInst>(inst);
					std::string id = call->getCalledFunction()->getName().str();

					/* absolute value */
					if(id == "llvm.fabs.f32") {
						fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
						fprintf(file, "(assert (= %s (fp.abs %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)));
					}
					/* copysign value */
					else if(id == "llvm.copysign.f32") {
						fprintf(file, "(declare-const %s Float32)\n", getstr(&*inst));
						fprintf(file, "(assert (= %s (fp_copysign_f32 %s %s)))\n", getstr(&*inst), getstr(inst->getOperand(0)), getstr(inst->getOperand(1)));
					}
					else
						fatal("Unhandled call '%s'.", id.c_str());

					break;
				}

			default:
				fatal("Unhandled instruction '%s'.", inst->getOpcodeName());
			}
		}

		fprintf(file, "(check-sat)\n(get-model)\n");
		fclose(file);

		gofile(path.c_str());
	}

	return 0;
}

int old()
{
	setbuf(stdout, NULL);
	setbuf(stderr, NULL);

	std::unique_ptr<llvm::Module> mod = llvm_load("foo.ll");

	Z3_config cfg;
	Z3_sort sort32, sort64;

	cfg = Z3_mk_config();
	z3 = Z3_mk_context(cfg);
	Z3_del_config(cfg);

	solver = Z3_mk_solver_for_logic(z3, Z3_mk_string_symbol(z3, "QF_FPBV"));

	sort32 = Z3_mk_fpa_sort_32(z3);
	sort64 = Z3_mk_fpa_sort_64(z3);

	Z3_ast rnd = Z3_mk_fpa_rne(z3);

	if(solver|| rnd) {}
	/*
	Z3_ast a = Z3_mk_const(z3, Z3_mk_string_symbol(z3, "a"), sort32);
	Z3_ast b = Z3_mk_const(z3, Z3_mk_string_symbol(z3, "b"), sort32);
	Z3_ast c = Z3_mk_const(z3, Z3_mk_string_symbol(z3, "c"), sort32);

	Z3_solver_assert(z3, solver, Z3_mk_fpa_eq(z3, a, Z3_mk_fpa_numeral_float(z3, 1.0f, sort32)));
	Z3_solver_assert(z3, solver, Z3_mk_fpa_eq(z3, b, Z3_mk_fpa_numeral_float(z3, 2.0f, sort32)));
	Z3_solver_assert(z3, solver, Z3_mk_fpa_eq(z3, c, Z3_mk_fpa_numeral_float(z3, 3.0f, sort32)));
	Z3_solver_assert(z3, solver, Z3_mk_fpa_eq(z3, c, Z3_mk_fpa_add(z3, rnd, a, b)));
	*/

	//Z3_lbool res = Z3_solver_check(z3, solver);
	//printf("%d (%d %d %d)\n", res, Z3_L_FALSE, Z3_L_UNDEF, Z3_L_TRUE);
	//Z3_mk_fpa_numeral_float(z3, 1.0f, sort32);

	for(auto func = mod->begin(); func != mod->end(); func++) {
		if(func->size() == 0)
			continue;

		const char *fn = func->getName().str().c_str();
		if(func->size() != 1)
			fatal("Function '%s' has more than one basic block.", fn);

		std::map<llvm::Value *, Z3_ast> map;

		for(auto arg = func->arg_begin(); arg != func->arg_end(); arg++) {
			const char *reg = arg->getName().str().c_str();

			map[&*arg] = Z3_mk_const(z3, Z3_mk_string_symbol(z3, reg), sort32);
		}

		printf("[%s]\n", fn);
		auto block = func->begin();

		int idx = 1;
		for(auto inst = block->begin(); inst != block->end(); inst++) {
			if(!inst->hasName())
				inst->setName("r" + std::to_string(idx++));
		}

		for(auto inst = block->begin(); inst != block->end(); inst++) {
			Z3_ast var;
			const char *reg = inst->getName().str().c_str();
			if(reg[0] != '\0')
				map[&*inst] = var = Z3_mk_const(z3, Z3_mk_string_symbol(z3, reg), sort32);

			bool iscall = (inst->getOpcode() == llvm::Instruction::Call);
			std::vector<Z3_ast> param(inst->getNumOperands());
			for(int i = 0; i < inst->getNumOperands() - (iscall ? 1 : 0); i++) {
				param[i] = map[inst->getOperand(i)];
				assert(param[i] != nullptr);
			}

			switch(inst->getOpcode()) {
			case llvm::Instruction::Call:
				{
					llvm::CallInst *call = llvm::cast<llvm::CallInst>(inst);
					const char *id = call->getCalledFunction()->getName().str().c_str();
					printf("call: %s\n", id);
					if(strcmp(id, "llvm.fabs.f32") == 0) {
						z3_eq(var, Z3_mk_fpa_abs(z3, param[0]));
					}
					else
						fatal("Unhandled called function '%s'.", id);
				}
				break;

			case llvm::Instruction::FAdd:
				z3_eq(var, Z3_mk_fpa_add(z3, rnd, param[0], param[1]));
				break;

			case llvm::Instruction::Ret:
				break;

			default:
				fatal("Unhandled instruction '%s'.", inst->getOpcodeName());
			}

		}
		//for(auto block = func->
	}

	return 0;
}


/**
 * Load a module from a path.
 *   @fmt: The format string.
 *   @...: The printf-style arguments.
 *   &returns: The module.
 */
std::unique_ptr<llvm::Module> llvm_load(const char *fmt, ...)
{
	char path[1024];
	va_list args;
	llvm::SMDiagnostic err;
	std::unique_ptr<llvm::Module> mod;

	va_start(args, fmt);
	vsnprintf(path, sizeof(path), fmt, args);
	va_end(args);

	mod = parseIRFile(path, err, llvm_ctx);
	if(mod == nullptr)
		fatal("Cannot open '%s'.", path);

	return mod;
}


static void fatal(const char *str, ...)
{
	va_list args;

	va_start(args, str);
	vfprintf(stderr, str, args);
	fprintf(stderr, "\n");
	va_end(args);

	abort();
}

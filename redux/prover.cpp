#include <stdarg.h>
#include <stdio.h>
#include <unistd.h>

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

static void fatal(const char *str, ...);


void z3_eq(Z3_ast a, Z3_ast b)
{
	Z3_solver_assert(z3, solver, Z3_mk_fpa_eq(z3, a, Z3_mk_fpa_abs(z3, b)));
}

/**
 * Main entry point.
 */
int main()
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

#ifndef INC_HPP
#define INC_HPP

/*
 * common headers
 */
#include <assert.h>
#include <float.h>
#include <math.h>
#include <stdint.h>
#include <string.h>

#include <algorithm>
#include <map>
#include <string>
#include <variant>
#include <vector>

/*
 * prototypes
 */
namespace llvm {
	class Function;
	class Instruction;
	class Value;
};

/*
 * local headers
 */
#include "ival.hpp"
#include "range.hpp"
#include "fact.hpp"


/*
 * common defintions
 */
[[noreturn]] void dbg_fatal(const char *file, unsigned long line, const char *fmt, ...);

#define fatal(...) dbg_fatal(__FILE__, __LINE__, __VA_ARGS__)

/*
 * llvm helper functions
 */
std::string llvm_name(llvm::Value *value);

#endif

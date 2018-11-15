#ifndef INC_HPP
#define INC_HPP

/*
 * global headers
 */
#include <algorithm>
#include <cassert>
#include <map>
#include <iostream>
#include <variant>
#include <vector>

#include <float.h>
#include <math.h>
#include <stdint.h>

/*
 * prototypes
 */
namespace llvm {
	class Function;
	class Instruction;
	class Value;
};

class Fact;
class IvalI64;
class IvalF64;
class Pass;
class Range;
class RangeUndef;
class RangeI64;
class RangeF64;

/*
 * operation and king enumerators
 */
enum class Op { Unk, Add, Sub, Mul };
enum class Kind { Unk, Int, Flt };

/*
 * type class
 */
class Type {
public:
	Kind kind;
	uint32_t width, count;

	Type() { kind = Kind::Unk; width = 0; count = 0; }
	Type(Kind _kind, uint32_t _width) { kind = _kind; width = _width; count = 1; }
	Type(Kind _kind, uint32_t _width, uint32_t _count) { kind = _kind; width = _width; count = _count; }
};

/*
 * local headers
 */
#include "defs.h"
#include "ivali64.hpp"
#include "ivalf64.hpp"
#include "rangei64.hpp"
#include "rangef64.hpp"
#include "range.hpp"

#define fatal(...) do { fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); abort(); } while(0)

#endif

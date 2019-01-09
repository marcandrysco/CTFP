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

template <class T> class IvalFlt;
using IvalF64 = IvalFlt<double>;
using IvalF32 = IvalFlt<float>;

template <class T> class RangeFlt;
using RangeF64 = RangeFlt<double>;
using RangeF32 = RangeFlt<float>;

template <class T> class RangeVecFlt;
using RangeVecF64 = RangeVecFlt<double>;
using RangeVecF32 = RangeVecFlt<float>;

template <class T> class RangeInt;
using RangeI64 = RangeInt<uint64_t>;
using RangeI32 = RangeInt<uint32_t>;

template <class T> class RangeVecInt;
using RangeVecI64 = RangeVecInt<uint64_t>;
using RangeVecI32 = RangeVecInt<uint32_t>;

class Fact;
class Pass;
class Range;
class RangeBool;
class RangeUndef;
class RangeVecBool;

#define fatal(...) do { fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); abort(); } while(0)

/*
 * local headers
 */
#include "defs.h"
#include "fp.hpp"

#include "ivali64.hpp"
#include "ivalf64.hpp"
#include "rangei64.hpp"
#include "rangef64.hpp"
#include "range.hpp"

#endif

#pragma once

#include <stdarg.h>
#include <stdlib.h>
#include <math.h>

#include <iostream>

static inline void __attribute__((noreturn)) fatal(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	vfprintf(stderr, fmt, args);
	fprintf(stderr, "\n");
	va_end(args);

	abort();
}

/*
 * using statements
 */
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

/*
 * operation and king enumerators
 */
enum class Op { Unk, Add, Sub, Mul, And, Or, Xor, FtoI, ItoF, CmpOLT, CmpOGT, CmpOEQ, Select, Insert, Extract, Abs, Sqrt };
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
 * Instruction info class
 */
class Info {
public:
	Op op;
	Type type;

	Info(Op _op, Type _type) { op = _op; type = _type; }
};

/*
 * local includes
 */
#include "fp.hpp"
#include "ival.hpp"
#include "range.hpp"
#include "pass.hpp"

#!/usr/bin/python

import sys
import math
import struct


def tofloat(val):
	return struct.unpack('f', struct.pack('f', val))[0]

infile = open("tpl.ll", "r")
outfile = open("ctfp.ll", "w")

FLT_MIN = 1.17549435082228751e-38
FLT_MAX = 3.40282346638528860e+38
FLT_SIG = 16777216.0

FLT_ABS="2147483647"
FLT_SIGN_BITS="2147483648"
FLT_ADDMIN = "9.860760727515472e-32" # format(FLT_MIN * FLT_SIG * 0.5, ".17e")
FLT_MULMIN = format(tofloat(math.sqrt(FLT_MIN)), ".17e")
FLT_DIVMAX = format(tofloat(math.sqrt(FLT_MIN) / FLT_MIN), ".17e")

FLT_NORM_MIN = format(tofloat(FLT_MIN), ".17e")
FLT_ADD_OFF = format(tofloat(FLT_SIG), ".17e")
FLT_ADD_CMP = format(tofloat(FLT_MIN * FLT_SIG), ".17e")
FLT_MUL_OFF = format(tofloat(math.sqrt(1.0 / FLT_MIN)), ".17e")
FLT_MUL_CMP = "0x3FEFFFFFE0000000"
FLT_DIV_OFF = format(math.sqrt(FLT_MIN), ".17e")
FLT_SIG_BITS = str(0x007FFFFF)
FLT_POW4_BITS = str(0x00FFFFFF)
FLT_ODDEXP_BITS = str(0x00800000)

DBL_MIN = 2.22507385850720138e-308
DBL_MAX = 1.79769313486231571e+308
DBL_SIG = 18014398509481984.0

DBL_ABS="9223372036854775807"
DBL_SIGN_BITS="9223372036854775808"
DBL_ADDMIN = format(DBL_MIN * DBL_SIG * 0.5, ".17e")
DBL_MULMIN = format(math.sqrt(DBL_MIN), ".17e")
DBL_DIVMAX = format(math.sqrt(DBL_MIN) / DBL_MIN, ".17e")

DBL_NORM_MIN = format(DBL_MIN, ".17e")
DBL_ADD_OFF = format(DBL_SIG)
DBL_ADD_CMP = format(DBL_MIN * DBL_SIG)
DBL_MUL_OFF = format(1.0 / DBL_MIN, ".17e")
DBL_MUL_OFF = format(math.sqrt(1.0 / DBL_MIN), ".17e")
DBL_MUL_CMP = "0x3FEFFFFFFFFFFFFF"
DBL_DIV_OFF = format(math.sqrt(DBL_MIN), ".17e")
DBL_SIG_BITS = str(0x000FFFFFFFFFFFFF)
DBL_POW4_BITS = str(0x001FFFFFFFFFFFFF)
DBL_ODDEXP_BITS = str(0x0010000000000000)

tpl = infile.read();


def mkconst(value, ty, width):
	if width == 1:
		return value
	else:
		res = ty + " " + value;

		for i in range(1, width):
			res += ", " + ty + " " + value;

		return "< " + res + " >"


def mktype(ty, width):
	if width == 1:
		return ty
	else:
		return "< " + str(width) + " x " + ty + " >"


for width in [ 1, 2, 4, 8, 16, 32 ]:
	text = tpl

	text = text.replace("FP", mktype("float", width))
	text = text.replace("INT", mktype("i32", width))
	text = text.replace("VEC", (".v" + str(width) + "f32") if width > 1 else ".f32")
	text = text.replace("VAL_ZERO", mkconst("0.0", "float", width))
	text = text.replace("VAL_ONE", mkconst("1.0", "float", width))
	text = text.replace("VAL_INF", mkconst("0x7FF0000000000000", "float", width))
	text = text.replace("VAL_NAN", mkconst("0x7FF8000000000000", "float", width))
	text = text.replace("BOOL", mktype("i1", width))
	text = text.replace("ADDMIN", mkconst(FLT_ADDMIN, "float", width))
	text = text.replace("MULMIN", mkconst(FLT_MULMIN, "float", width))
	text = text.replace("DIVMAX", mkconst(FLT_DIVMAX, "float", width))
	text = text.replace("ABS", mkconst(FLT_ABS, "i32", width))
	text = text.replace("SIGN_BITS", mkconst(FLT_SIGN_BITS, "i32", width))
	text = text.replace("SIG_BITS", mkconst(FLT_SIG_BITS, "i32", width))
	text = text.replace("POW4_BITS", mkconst(FLT_POW4_BITS, "i32", width))
	text = text.replace("ODDEXP_BITS", mkconst(FLT_ODDEXP_BITS, "i32", width))
	text = text.replace("VAL_DUMMY", mkconst("1.5", "float", width))

	text = text.replace("ZERO", mkconst("0", "i32", width))
	text = text.replace("ONES", mkconst("-1", "i32", width))
	text = text.replace("ONE", mkconst("1", "i32", width))

	text = text.replace("NORM_MIN", mkconst(FLT_NORM_MIN, "float", width))
	text = text.replace("ADD_OFF", mkconst(FLT_ADD_OFF, "float", width))
	text = text.replace("ADD_CMP", mkconst(FLT_ADD_CMP, "float", width))
	text = text.replace("MUL_OFF", mkconst(FLT_MUL_OFF, "float", width))
	text = text.replace("MUL_CMP", mkconst(FLT_MUL_CMP, "float", width))
	text = text.replace("DIV_OFF", mkconst(FLT_DIV_OFF, "float", width))

	text = text.replace("NAME", "f" + str(width))
	outfile.write(text)


for width in [ 1, 2, 4, 8, 16 ]:
	text = tpl

	text = text.replace("FP", mktype("double", width))
	text = text.replace("INT", mktype("i64", width))
	text = text.replace("VEC", (".v" + str(width) + "f64") if width > 1 else ".f64")
	text = text.replace("VAL_ZERO", mkconst("0.0", "double", width))
	text = text.replace("VAL_ONE", mkconst("1.0", "double", width))
	text = text.replace("VAL_INF", mkconst("0x7FF0000000000000", "double", width))
	text = text.replace("VAL_NAN", mkconst("0x7FF8000000000000", "double", width))
	text = text.replace("BOOL", mktype("i1", width))
	text = text.replace("ADDMIN", mkconst(DBL_ADDMIN, "double", width))
	text = text.replace("MULMIN", mkconst(DBL_MULMIN, "double", width))
	text = text.replace("DIVMAX", mkconst(DBL_DIVMAX, "double", width))
	text = text.replace("ABS", mkconst(DBL_ABS, "i64", width))
	text = text.replace("SIGN_BITS", mkconst(DBL_SIGN_BITS, "i64", width))
	text = text.replace("SIG_BITS", mkconst(DBL_SIG_BITS, "i64", width))
	text = text.replace("POW4_BITS", mkconst(DBL_POW4_BITS, "i64", width))
	text = text.replace("ODDEXP_BITS", mkconst(DBL_ODDEXP_BITS, "i64", width))
	text = text.replace("VAL_DUMMY", mkconst("1.5", "double", width))

	text = text.replace("ZERO", mkconst("0", "i64", width))
	text = text.replace("ONES", mkconst("-1", "i64", width))
	text = text.replace("ONE", mkconst("1", "i64", width))

	text = text.replace("NORM_MIN", mkconst(DBL_NORM_MIN, "double", width))
	text = text.replace("ADD_OFF", mkconst(DBL_ADD_OFF, "double", width))
	text = text.replace("ADD_CMP", mkconst(DBL_ADD_CMP, "double", width))
	text = text.replace("MUL_OFF", mkconst(DBL_MUL_OFF, "double", width))
	text = text.replace("MUL_CMP", mkconst(DBL_MUL_CMP, "double", width))
	text = text.replace("DIV_OFF", mkconst(DBL_DIV_OFF, "double", width))

	text = text.replace("NAME", "d" + str(width))
	outfile.write(text)


infile.close()
outfile.close()

#!/usr/bin/python

import sys
import math
import struct


def tofloat(val):
	return struct.unpack('f', struct.pack('f', val))[0]

infile = open("add.spec", "r")
outfile = open("ctfp.ll", "w")

FLT_MIN = 1.17549435082228751e-38
FLT_MAX = 3.40282346638528860e+38
FLT_SIG = 16777216.0

FLT_ABS="2147483647"
FLT_ADDMIN = "9.860760727515472e-32" # format(FLT_MIN * FLT_SIG * 0.5, ".17e")
FLT_MULMIN = format(tofloat(math.sqrt(FLT_MIN)), ".17e")
FLT_DIVMAX = format(tofloat(math.sqrt(FLT_MIN) / FLT_MIN), ".17e")

FLT_NORM_MIN = format(tofloat(FLT_MIN), ".17e")
FLT_ADD_OFF = format(tofloat(FLT_SIG), ".17e")
FLT_ADD_CMP = format(tofloat(FLT_MIN * FLT_SIG), ".17e")

DBL_MIN = 2.22507385850720138e-308
DBL_MAX = 1.79769313486231571e+308
DBL_SIG = 9007199254740992.0

DBL_ABS="9223372036854775807"
DBL_ADDMIN = format(DBL_MIN * DBL_SIG * 0.5, ".17e")
DBL_MULMIN = format(math.sqrt(DBL_MIN), ".17e")
DBL_DIVMAX = format(math.sqrt(DBL_MIN) / DBL_MIN, ".17e")

DBL_NORM_MIN = format(DBL_MIN, ".17e")
DBL_ADD_OFF = format(DBL_SIG)
DBL_ADD_CMP = format(DBL_MIN * DBL_SIG)

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


for width in [ 1, 2, 4 ]:
	text = tpl

	text = text.replace("FP", mktype("float", width))
	text = text.replace("INT", mktype("i32", width))
	text = text.replace("VEC", (".v" + str(width) + "f32") if width > 1 else ".f32")
	text = text.replace("VAL_ZERO", mkconst("0.0", "float", width))
	text = text.replace("VAL_INF", mkconst("0x7FF0000000000000", "float", width))
	text = text.replace("BOOL", mktype("i1", width))
	text = text.replace("ADDMIN", mkconst(FLT_ADDMIN, "float", width))
	text = text.replace("MULMIN", mkconst(FLT_MULMIN, "float", width))
	text = text.replace("DIVMAX", mkconst(FLT_DIVMAX, "float", width))
	text = text.replace("ABS", mkconst(FLT_ABS, "i32", width))

	text = text.replace("ZEROS", mkconst("0", "i32", width))
	text = text.replace("ONES", mkconst("-1", "i32", width))

	text = text.replace("NORM_MIN", mkconst(FLT_NORM_MIN, "float", width))
	text = text.replace("ADD_OFF", mkconst(FLT_ADD_OFF, "float", width))
	text = text.replace("ADD_CMP", mkconst(FLT_ADD_CMP, "float", width))

	text = text.replace("NAME", "f" + str(width))
	outfile.write(text)


for width in [ 1, 2, 4 ]:
	text = tpl

	text = text.replace("FP", mktype("double", width))
	text = text.replace("INT", mktype("i64", width))
	text = text.replace("VEC", (".v" + str(width) + "f64") if width > 1 else ".f64")
	text = text.replace("VAL_ZERO", mkconst("0.0", "double", width))
	text = text.replace("VAL_INF", mkconst("0x7FF0000000000000", "double", width))
	text = text.replace("BOOL", mktype("i1", width))
	text = text.replace("ADDMIN", mkconst(DBL_ADDMIN, "double", width))
	text = text.replace("MULMIN", mkconst(DBL_MULMIN, "double", width))
	text = text.replace("DIVMAX", mkconst(DBL_DIVMAX, "double", width))
	text = text.replace("ABS", mkconst(DBL_ABS, "i64", width))

	text = text.replace("ZEROS", mkconst("0", "i64", width))
	text = text.replace("ONES", mkconst("-1", "i64", width))

	text = text.replace("NORM_MIN", mkconst(DBL_NORM_MIN, "double", width))
	text = text.replace("ADD_OFF", mkconst(DBL_ADD_OFF, "double", width))
	text = text.replace("ADD_CMP", mkconst(DBL_ADD_CMP, "double", width))

	text = text.replace("NAME", "d" + str(width))
	outfile.write(text)


infile.close()
outfile.close()

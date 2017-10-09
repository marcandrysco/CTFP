; add NAME

define weak FP @ctfp_add0_NAME(FP %a, FP %b) {
	%r = fadd FP %a, %b
	ret FP %r
}

define weak FP @ctfp_add1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, ADDMIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, ADDMIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b

	%r = fadd FP %a4, %b4
	ret FP %r
}

define weak FP @ctfp_add2_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, ADD_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, ADD_OFF

	%t0 = fadd FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m1
	%a8 = bitcast INT %a7 to FP

	%b6 = bitcast FP %b4 to INT
	%b7 = and INT %b6, %m1
	%b8 = bitcast INT %b7 to FP

	%r = fadd FP %a8, %b8
	ret FP %r
}

define weak FP @ctfp_add3_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, ADD_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, ADD_OFF

	%t0 = fadd FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZEROS
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP

	%b6 = bitcast FP %b4 to INT
	%b7 = and INT %b6, %m4
	%b8 = bitcast INT %b7 to FP

	%r = fadd FP %a8, %b8
	ret FP %r
}

; sub NAME

define weak FP @ctfp_sub0_NAME(FP %a, FP %b) {
	%r = fsub FP %a, %b
	ret FP %r
}

define weak FP @ctfp_sub1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, ADDMIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, ADDMIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b

	%r = fsub FP %a4, %b4
	ret FP %r
}

define weak FP @ctfp_sub2_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, ADD_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, ADD_OFF

	%t0 = fsub FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m1
	%a8 = bitcast INT %a7 to FP

	%b6 = bitcast FP %b4 to INT
	%b7 = and INT %b6, %m1
	%b8 = bitcast INT %b7 to FP

	%r = fsub FP %a8, %b8
	ret FP %r
}

define weak FP @ctfp_sub3_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, ADD_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, ADD_OFF

	%t0 = fsub FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZEROS
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP

	%b6 = bitcast FP %b4 to INT
	%b7 = and INT %b6, %m4
	%b8 = bitcast INT %b7 to FP

	%r = fsub FP %a8, %b8
	ret FP %r
}

; mul NAME

define weak FP @ctfp_mul0_NAME(FP %a, FP %b) {
	%r = fmul FP %a, %b
	ret FP %r
}

define weak FP @ctfp_mul1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, MULMIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, MULMIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b

	%r = fmul FP %a4, %b4
	ret FP %r
}

define weak FP @ctfp_mul3_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, MUL_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, MUL_OFF

	%t0 = fmul FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZEROS
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP

	%r = fmul FP %a8, %b4
	ret FP %r
}

define weak FP @ctfp_mul2_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, MUL_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, MUL_OFF

	%t0 = fmul FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, MUL_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m1
	%a8 = bitcast INT %a7 to FP

	%r = fmul FP %a8, %b4
	ret FP %r
}

; div NAME

define weak FP @ctfp_div0_NAME(FP %a, FP %b) {
	%r = fdiv FP %a, %b
	ret FP %r
}

define weak FP @ctfp_div1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, MULMIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fcmp ogt FP %a2, DIVMAX
	%a6 = select BOOL %a5, FP VAL_INF, FP %a4

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, MULMIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fcmp ogt FP %b2, DIVMAX
	%b6 = select BOOL %b5, FP VAL_INF, FP %b4

	%r = fdiv FP %a6, %b6
	ret FP %r
}

define weak FP @ctfp_div2_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, MUL_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, DIV_OFF

	%t0 = fdiv FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, MUL_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m1
	%a8 = bitcast INT %a7 to FP

	%r = fdiv FP %a8, %b4
	ret FP %r
}

define weak FP @ctfp_div3_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, MUL_OFF

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, DIV_OFF

	%t0 = fdiv FP %a5, %b5

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZEROS
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZEROS
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP

	%r = fdiv FP %a8, %b4
	ret FP %r
}


; sqrt NAME

define weak FP @ctfp_sqrt0_NAME(FP %a) {
	%r = tail call FP @llvm.sqrtVEC(FP %a)
	ret FP %r
}

define weak FP @ctfp_sqrt1_NAME(FP %a) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a

	%r = tail call FP @llvm.sqrtVEC(FP %a4)
	ret FP %r
}

declare FP @llvm.sqrtVEC(FP %a)

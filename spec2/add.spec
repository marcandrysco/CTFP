; add NAME

define FP @ctfp_add0_NAME(FP %a, FP %b) {
	%r = fadd FP %a, %b
	ret FP %r
}

define FP @ctfp_add1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, ADDMIN
	%a4 = select BOOL %a3, FP ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, ADDMIN
	%b4 = select BOOL %b3, FP ZERO, FP %b

	%r = fadd FP %a4, %b4
	ret FP %r
}

; sub NAME

define FP @ctfp_sub0_NAME(FP %a, FP %b) {
	%r = fsub FP %a, %b
	ret FP %r
}

define FP @ctfp_sub1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, ADDMIN
	%a4 = select BOOL %a3, FP ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, ADDMIN
	%b4 = select BOOL %b3, FP ZERO, FP %b

	%r = fsub FP %a4, %b4
	ret FP %r
}

; mul NAME

define FP @ctfp_mul0_NAME(FP %a, FP %b) {
	%r = fmul FP %a, %b
	ret FP %r
}

define FP @ctfp_mul1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, MULMIN
	%a4 = select BOOL %a3, FP ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, MULMIN
	%b4 = select BOOL %b3, FP ZERO, FP %b

	%r = fmul FP %a4, %b4
	ret FP %r
}

; div NAME

define FP @ctfp_div0_NAME(FP %a, FP %b) {
	%r = fdiv FP %a, %b
	ret FP %r
}

define FP @ctfp_div1_NAME(FP %a, FP %b) {
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, MULMIN
	%a4 = select BOOL %a3, FP ZERO, FP %a

	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp ogt FP %b2, DIVMAX
	%b4 = select BOOL %b3, FP ZERO, FP %b

	%r = fdiv FP %a4, %b4
	ret FP %r
}


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
	%m1 = select BOOL %m0, INT ONES, INT ZERO

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
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
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
	%m1 = select BOOL %m0, INT ONES, INT ZERO

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
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
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

	%m0 = fcmp uge FP %t3, MUL_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
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
	%m1 = select BOOL %m0, INT ONES, INT ZERO

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

define weak FP @ctfp_div_NAME(FP %a, FP %b) #0 {
	; common constants
	%one = bitcast FP VAL_ONE to INT
	%inf = bitcast FP VAL_INF to INT
	%nan = bitcast FP VAL_NAN to INT
	%dummy = bitcast FP VAL_DUMMY to INT

	; discard values outside the range on input A
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP

	; discard values outside the range on input B
	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP

	; compute the sign bit
	%s0 = xor INT %a0, %b0
	%s1 = xor INT ABS, ONES
	%s2 = and INT %s0, %s1

	; split B into exponent (%b9) and significand (%b12)
	%b8 = xor INT SIG_BITS, ONES
	%b9 = and INT %b1, %b8
	%b10 = and INT %b1, SIG_BITS
	%b11 = bitcast FP VAL_ONE to INT
	%b12 = or INT %b10, %b11

	; test for special values
	%t1 = fcmp oeq FP %a2, VAL_INF
	%t2 = fcmp oeq FP %a2, VAL_ZERO
	%t3 = fcmp une FP %a2, %a2
	%t4 = fcmp oeq FP %b2, VAL_INF
	%t5 = fcmp oeq FP %b2, VAL_ZERO
	%t6 = fcmp une FP %b2, %b2
	%t7 = icmp eq INT %b12, %one

	; convert special comparisons into bitmasks
	%u1 = select BOOL %t1, INT ONES, INT ZERO
	%u2 = select BOOL %t2, INT ONES, INT ZERO
	%u3 = select BOOL %t3, INT ONES, INT ZERO
	%u4 = select BOOL %t4, INT ONES, INT ZERO
	%u5 = select BOOL %t5, INT ONES, INT ZERO
	%u6 = select BOOL %t6, INT ONES, INT ZERO
	%u7 = select BOOL %t7, INT ONES, INT ZERO

	; check for nan (mask %c1, constant %c2)
	%n1 = and INT %u2, %u5
	%n2 = and INT %u1, %u4
	%n3 = or INT %n1, %n2
	%n4 = or INT %u3, %u6
	%c1 = or INT %n3, %n4
	%c1n = xor INT %c1, ONES
	%c2 = and INT %c1, %nan

	; check for inf (mask %c3, constant %c4)
	%i1 = or INT %u1, %u5
	%i2 = and INT %i1, %c1n
	%i3 = and INT %inf, %i2
	%c3 = or INT %c1, %i2
	%c3n = xor INT %c3, ONES
	%c4 = or INT %c2, %i3

	; check for zero (mask %c5, constant %c6)
	%z1 = or INT %u2, %u4
	%z2 = and INT %z1, %c3n
	%z3 = and INT ZERO, %z2
	%c5 = or INT %c3, %z2
	%c5n = xor INT %c5, ONES
	%c6 = or INT %c4, %z3

	; mask in dummy value to A (%a11)
	%a8 = and INT %a1, %c5n
	%a9 = and INT %dummy, %c5
	%a10 = or INT %a8, %a9
	%a11 = bitcast INT %a10 to FP

	; mask in the dummy value to B exponent (%b16)
	%b13 = and INT %b9, %c5n
	%b14 = and INT %one, %c5
	%b15 = or INT %b13, %b14
	%b16 = bitcast INT %b15 to FP

	; compute exponent result (%r1)
	%r1 = fdiv FP %a11, %b16

	; check for one (mask %c7, constant %c8)
	%o1 = and INT %u7, %c5n
	%o2 = bitcast FP %r1 to INT
	%o3 = and INT %o1, %o2
	%c7 = or INT %c5, %o1
	%c7n = xor INT %c7, ONES
	%c8 = or INT %c6, %o3

	; check for inf (mask %c9, constant %c10)
	%i4 = fcmp oeq FP %r1, VAL_INF
	%i5 = select BOOL %i4, INT ONES, INT ZERO
	%c9 = or INT %c7, %i5
	%c9n = xor INT %c9, ONES
	%i6 = xor INT %i5, ONES
	%i7 = and INT %i6, %c8
	%i8 = and INT %i5, %inf
	%c10 = or INT %i7, %i8

	; check for zero (mask %c11, constant %c12)
	%z4 = fcmp oeq FP %r1, VAL_ZERO
	%z5 = select BOOL %z4, INT ONES, INT ZERO
	%c11 = or INT %c9, %z5
	%c11n = xor INT %c11, ONES
	%z6 = xor INT %z5, ONES
	%c12 = and INT %z6, %c10

	; mask in dummy value to R significand (%a11)
	%r0 = bitcast FP %r1 to INT
	%r2 = and INT %r0, %c11n
	%r3 = and INT %dummy, %c11
	%r4 = or INT %r2, %r3
	%r5 = bitcast INT %r4 to FP

	; mask in dummy value to B significand (%a11)
	%b17 = and INT %b12, %c11n
	%b18 = and INT %dummy, %c11
	%b19 = or INT %b17, %b18
	%b20 = bitcast INT %b19 to FP

	; compute final result (%r2)
	%r6 = fdiv FP %r5, %b20

	; mask in constant and sign bit
	%r7 = bitcast FP %r6 to INT
	%r8 = and INT %r7, %c11n
	%r9 = or INT %r8, %c12
	%r10 = or INT %r9, %s2
	%r11 = bitcast INT %r10 to FP
	
	ret FP %r11
}

define weak FP @ctfp_div1_NAME(FP %a, FP %b) {
	; discard values outside the range on input A
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, MULMIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fcmp ogt FP %a2, DIVMAX
	%a6 = select BOOL %a5, FP VAL_INF, FP %a4

	; discard values outside the range on input B
	%b0 = bitcast FP %b to INT
	%b1 = and INT %b0, ABS
	%b2 = bitcast INT %b1 to FP
	%b3 = fcmp olt FP %b2, MULMIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fcmp ogt FP %b2, DIVMAX
	%b6 = select BOOL %b5, FP VAL_INF, FP %b4

	%r = tail call FP @ctfp_div_NAME(FP %a6, FP %b6)
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
	%b6 = fcmp olt FP %b2, VAL_ONE
	%b7 = select BOOL %b6, FP VAL_ONE, FP %b4

	%b5 = fmul FP %b7, DIV_OFF

	%t0 = tail call FP @ctfp_div_NAME(FP %a5, FP %b5)

	%t1 = bitcast FP %t0 to INT
	%t2 = and INT %t1, ABS
	%t3 = bitcast INT %t2 to FP

	%m0 = fcmp uge FP %t3, MUL_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP

	%r = tail call FP @ctfp_div_NAME(FP %a8, FP %b4)
	ret FP %r
}


; sqrt NAME

define weak FP @ctfp_sqrt0_NAME(FP %a) {
	%r = tail call FP @llvm.sqrtVEC(FP %a)
	ret FP %r
}

define weak FP @ctfp_sqrt1_NAME(FP %a) {
	; common constants
	%one = bitcast FP VAL_ONE to INT
	%inf = bitcast FP VAL_INF to INT
	%nan = bitcast FP VAL_NAN to INT
	%dummy = bitcast FP VAL_DUMMY to INT

	; flush subnormals to zero
	%a0 = bitcast FP %a to INT
	%a1 = and INT %a0, ABS
	%a2 = bitcast INT %a1 to FP
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = bitcast FP %a4 to INT

	; compute the sign bit
	%s1 = xor INT ABS, ONES
	%s2 = and INT %a0, %s1

	; check for zero
	%t1 = fcmp oeq FP %a4, VAL_ZERO
	%m1 = select BOOL %t1, INT ONES, INT ZERO
	%m1n = xor INT %m1, ONES
	%c1 = and INT %m1n, %a5
	%d1 = and INT %m1, %dummy
	%a6 = or INT %c1, %d1

	; check for inf
	%t2 = fcmp oeq FP %a4, VAL_INF
	%m2 = select BOOL %t2, INT ONES, INT ZERO
	%m2n = xor INT %m2, ONES
	%c2 = and INT %m2n, %a6
	%d2 = and INT %m2, %dummy
	%a7 = or INT %c2, %d2

	; check for nan
	%t3 = fcmp ult FP %a4, VAL_ZERO
	%m3 = select BOOL %t3, INT ONES, INT ZERO
	%m3n = xor INT %m3, ONES
	%c3 = and INT %m3n, %a7
	%d3 = and INT %m3, %dummy
	%a8 = or INT %c3, %d3

	; check for power of four
	%f1 = and INT %a8, POW4_BITS
	%f2 = icmp eq INT %f1, ODDEXP_BITS
	%f3 = select BOOL %f2, INT ONES, INT ZERO
	%f4 = and INT SIG_BITS, %f3
	%f5 = xor INT %f4, ONES
	%a9 = or INT %a8, %f4

	; compute root
	%r0 = bitcast INT %a9 to FP
	%r1 = tail call FP @llvm.sqrtVEC(FP %r0)
	%r2 = bitcast FP %r1 to INT

	; replace zero
	%v1 = and INT %r2, %m1n
	%v1n = and INT ZERO, %m1
	%r3 = or INT %v1, %v1n

	; replace infinity
	%v2 = and INT %r3, %m2n
	%v2n = and INT %inf, %m2
	%r4 = or INT %v2, %v2n

	; replace nan
	%v3 = and INT %r4, %m3n
	%v3n = and INT %nan, %m3
	%r5 = or INT %v3, %v3n

	; add in sign bit
	%r6 = or INT %r5, %s2
	%r7 = and INT %r6, %f5
	%r8 = bitcast INT %r7 to FP
	ret FP %r8
}

declare FP @llvm.sqrtVEC(FP %a)
attributes #0 = { alwaysinline }

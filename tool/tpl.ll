; misc NAME

define weak FP @or_NAME(FP %a, FP %b) #0 {
	%a1 = bitcast FP %a to INT
	%b1 = bitcast FP %b to INT
	%r1 = or INT %a1, %b1
	%r2 = bitcast INT %r1 to FP
	ret FP %r2
}
; def or(a, b):
;   return a | b

define weak FP @and_NAME(FP %a, FP %b) #0 {
	%a1 = bitcast FP %a to INT
	%b1 = bitcast FP %b to INT
	%r1 = and INT %a1, %b1
	%r2 = bitcast INT %r1 to FP
	ret FP %r2
}
; def and(a, b):
;   return a & b

define weak FP @xor_NAME(FP %a, FP %b) #0 {
	%a1 = bitcast FP %a to INT
	%b1 = bitcast FP %b to INT
	%r1 = xor INT %a1, %b1
	%r2 = bitcast INT %r1 to FP
	ret FP %r2
}
; def and(a, b):
;   return a ^ b

define weak FP @not_NAME(FP %a) #0 {
	%a1 = bitcast FP %a to INT
	%a2 = xor INT %a1, ONES
	%a3 = bitcast INT %a2 to FP
	ret FP %a3
}
; def not(a):
;   return ~a

define weak FP @isnan_NAME(FP %a) #0 {
	%c = fcmp une FP %a, %a
	%i = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %i to FP
	ret FP %f
}
; def isnan(a):
;   return a != a

define weak FP @eq_NAME(FP %a, FP %b) #0 {
	%c = fcmp oeq FP %a, %b
	%i = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %i to FP
	ret FP %f
}
; def eq(a, b):
;   return (a == b) ? ONES : ZEROS

define weak FP @mask_NAME(FP %m, FP %a, FP %b) #0 {
	%n = call FP @not_NAME(FP %m)
	%a1 = call FP @and_NAME(FP %m, FP %a)
	%b1 = call FP @and_NAME(FP %n, FP %b)
	%r = call FP @or_NAME(FP %a1, FP %b1)
	ret FP %r
}
; def mask(m, a, b)
;   return (m & a) | (~m & b)

define weak FP @cond_NAME(BOOL %c, FP %a, FP %b) #0 {
	%m1 = select BOOL %c, INT ONES, INT ZERO
	%m2 = xor INT %m1, ONES

	%a1 = bitcast FP %a to INT
	%a2 = and INT %m1, %a1

	%b1 = bitcast FP %b to INT
	%b2 = and INT %m2, %b1

	%r1 = or INT %a2, %b2
	%r2 = bitcast INT %r1 to FP
	ret FP %r2
}
; def cond(c, a, b)
;   return if c then a else b

define weak FP @underflow_NAME(FP %a, FP %l) #0 {
	%a1 = call FP @llvm.fabsVEC(FP %a)
	%a2 = fcmp olt FP %a1, %l
	%a3 = select BOOL %a2, FP VAL_ZERO, FP %a
	%a4 = call FP @llvm.copysignVEC(FP %a3, FP %a)
	ret FP %a4
}
; def underflow(a, l):
;   return if a < l then 0 else a

define weak FP @overflow_NAME(FP %a, FP %l) #0 {
	%a1 = call FP @llvm.fabsVEC(FP %a)
	%a2 = fcmp olt FP %a1, %l
	%a3 = select BOOL %a2, FP VAL_ZERO, FP %a
	%a4 = call FP @llvm.copysignVEC(FP %a3, FP %a)
	ret FP %a4
}
; def underflow(a, l):
;   return if a > l then INFINITY else a

define weak BOOL @tryadd_NAME(FP %a, FP %b) #0 {
	%a1 = fmul FP %a, ADD_OFF
	%b1 = fmul FP %b, ADD_OFF

	%t1 = fadd FP %a1, %b1
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = fcmp uge FP %t2, ADD_CMP
	%t4 = fcmp ueq FP %t2, VAL_ZERO
	%t5 = or BOOL %t3, %t4
	ret BOOL %t5
}
; def tryadd(a, b):
;   t := fabs((a * ADD_OFF) + (b * ADD_OFF))
;   return (t == 0.0) || (t >= ADD_CMP)

define weak BOOL @trymul_NAME(FP %a, FP %b) #0 {
	%a2 = fmul FP %a, MUL_OFF

	%t1 = fmul FP %a2, %b
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = fcmp uge FP %t2, MUL_CMP
	%t4 = fcmp ueq FP %t2, VAL_ZERO
	%t5 = or BOOL %t3, %t4
	ret BOOL %t5
}
; def trymul(a, b):
;   t := fabs((a * MUL_OFF) * b)
;   return (t == 0.0) || (t >= MUL_CMP)

define weak BOOL @trymul_fma_NAME(FP %a, FP %b) #0 {
	%a2 = fmul FP %a, MUL_OFF

	;%t1 = fmul FP %a2, %b
	%t1 = call FP @llvm.fmaVEC(FP %a2, FP %b, FP FMA_ADD)
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = fcmp uge FP %t2, MUL_CMP
	%t4 = fcmp ueq FP %t2, VAL_ZERO
	%t5 = or BOOL %t3, %t4
	ret BOOL %t5
}
; def trymul_fma(a, b):
;   t := fabs(fma((a * MUL_OFF), b, FMA_ADD))
;   return (t == 0.0) || (t >= MUL_CMP)

define weak BOOL @trydiv_NAME(FP %a, FP %b) #0 {
	%a2 = fmul FP %a, MUL_OFF

	%t1 = tail call FP @ctfp_div_NAME(FP %a2, FP %b)
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = fcmp uge FP %t2, MUL_CMP
	%t4 = fcmp ueq FP %t2, VAL_ZERO
	%t5 = or BOOL %t3, %t4
	ret BOOL %t5
}
; def trydiv(a, b):
;   t := fabs((a * MUL_OFF) / b)
;   return (t == 0.0) || (t >= MUL_CMP)

define weak FP @getexp_NAME(FP %a) #0 {
	%t1 = bitcast FP %a to INT
	%t2 = and INT %t1, EXP_BITS
	%t3 = bitcast INT %t2 to FP
	ret FP %t3
}
; def getexp(a):
;   return a & EXP_BITS

define weak FP @getsig_NAME(FP %a) #0 {
	%t1 = bitcast FP %a to INT
	%t2 = and INT %t1, SIG_BITS
	%t3 = bitcast FP VAL_ONE to INT
	%t4 = or INT %t2, %t3
	%t5 = bitcast INT %t4 to FP
	ret FP %t5
}
; def getsig(a):
;   return (a & SIG_BITS) | 1.0

define weak {FP, FP, FP} @initdummy_NAME(FP %v) #0 {
	%d1 = insertvalue {FP, FP, FP} undef, FP %v, 0
	%d2 = insertvalue {FP, FP, FP} %d1, FP VAL_ZERO, 1
	%d3 = insertvalue {FP, FP, FP} %d2, FP VAL_ZERO, 2
	ret {FP, FP, FP} %d3
}
; def initdummy(v):
;   return (v, 0, 0)

define weak {FP, FP, FP} @setdummy_NAME(FP %m, FP %r, {FP, FP, FP} %d) #0 {
	%dv = extractvalue {FP, FP, FP} %d, 0
	%dm = extractvalue {FP, FP, FP} %d, 1
	%dr = extractvalue {FP, FP, FP} %d, 2

	%d2v = call FP @mask_NAME(FP %m, FP VAL_DUMMY, FP %dv)
	%d2m = call FP @or_NAME(FP %m, FP %dm)
	%d2r = call FP @mask_NAME(FP %m, FP %r, FP %dr)

	%d1 = insertvalue {FP, FP, FP} undef, FP %d2v, 0
	%d2 = insertvalue {FP, FP, FP} %d1, FP %d2m, 1
	%d3 = insertvalue {FP, FP, FP} %d2, FP %d2r, 2

	ret {FP, FP, FP} %d3
}
; def setdummy(m, r, (dv, dm, dr)):
;   return (mask(m, 1.5, dv), m | dm, mask(m, r, dr))

define weak {FP, FP, FP} @ifdummy_NAME(FP %c, {FP, FP, FP} %d) #0 {
	%v = extractvalue {FP, FP, FP} %d, 0
	%m = call FP @eq_NAME(FP %c, FP %v)
	%r = call {FP, FP, FP} @setdummy_NAME(FP %m, FP %c, {FP, FP, FP} %d)
	ret {FP, FP, FP} %r
}
; def ifdummy(c, (dv, dm, dr)):
;   return setdummy((c == dv), c, d)

define weak FP @applydummy_NAME(FP %v, {FP, FP, FP} %d) #0 {
	%dm = extractvalue {FP, FP, FP} %d, 1
	%dr = extractvalue {FP, FP, FP} %d, 2
	%r = call FP @mask_NAME(FP %dm, FP %dr, FP %v)
	ret FP %r
}
; def applydummy(v, (dv, dm, dr)):
;   return mask(dm, dr, v)

define weak FP @divbyparts_NAME(FP %a, FP %b) #0 {
	%e = call FP @getexp_NAME(FP %b)
	%s1 = call FP @getsig_NAME(FP %b)

	%i1 = fdiv FP %a, %e
	;%i1 = call FP @chkdiv_NAME(FP %a, FP %e, INT ONE)

	%m1 = call FP @eq_NAME(FP %s1, FP VAL_ONE)
	%s2 = call FP @mask_NAME(FP %m1, FP VAL_DUMMY, FP %s1)

	%m2 = call FP @eq_NAME(FP %i1, FP VAL_INF)
	%m3 = call FP @eq_NAME(FP %i1, FP VAL_ZERO)
	%m4 = call FP @or_NAME(FP %m2, FP %m3)
	%i2 = call FP @mask_NAME(FP %m4, FP VAL_DUMMY, FP %i1)

	%t2 = fdiv FP %i2, %s2
	;%t2 = call FP @chkdiv_NAME(FP %i2, FP %s2, INT ZERO)

	%t3 = call FP @mask_NAME(FP %m1, FP %i1, FP %t2)
	%t4 = call FP @mask_NAME(FP %m2, FP VAL_INF, FP %t3)
	%t5 = call FP @mask_NAME(FP %m3, FP VAL_ZERO, FP %t4)

	ret FP %t5
}
; def divbyparts(a, b):
;   i1 := a / getexp(b)
;   i2 := if ((i2 == Inf) || (i2 == 0.0)) then 1.5 else i1
;   s1 := getsig(b)
;   s2 := if (s1 == 1.0) then 1.5 else s1
;   r1 := i2 / s2
;   r2 := if (s1 == 1.0) then i2 else r1
;   r3 := if (i2 == Inf) then Inf else r2
;   r4 := if (i2 == 0.0) then 0.0 else r3
;   return r4

			declare void @dump_NAME(FP %v)

define weak FP @divdummy_NAME(FP %a, FP %b) #0 {
	%a0 = call FP @llvm.fabsVEC(FP %a)
	%b0 = call FP @llvm.fabsVEC(FP %b)

	%an = call FP @isnan_NAME(FP %a0)
	%bn = call FP @isnan_NAME(FP %b0)

	%ai = call FP @eq_NAME(FP %a0, FP VAL_INF)
	%bi = call FP @eq_NAME(FP %b0, FP VAL_INF)

	%az = call FP @eq_NAME(FP %a0, FP VAL_ZERO)
	%bz = call FP @eq_NAME(FP %b0, FP VAL_ZERO)

	%mn1 = call FP @and_NAME(FP %az, FP %bz)
	%mn2 = call FP @and_NAME(FP %ai, FP %bi)
	%mn3 = call FP @or_NAME(FP %an, FP %bn)
	%mn4 = call FP @or_NAME(FP %mn1, FP %mn2)
	%mn = call FP @or_NAME(FP %mn3, FP %mn4)

	%mi = call FP @or_NAME(FP %ai, FP %bz)

	%mz = call FP @or_NAME(FP %az, FP %bi)

	%m1 = call FP @or_NAME(FP %mi, FP %mz)
	%m2 = call FP @or_NAME(FP %m1, FP %mn)

	%a1 = call FP @mask_NAME(FP %m2, FP VAL_DUMMY, FP %a0)
	%b1 = call FP @mask_NAME(FP %m2, FP VAL_DUMMY, FP %b0)

	%r1 = call FP @divbyparts_NAME(FP %a1, FP %b1)

	%r2 = call FP @mask_NAME(FP %mz, FP VAL_ZERO, FP %r1)
	%r3 = call FP @mask_NAME(FP %mi, FP VAL_INF, FP %r2)
	%r4 = call FP @mask_NAME(FP %mn, FP VAL_NAN, FP %r3)

	%sgn = call FP @xor_NAME(FP %a, FP %b)
	%r5 = call FP @llvm.copysignVEC(FP %r4, FP %sgn)

	ret FP %r5
}

; add NAME

define weak FP @ctfp_add0_NAME(FP %a, FP %b) {
	%r = fadd FP %a, %b
	ret FP %r
}

define weak FP @ctfp_add1_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP ADDMIN)
	%b1 = call FP @underflow_NAME(FP %b, FP ADDMIN)

	%r = fadd FP %a1, %b1
	ret FP %r
}

define weak FP @ctfp_add2_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%b1 = call FP @underflow_NAME(FP %b, FP NORM_MIN)

	%t1 = call BOOL @tryadd_NAME(FP %a1, FP %b1)

	%a2 = call FP @cond_NAME(BOOL %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @cond_NAME(BOOL %t1, FP %b1, FP VAL_ZERO)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = fadd FP %a3, %b3
	ret FP %r
}

define weak FP @ctfp_add3_NAME(FP %a, FP %b) {
	%a2 = call FP @llvm.fabsVEC(FP %a)
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, ADD_OFF

	%b2 = call FP @llvm.fabsVEC(FP %b)
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, ADD_OFF

	%t0 = fadd FP %a5, %b5
	%t3 = call FP @llvm.fabsVEC(FP %t0)

	%m0 = fcmp uge FP %t3, ADD_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP
	%a9 = call FP @llvm.copysignVEC(FP %a8, FP %a)

	%b6 = bitcast FP %b4 to INT
	%b7 = and INT %b6, %m4
	%b8 = bitcast INT %b7 to FP
	%b9 = call FP @llvm.copysignVEC(FP %b8, FP %b)

	%r = fadd FP %a9, %b9
	ret FP %r
}

; sub NAME

define weak FP @ctfp_sub0_NAME(FP %a, FP %b) {
	%r = fsub FP %a, %b
	ret FP %r
}

define weak FP @ctfp_sub1_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP ADDMIN)
	%b1 = call FP @underflow_NAME(FP %b, FP ADDMIN)

	%r = fsub FP %a1, %b1
	ret FP %r
}

define weak FP @ctfp_sub2_NAME(FP %a, FP %b) {
	%a2 = call FP @llvm.fabsVEC(FP %a)
	%a1 = bitcast FP %a2 to INT
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, ADD_OFF

	%b2 = call FP @llvm.fabsVEC(FP %b)
	%b1 = bitcast FP %b2 to INT
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fmul FP %b4, ADD_OFF

	%t0 = fsub FP %a5, %b5
	%t3 = call FP @llvm.fabsVEC(FP %t0)

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
	%a1 = call FP @underflow_NAME(FP %a, FP MULMIN)
	%b1 = call FP @underflow_NAME(FP %b, FP MULMIN)

	%r = fmul FP %a1, %b1
	ret FP %r
}

define weak FP @ctfp_mul2_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%b1 = call FP @underflow_NAME(FP %b, FP NORM_MIN)

	%t1 = call BOOL @trymul_NAME(FP %a1, FP %b1)

	%a2 = call FP @cond_NAME(BOOL %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @cond_NAME(BOOL %t1, FP %b1, FP VAL_ZERO)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = fmul FP %a3, %b3
	ret FP %r
}

define weak FP @ctfp_mul2_fma_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%b1 = call FP @underflow_NAME(FP %b, FP NORM_MIN)

	%t1 = call BOOL @trymul_fma_NAME(FP %a1, FP %b1)

	%a2 = call FP @cond_NAME(BOOL %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @cond_NAME(BOOL %t1, FP %b1, FP VAL_ZERO)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = fmul FP %a3, %b3
	ret FP %r
}

define weak FP @ctfp_mul3_NAME(FP %a, FP %b) {
	%a2 = call FP @llvm.fabsVEC(FP %a)
	%a1 = bitcast FP %a2 to INT
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, MUL_OFF

	%b2 = call FP @llvm.fabsVEC(FP %b)
	%b1 = bitcast FP %b2 to INT
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b6 = call FP @llvm.copysignVEC(FP %b4, FP %b)

	%t0 = fmul FP %a5, %b4
	%t3 = call FP @llvm.fabsVEC(FP %t0)

	%m0 = fcmp uge FP %t3, MUL_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP
	%a9 = call FP @llvm.copysignVEC(FP %a8, FP %a)

	%r = fmul FP %a9, %b6
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

	; compute absolute values
	%a0 = bitcast FP %a to INT
	%a2 = call FP @llvm.fabsVEC(FP %a)
	%a1 = bitcast FP %a2 to INT
	%b0 = bitcast FP %b to INT
	%b2 = call FP @llvm.fabsVEC(FP %b)
	%b1 = bitcast FP %b2 to INT

	; compute the sign bit
	%s0 = xor INT %a0, %b0
	%s2 = and INT %s0, SIGN_BITS

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
	%r11 = or INT %r9, %s2
	%r12 = bitcast INT %r11 to FP
	
	ret FP %r12
}

define weak FP @ctfp_div1_NAME(FP %a, FP %b) {
	; discard values outside the range on input A
	%a2 = call FP @llvm.fabsVEC(FP %a)
	%a1 = bitcast FP %a2 to INT
	%a3 = fcmp olt FP %a2, MULMIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fcmp ogt FP %a2, DIVMAX
	%a6 = select BOOL %a5, FP VAL_INF, FP %a4
	%a7 = call FP @llvm.copysignVEC(FP %a6, FP %a)

	; discard values outside the range on input B
	%b2 = call FP @llvm.fabsVEC(FP %b)
	%b1 = bitcast FP %b2 to INT
	%b3 = fcmp olt FP %b2, MULMIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b5 = fcmp ogt FP %b2, DIVMAX
	%b6 = select BOOL %b5, FP VAL_INF, FP %b4
	%b7 = call FP @llvm.copysignVEC(FP %b6, FP %b)

	%r = tail call FP @divdummy_NAME(FP %a7, FP %b7)
	ret FP %r
}

define weak FP @ctfp_div2_NAME(FP %a, FP %b) {
	%a2 = call FP @llvm.fabsVEC(FP %a)
	%a1 = bitcast FP %a2 to INT
	%a3 = fcmp olt FP %a2, NORM_MIN
	%a4 = select BOOL %a3, FP VAL_ZERO, FP %a
	%a5 = fmul FP %a4, MUL_OFF

	%b2 = call FP @llvm.fabsVEC(FP %b)
	%b1 = bitcast FP %b2 to INT
	%b3 = fcmp olt FP %b2, NORM_MIN
	%b4 = select BOOL %b3, FP VAL_ZERO, FP %b
	%b6 = fcmp olt FP %b2, VAL_ONE
	%b7 = select BOOL %b6, FP VAL_ONE, FP %b4

	%t0 = tail call FP @divdummy_NAME(FP %a5, FP %b7)

	%t3 = call FP @llvm.fabsVEC(FP %t0)

	%m0 = fcmp uge FP %t3, MUL_CMP
	%m1 = select BOOL %m0, INT ONES, INT ZERO
	%m2 = fcmp ueq FP %t3, VAL_ZERO
	%m3 = select BOOL %m2, INT ONES, INT ZERO
	%m4 = or INT %m1, %m3

	%a6 = bitcast FP %a4 to INT
	%a7 = and INT %a6, %m4
	%a8 = bitcast INT %a7 to FP

	%a9 = call FP @llvm.copysignVEC(FP %a8, FP %a)
	%b8 = call FP @llvm.copysignVEC(FP %b4, FP %b)

	%r = tail call FP @divdummy_NAME(FP %a9, FP %b8)
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
declare FP @llvm.fabsVEC(FP %a)
declare FP @llvm.copysignVEC(FP %a, FP %b)
declare FP @llvm.fmaVEC(FP %a, FP %b, FP %c)

declare FP @chkdiv_NAME(FP %a, FP %b, INT %c)

attributes #0 = { alwaysinline }

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

define weak FP @isuneg_NAME(FP %a) #0 {
	%c = fcmp ult FP %a, VAL_ZERO
	%i = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %i to FP
	ret FP %f
}
; def isuneg(a):
;   return (a < 0.0) || (a != a)

define weak FP @isolt_NAME(FP %a, FP %b) #0 {
	%c = fcmp olt FP %a, %b
	%i = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %i to FP
	ret FP %f
}
; def isolt(a, b):
;   return a < b;

define weak FP @isogt_NAME(FP %a, FP %b) #0 {
	%c = fcmp ogt FP %a, %b
	%i = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %i to FP
	ret FP %f
}
; def isogt(a, b):
;   return a > b;

define weak FP @uge_NAME(FP %a, FP %b) #0 {
	%c = fcmp uge FP %a, %b
	%i = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %i to FP
	ret FP %f
}
; def uge(a, b):
;   return (a >= b) || (a == NaN) || (b == NaN);

define weak FP @ispow4_NAME(FP %a) #0 {
	%i = bitcast FP %a to INT
	%b = and INT %i, POW4_BITS
	%c = icmp eq INT %b, ODDEXP_BITS
	%m = select BOOL %c, INT ONES, INT ZERO
	%f = bitcast INT %m to FP
	ret FP %f
}
; def ispow4(a):
;   return (a & POW4_BITS) == ODDEXP_BITS;

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
; def mask(m, a, b):
;   return (m & a) | (~m & b)

define weak FP @underflow_NAME(FP %a, FP %l) #0 {
	%a1 = call FP @llvm.fabsVEC(FP %a)
	%a2 = call FP @isolt_NAME(FP %a1, FP %l)
	%a3 = call FP @mask_NAME(FP %a2, FP VAL_ZERO, FP %a)
	%a4 = call FP @llvm.copysignVEC(FP %a3, FP %a)
	ret FP %a4
}
; def underflow(a, l):
;   return if |a| < l then 0.0 else a

define weak FP @overflow_NAME(FP %a, FP %l) #0 {
	%a1 = call FP @llvm.fabsVEC(FP %a)
	%a2 = call FP @isogt_NAME(FP %a1, FP %l)
	%a3 = call FP @mask_NAME(FP %a2, FP VAL_INF, FP %a)
	%a4 = call FP @llvm.copysignVEC(FP %a3, FP %a)
	ret FP %a4
}
; def underflow(a, l):
;   return if |a| > l then INFINITY else a

define weak FP @tryadd_NAME(FP %a, FP %b) #0 {
	%a1 = fmul FP %a, ADD_OFF
	%b1 = fmul FP %b, ADD_OFF

	%t1 = fadd FP %a1, %b1
	%t2 = call FP @llvm.fabsVEC(FP %t1)

	%t3 = call FP @uge_NAME(FP %t2, FP ADD_CMP)
	%t4 = call FP @eq_NAME(FP %t2, FP VAL_ZERO)
	%t5 = call FP @or_NAME(FP %t3, FP %t4)
	ret FP %t5
}
; def tryadd(a, b):
;   t := fabs((a * ADD_OFF) + (b * ADD_OFF))
;   return (t == 0.0) || (t >= ADD_CMP)

define weak FP @trysub_NAME(FP %a, FP %b) #0 {
	%a1 = fmul FP %a, ADD_OFF
	%b1 = fmul FP %b, ADD_OFF

	%t1 = fsub FP %a1, %b1
	%t2 = call FP @llvm.fabsVEC(FP %t1)

	%t3 = call FP @uge_NAME(FP %t2, FP ADD_CMP)
	%t4 = call FP @eq_NAME(FP %t2, FP VAL_ZERO)
	%t5 = call FP @or_NAME(FP %t3, FP %t4)
	ret FP %t5
}
; def trysub(a, b):
;   t := fabs((a * ADD_OFF) - (b * ADD_OFF))
;   return (t == 0.0) || (t >= ADD_CMP)

define weak FP @trymul_NAME(FP %a, FP %b) #0 {
	%a2 = fmul FP %a, MUL_OFF

	%t1 = fmul FP %a2, %b
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = call FP @uge_NAME(FP %t2, FP MUL_CMP)
	%t4 = call FP @eq_NAME(FP %t2, FP VAL_ZERO)
	%t5 = call FP @or_NAME(FP %t3, FP %t4)
	ret FP %t5
}
; def trymul(a, b):
;   t := fabs((a * MUL_OFF) * b)
;   return (t == 0.0) || (t >= MUL_CMP)

define weak FP @trymul_fma_NAME(FP %a, FP %b) #0 {
	%a2 = fmul FP %a, MUL_OFF

	%t1 = call FP @llvm.fmaVEC(FP %a2, FP %b, FP FMA_ADD)
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = call FP @uge_NAME(FP %t2, FP MUL_CMP)
	%t4 = call FP @eq_NAME(FP %t2, FP VAL_ZERO)
	%t5 = call FP @or_NAME(FP %t3, FP %t4)
	ret FP %t5
}
; def trymul_fma(a, b):
;   t := fabs(fma((a * MUL_OFF), b, FMA_ADD))
;   return (t == 0.0) || (t >= MUL_CMP)

define weak FP @trydiv_NAME(FP %a, FP %b) #0 {
	%a2 = fmul FP %a, MUL_OFF

	%t1 = call FP @divdummy_NAME(FP %a2, FP %b)
	%t2 = call FP @llvm.fabsVEC(FP %t1)
	%t3 = call FP @uge_NAME(FP %t2, FP MUL_CMP)
	%t4 = call FP @eq_NAME(FP %t2, FP VAL_ZERO)
	%t5 = call FP @or_NAME(FP %t3, FP %t4)
	ret FP %t5
}
; def trydiv(a, b):
;   t := fabs((a * MUL_OFF) / b)
;   return (t == 0.0) || (t >= MUL_CMP)

define weak FP @getexp_NAME(FP %a) #0 {
	%b = bitcast INT EXP_BITS to FP
	%r = call FP @and_NAME(FP %a, FP %b)
	ret FP %r
}
; def getexp(a):
;   return a & EXP_BITS

define weak FP @getsig_NAME(FP %a) #0 {
	%b = bitcast INT SIG_BITS to FP
	%t = call FP @and_NAME(FP %a, FP %b)
	%r = call FP @or_NAME(FP %t, FP VAL_ONE)
	ret FP %r
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
; def divdummy(a, b):
;   nan  := isnan(a) | isnan(b)
;                    | ((a == INF) & (b == INF))
;                    | ((a == 0.0) & (b == 0.0))
;   inf  := (a == INF) | (b == 0.0)
;   zero := (a == 0.0) | (b == INF)
;   a'   := if (nan || inf || zero) then 1.5 else a'
;   b'   := if (nan || inf || zero) then 1.5 else b'
;   tmp1 := a' / b'
;   tmp2 := if zero then 0.0 else tmp1
;   tmp3 := if inf  then INF else tmp1
;   tmp3 := if nan  then NAN else tmp1
;   return tmp3

define weak FP @blindsqrt_NAME(FP %a) #0 {
	%m2 = bitcast INT ONE to FP
	%m3 = call FP @ispow4_NAME(FP %a)
	%m4 = call FP @and_NAME(FP %m2, FP %m3)
	%m5 = call FP @not_NAME(FP %m4)

	%a1 = call FP @or_NAME(FP %a, FP %m4)
	%a2 = tail call FP @llvm.sqrtVEC(FP %a1)
	;%a2 = tail call FP @chksqrt_NAME(FP %a1)
	%a3 = call FP @and_NAME(FP %a2, FP %m5)

	ret FP %a3
}
; def blindsqrt(a):
;   t1 = if ispow4 then a | 1 else a
;   t2 = sqrt t1
;   t3 = if ispow4 then t2 & ~1 else t2
;   return t3

define weak FP @sqrtdummy_NAME(FP %a) #0 {
	%n = call FP @isuneg_NAME(FP %a)
	%i = call FP @eq_NAME(FP %a, FP VAL_INF)
	%z = call FP @eq_NAME(FP %a, FP VAL_ZERO)

	%m1 = call FP @or_NAME(FP %n, FP %i)
	%m2 = call FP @or_NAME(FP %m1, FP %z)

	%a3 = call FP @mask_NAME(FP %m2, FP VAL_DUMMY, FP %a)

	%r1 = call FP @blindsqrt_NAME(FP %a3)

	%r2 = call FP @mask_NAME(FP %z, FP VAL_ZERO, FP %r1)
	%r3 = call FP @mask_NAME(FP %n, FP VAL_NAN, FP %r2)
	%r4 = call FP @mask_NAME(FP %i, FP VAL_INF, FP %r3)
	
	%r5 = call FP @llvm.copysignVEC(FP %r4, FP %a)

	ret FP %r5
}
; def sqrtdummy(a):
;   neg  := (a < 0)
;   inf  := (a == inf)
;   zero := (a == 0.0)
;   tmp  := if (neg | inf | zero) then 1.5 else a
;   res  := blindsqrt(tmp)
;   res2 := if neg then NAN else res
;   res3 := if inf then INF else res2
;   res4 := if inf then INF else res3
;   return copysign(res4, a)

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

	%t1 = call FP @tryadd_NAME(FP %a1, FP %b1)

	%a2 = call FP @mask_NAME(FP %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @mask_NAME(FP %t1, FP %b1, FP VAL_ZERO)
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
	%a1 = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%b1 = call FP @underflow_NAME(FP %b, FP NORM_MIN)

	%t1 = call FP @trysub_NAME(FP %a1, FP %b1)

	%a2 = call FP @mask_NAME(FP %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @mask_NAME(FP %t1, FP %b1, FP VAL_ZERO)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = fsub FP %a3, %b3
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

	%t1 = call FP @trymul_NAME(FP %a1, FP %b1)

	%a2 = call FP @mask_NAME(FP %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @mask_NAME(FP %t1, FP %b1, FP VAL_ZERO)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = fmul FP %a3, %b3
	ret FP %r
}

define weak FP @ctfp_mul2_fma_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%b1 = call FP @underflow_NAME(FP %b, FP NORM_MIN)

	%t1 = call FP @trymul_fma_NAME(FP %a1, FP %b1)

	%a2 = call FP @mask_NAME(FP %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @mask_NAME(FP %t1, FP %b1, FP VAL_ZERO)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = fmul FP %a3, %b3
	ret FP %r
}

; div NAME

define weak FP @ctfp_div0_NAME(FP %a, FP %b) {
	%r = fdiv FP %a, %b
	ret FP %r
}

define weak FP @ctfp_div1_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP MULMIN)
	%b1 = call FP @overflow_NAME(FP %b, FP DIVMAX)

	%r = tail call FP @divdummy_NAME(FP %a1, FP %b1)
	ret FP %r
}

define weak FP @ctfp_div2_NAME(FP %a, FP %b) {
	%a1 = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%b1 = call FP @underflow_NAME(FP %b, FP NORM_MIN)

	%t1 = call FP @trydiv_NAME(FP %a1, FP %b1)

	%a2 = call FP @mask_NAME(FP %t1, FP %a1, FP VAL_ZERO)
	%a3 = call FP @llvm.copysignVEC(FP %a2, FP %a)

	%b2 = call FP @mask_NAME(FP %t1, FP %b1, FP VAL_ONE)
	%b3 = call FP @llvm.copysignVEC(FP %b2, FP %b)

	%r = call FP @divdummy_NAME(FP %a3, FP %b3)
	ret FP %r
}


; sqrt NAME

define weak FP @ctfp_sqrt0_NAME(FP %a) {
	%r = tail call FP @llvm.sqrtVEC(FP %a)
	ret FP %r
}

define weak FP @ctfp_sqrt1_NAME(FP %a) {
	%t = call FP @underflow_NAME(FP %a, FP NORM_MIN)
	%r = call FP @sqrtdummy_NAME(FP %t)
	ret FP %r
}

declare FP @llvm.sqrtVEC(FP %a)
declare FP @llvm.fabsVEC(FP %a)
declare FP @llvm.copysignVEC(FP %a, FP %b)
declare FP @llvm.fmaVEC(FP %a, FP %b, FP %c)

declare FP @chkdiv_NAME(FP %a, FP %b, INT %c)
declare FP @chksqrt_NAME(FP %a)

declare void @dump_NAME(FP %v)

attributes #0 = { alwaysinline }

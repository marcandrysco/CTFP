(set-logic QF_FPBV)


; define bitvector types
(define-sort Int32 () (_ BitVec 32))
(define-sort Int64 () (_ BitVec 64))


; CONSANTS
(define-const addmin Float32 ((_ to_fp 8 24) #x0c000000))
(define-const zero Float32 ((_ to_fp 8 24) #x00000000))


; check if a value is NaN
(define-fun isnan ((x Float32)) Bool
  (not (fp.eq x x))
)

; get the sign as a bitvector
(define-fun getsign ((x Float32)) Int32
  (bvand (to_ieee_bv x) #x80000000)
)

; compare values for equal such that: x = y OR isnan(x) & isnan(y)
(define-fun iseq ((x Float32) (y Float32)) Bool
  (or
    (and (fp.eq x y) (= (getsign x) (getsign y)))
    (and (isnan x) (isnan y))
  )
)


;define weak float @ctfp_restrict_add_f32v1(float %a, float %b) #2 {
(declare-const a Float32)
(declare-const b Float32)

; PRE-CONDITION: NONE

; %1 = call float @llvm.fabs.f32(float %a)
(declare-const r1 Float32)
(assert (= r1 (fp.abs a)))

; %2 = fcmp olt float %1, 0x3980000000000000
(declare-const r2 Bool)
(assert (= r2 (fp.lt r1 ((_ to_fp 8 24) RNE addmin))))

; %3 = select i1 %2, i32 -1, i32 0
(declare-const r3 Int32)
(assert (= r3 (ite r2 #xffffffff #x00000000)))

; %4 = bitcast i32 %3 to float
(declare-const r4 Float32)
(assert (= r4 ((_ to_fp 8 24) RNE r3)))

; %5 = xor i32 %3, -1
(declare-const r5 Int32)
(assert (= r5 (bvxor r3 #xffffffff)))

; %6 = bitcast i32 %5 to float
(declare-const r6 Float32)
(assert (= r6 ((_ to_fp 8 24) RNE r5)))

; %7 = bitcast float %a to i32
(declare-const r7 Int32)
(assert (= r7 (to_ieee_bv a)))

; %8 = and i32 %5, %7
(declare-const r8 Int32)
(assert (= r8 (bvand r5 r7)))

; %9 = bitcast i32 %8 to float
(declare-const r9 Float32)
(assert (= (to_ieee_bv r9) r8))

; %10 = call float @llvm.copysign.f32(float %9, float %a)
(declare-const r10 Float32)
(assert (= (to_ieee_bv r10) (bvor
  (bvand (to_ieee_bv r9) #x7fffffff)
  (bvand (to_ieee_bv a) #x80000000)
)))

; POST-CONDITION: |r11| >= ADDMIN | |r11| = 0.0 | isnan(r11)
(declare-const post1 Bool)
(assert (= post1 (not (
  or
  (fp.geq (fp.abs r10) addmin)
  (fp.eq (fp.abs r10) zero)
  (isnan r10)
))))

; %11 = call float @ctfp_restrict_add_f32v1_1(float %10, float %b)
(declare-const r11 Float32)
(assert (= r11 (fp.add RNE r10 b)))

; COMPUTED ANSWER
(declare-const ret Float32)
(assert (= ret r11))

; ACTUAL ANSWER
(declare-const ans Float32)
(assert (= ans (fp.add RNE a b)))

; CORRECT-CONDITION-1: (|a| >= ADDMIN || |a| = 0) => ret = a + b
(declare-const cor1 Bool)
(assert (= cor1 (not (
  =>
    (or
      (fp.geq (fp.abs a) addmin)
      (fp.eq (fp.abs a) zero)
    )
    (or
      (fp.eq ret (fp.add RNE a b))
      (and (isnan ret) (isnan (fp.add RNE a b)))
    )
))))

; CORRECT-CONDITION-2: (|a| < ADDMIN && |a| > 0) => ret = 0*a + b
(declare-const cor2 Bool)
(assert (= cor2 (not (
  =>
    (and
      (fp.lt (fp.abs a) addmin)
      (fp.gt (fp.abs a) zero)
    )
    (iseq ret (fp.add RNE (fp.mul RNE zero a) b))
))))

(assert (or post1 cor1 cor2))

(check-sat)
;(get-model)

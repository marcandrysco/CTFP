(set-logic QF_FPBV)

(define-fun split ((b Bool)) Bool (or b (not b)))
(define-fun spliteq32 ((a Float32) (b Float32)) Bool (or (= a b) (not (= a b))))
(define-fun spliteq64 ((a Float64) (b Float64)) Bool (or (= a b) (not (= a b))))

; The global rounding mode
(declare-const rm RoundingMode)

(define-sort Int1    () Bool)
(define-sort Int32   () (_ BitVec 32))
(define-sort Int64   () (_ BitVec 64))
(define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) a))
(define-fun fp_add ((a Float32) (b Float32)) Float32 (fp.add rm a b))
(define-fun fp_sub ((a Float32) (b Float32)) Float32 (fp.sub rm a b))
(define-fun fp_mul ((a Float32) (b Float32)) Float32 (fp.mul rm a b))
(define-fun fp_sqrt ((a Float32)) Float32 (fp.sqrt rm a))
(define-fun fp_div ((a Float32) (b Float32)) Float32 (fp.div rm a b))
(define-const addmin Float32 ((_ to_fp 8 24) #x0c000000))
;(define-const addmin Float32 ((_ to_fp 8 24) #x0bffffff)) ; FAILS!
(define-const mulmin Float32 ((_ to_fp 8 24) #x20000000))
;(define-const mulmin Float32 ((_ to_fp 8 24) #x1fffffff)) ; FAILS!
(define-const divmin Float32 ((_ to_fp 8 24) #x00800000))
(define-const divmin4 Float32 (fp #b0 #x03 #b00000000000000000000000))
(define-const mulmin64 Float64 ((_ to_fp 11 53) #x2000000000000000))
(define-const divmax Float32 ((_ to_fp 8 24) #x5e800000))
;(define-const divmax Float32 ((_ to_fp 8 24) #x5e800001)) ; FAILS!
(define-const divmax64 Float64 ((_ to_fp 11 53) #x5fd0000000000000))
(define-const sqrtmin Float32 ((_ to_fp 8 24) #x00800000))
;(define-const sqrtmin Float32 ((_ to_fp 8 24) #x007fffff)) ; FAILS!
(define-const zero Float32 ((_ to_fp 8 24) #x00000000))
(define-const zero64 Float64 ((_ to_fp 11 53) #x0000000000000000))
(define-const one Float32 ((_ to_fp 8 24) #x3f800000))
(define-const one64 Float64 ((_ to_fp 11 53) RTZ 1.0))
(define-const onePt5 Float32 (fp #b0 #x7f #b10000000000000000000000))
(define-const two Float32 ((_ to_fp 8 24) #x40000000))
(define-const two64 Float64 ((_ to_fp 11 53) RNE 2.0))
(define-const four Float32 ((_ to_fp 8 24) #x40800000))
(define-const eight Float32 ((_ to_fp 8 24) RNE 8.0))
(define-const forth Float32 ((_ to_fp 8 24) #x3e800000))
(define-const thirtytwoth Float32 ((_ to_fp 8 24) RTZ 0.03125))
(define-const inf Float32 ((_ to_fp 8 24) #x7f800000))
(define-const inf64 Float64 ((_ to_fp 11 53) #x7ff0000000000000))

(define-const fltmin Float32 ((_ to_fp 8 24) #x00800000))
(define-const dblmin Float64 ((_ to_fp 11 53) #x0010000000000000))
(define-const fltmin4 Float32 ((_ to_fp 8 24) #x01800000))
(define-const fltmax Float32 ((_ to_fp 8 24) #x7f7fffff))
(define-const dblmax Float64 ((_ to_fp 11 53) #x7fefffffffffffff))
(define-const fltmax8 Float32 (fp.div RNE fltmax eight))
(define-const fltmax32 Float32 (fp #b0 #xf9 #b11111111111111111111111))
(define-const fltmax4 Float32 (fp #b0 #xfc #b11111111111111111111111))
(define-const divlo Float32 ((_ to_fp 8 24) #x01000000))
(define-const divlo64 Float64 ((_ to_fp 11 53) #x0020000000000000))
(define-const divcmp Float32 ((_ to_fp 8 24) #x40800000))

(define-const zero1 (_ BitVec 1) (_ bv0 1))
(define-const zero23 (_ BitVec 23) (_ bv0 23))
(define-const zero52 (_ BitVec 52) (_ bv0 52))
(define-const one8 (_ BitVec 8) (_ bv128 8))
(define-const bias (_ BitVec 8) (_ bv127 8))
(define-const muloff Float32 ((_ to_fp 8 24) #x7e800000))
(define-const divoff Float32 ((_ to_fp 8 24) #x7e800000))
(define-const divoff2 Float32 ((_ to_fp 8 24) RNE 8.0))

(define-const one_point_zero Float32 ((_ to_fp 8 24) roundTowardZero 1.0))
(define-const zero_point_zero Float32 ((_ to_fp 8 24) roundTowardZero 0.0))

; (define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) (_ BitVec 32) a))
;    ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb))

;
; some functions on Int32
(define-fun lt32    ((a Int32) (b Int32)) Bool 
  (bvslt a b)
)
(define-fun rng32   ((n Int32) (x Int32)) Bool 
  (or (= #x00000000 x) (bvsle n x))
)
(define-fun trunc32 ((n Int32) (x Int32)) Int32 
  (ite (bvslt x n) #x00000000 x)
)
(define-fun plus32  ((a Int32) (b Int32)) Int32 
  (bvadd a b)
) 
; some functions on Float32 
(define-fun fp_rng  ((n Float32) (x Float32)) Bool 
  (or (fp.isZero x) (fp.isNaN x) (fp.leq n (fp.abs x)))
)

(define-fun copysign ((a Float32) (b Float32)) Float32  
  (to_fp_32 (bvor (bvand (to_ieee_bv a) #x7fffffff)                  
    		          (bvand (to_ieee_bv b) #x80000000)))
)

(define-fun fp_trunc ((n Float32) (x Float32)) Float32 
  (ite (fp.lt (fp.abs x) n) (copysign zero x) x)
)


;; CONSTANTS

; cast a bitvector to a float
(define-fun fp64_cast ((a Int64)) Float64  ((_ to_fp 11 53) a))

; zero
(define-const fp64_zero Float64 (fp64_cast #x0000000000000000))

; add limits
(define-const fp64_addmin Float64 (fp64_cast #x0360000000000000))


;; HELPERS

; copy the sign of b onto the magnitude of a
(define-fun fp64_copysign ((a Float64) (b Float64)) Float64  
  (fp64_cast (bvor
    (bvand (to_ieee_bv a) #x7fffffffffffffff)
    (bvand (to_ieee_bv b) #x8000000000000000)
  ))
)

; check if a value is special
(define-fun fp_isspec_f32 ((a Float32)) Bool
  (or (fp.isZero a) (fp.isInfinite a) (fp.isNaN a) (fp.isSubnormal a))
)
(define-fun fp_isspec_f64 ((a Float64)) Bool
  (or (fp.isZero a) (fp.isInfinite a) (fp.isNaN a) (fp.isSubnormal a))
)

; check if a value is a power-of-two
(define-fun fp32_ispow2 ((v Float32)) Bool
  (= #x00000000 (bvand (to_ieee_bv v) #x007fffff))
)
(define-fun fp64_ispow2 ((v Float64)) Bool
  (= #x0000000000000000 (bvand (to_ieee_bv v) #x000fffffffffffff))
)

; check if a value is a power-of-four
(define-fun fp32_ispow4 ((v Float32)) Bool
  (= #x00800000 (bvand (to_ieee_bv v) #x00ffffff))
)
(define-fun fp64_ispow4 ((v Float64)) Bool
  (= #x0010000000000000 (bvand (to_ieee_bv v) #x001fffffffffffff))
)

(define-fun fp32_sign ((v Float32)) (_ BitVec 1)
  ((_ extract 31 31) (to_ieee_bv v))
)

(define-fun fp32_exp ((v Float32)) (_ BitVec 8)
  ((_ extract 30 23) (to_ieee_bv v))
)

(define-fun fp32_sig ((v Float32)) (_ BitVec 23)
  ((_ extract 22 0) (to_ieee_bv v))
)

(define-fun fp64_sign ((v Float64)) (_ BitVec 1)
  ((_ extract 63 63) (to_ieee_bv v))
)

(define-fun fp64_exp ((v Float64)) (_ BitVec 11)
  ((_ extract 62 52) (to_ieee_bv v))
)

(define-fun fp64_sig ((v Float64)) (_ BitVec 52)
  ((_ extract 51 0) (to_ieee_bv v))
)

; underflow a value below `lim` to zero
(define-fun fp32_underflow ((val Float32) (lim Float32)) Float32 
  (ite (fp.lt (fp.abs val) lim) (copysign zero val) val)
)
(define-fun fp64_underflow ((val Float64) (lim Float64)) Float64 
  (ite (fp.lt (fp.abs val) lim) (fp64_copysign fp64_zero val) val)
)
(define-fun fp32_underflow_pos ((val Float32) (lim Float32)) Float32 
  (ite (fp.lt val lim) zero val)
)
(define-fun fp32_underflow_neg ((val Float32) (lim Float32)) Float32 
  (ite (fp.gt val (fp.neg lim)) (fp.neg zero) val)
)

; overflow a value above `lim` to infinity
(define-fun fp32_overflow ((val Float32) (lim Float32)) Float32 
  (ite (fp.gt (fp.abs val) lim) (copysign inf val) val)
)

(define-fun fp64_overflow ((val Float64) (lim Float64)) Float64 
  (ite (fp.gt (fp.abs val) lim) (fp64_copysign inf64 val) val)
)

; clamp a value to the range `[lo,hi]`, over/under-flowing as needed
(define-fun fp32_clamp ((x Float32) (lo Float32) (hi Float32)) Float32
  (fp32_overflow (fp32_underflow x lo) hi)
)

(define-fun fp64_clamp ((x Float64) (lo Float64) (hi Float64)) Float64
  (fp64_overflow (fp64_underflow x lo) hi)
)


; return true if above or at a threshold
(define-fun fp32_above ((val Float32) (lim Float32)) Bool
  (fp.geq val lim)
)

; return true if below or at a threshold
(define-fun fp32_below ((val Float32) (lim Float32)) Bool
  (fp.leq val lim)
)

; return true if inside a range, inclusive
(define-fun fp32_range ((val Float32) (lo Float32) (hi Float32)) Bool
  (and (fp.geq val lo) (fp.leq val hi))
)

(define-fun fp64_range ((val Float64) (lo Float64) (hi Float64)) Bool
  (and (fp.geq val lo) (fp.leq val hi))
)

; return true if inside a range, exclusive
(define-fun fp32_between ((val Float32) (lo Float32) (hi Float32)) Bool
  (and (fp.gt val lo) (fp.lt val hi))
)

(define-fun fp64_between ((val Float64) (lo Float64) (hi Float64)) Bool
  (and (fp.gt val lo) (fp.lt val hi))
)


;; RESTRICT ADDITION PRE/POST

; addition, part 0
(define-fun restrict_add_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_add_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add rm (fp32_underflow a addmin) (fp32_underflow b addmin)))
)

; addition, part 1
(define-fun restrict_add_f32_pre1 ((a Float32) (b Float32)) Bool
  (or (fp.eq a zero) (fp.geq (fp.abs a) addmin) (fp.isNaN a))
)
(define-fun restrict_add_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add rm a (fp32_underflow b addmin)))
)

; addition, part 2
(define-fun restrict_add_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.eq a zero) (fp.geq (fp.abs a) addmin) (fp.isNaN a))
    (or (fp.eq b zero) (fp.geq (fp.abs b) addmin) (fp.isNaN b))
  )
)
(define-fun restrict_add_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add rm a b))
)

; addition f64, part 0
(define-fun restrict_add_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun restrict_add_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.add rm (fp64_underflow a fp64_addmin) (fp64_underflow b fp64_addmin)))
)

; addition f64, part 1
(define-fun restrict_add_f64_pre1 ((a Float64) (b Float64)) Bool
  (or (fp.eq a fp64_zero) (fp.geq (fp.abs a) fp64_addmin) (fp.isNaN a))
)
(define-fun restrict_add_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.add rm a (fp64_underflow b fp64_addmin)))
)

; addition f64, part 2
(define-fun restrict_add_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.eq a fp64_zero) (fp.geq (fp.abs a) fp64_addmin) (fp.isNaN a))
    (or (fp.eq b fp64_zero) (fp.geq (fp.abs b) fp64_addmin) (fp.isNaN b))
  )
)
(define-fun restrict_add_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.add rm a b))
)


;; RESTRICT SUBTRACTION PRE/POST

; subtraction, part 0
(define-fun restrict_sub_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_sub_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub rm (fp32_underflow a addmin) (fp32_underflow b addmin)))
)

; subtraction, part 1
(define-fun restrict_sub_f32_pre1 ((a Float32) (b Float32)) Bool
  (or (fp.eq a zero) (fp.geq (fp.abs a) addmin) (fp.isNaN a))
)
(define-fun restrict_sub_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub rm a (fp32_underflow b addmin)))
)

; subtraction, part 2
(define-fun restrict_sub_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.eq a zero) (fp.geq (fp.abs a) addmin) (fp.isNaN a))
    (or (fp.eq b zero) (fp.geq (fp.abs b) addmin) (fp.isNaN b))
  )
)
(define-fun restrict_sub_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub rm a b))
)

; subtraction f64, part 0
(define-fun restrict_sub_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun restrict_sub_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.sub rm (fp64_underflow a fp64_addmin) (fp64_underflow b fp64_addmin)))
)

; subtraction f64, part 1
(define-fun restrict_sub_f64_pre1 ((a Float64) (b Float64)) Bool
  (or (fp.eq a fp64_zero) (fp.geq (fp.abs a) fp64_addmin) (fp.isNaN a))
)
(define-fun restrict_sub_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.sub rm a (fp64_underflow b fp64_addmin)))
)

; subtraction f64, part 2
(define-fun restrict_sub_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.eq a fp64_zero) (fp.geq (fp.abs a) fp64_addmin) (fp.isNaN a))
    (or (fp.eq b fp64_zero) (fp.geq (fp.abs b) fp64_addmin) (fp.isNaN b))
  )
)
(define-fun restrict_sub_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.sub rm a b))
)


;; RESTRICT MULTIPLICATION PRE/POST

; multiplication, part 0
(define-fun restrict_mul_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_mul_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul rm (fp32_underflow a mulmin) (fp32_underflow b mulmin)))
)

; multiplication, part 1
(define-fun restrict_mul_f32_pre1 ((a Float32) (b Float32)) Bool
  (or (fp.eq a zero) (fp.geq (fp.abs a) mulmin) (fp.isNaN a))
)
(define-fun restrict_mul_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul rm a (fp32_underflow b mulmin)))
)

; multiplication, part 2
(define-fun restrict_mul_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.eq a zero) (fp.geq (fp.abs a) mulmin) (fp.isNaN a))
    (or (fp.eq b zero) (fp.geq (fp.abs b) mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul rm a b))
)

; multiplication f64, part 0
(define-fun restrict_mul_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun restrict_mul_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.mul rm (fp64_underflow a mulmin64) (fp64_underflow b mulmin64)))
)

; multiplication f64, part 1
(define-fun restrict_mul_f64_pre1 ((a Float64) (b Float64)) Bool
  (or (fp.eq a zero64) (fp.geq (fp.abs a) mulmin64) (fp.isNaN a))
)
(define-fun restrict_mul_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.mul rm a (fp64_underflow b mulmin64)))
)

; multiplication f64, part 2
(define-fun restrict_mul_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.eq a zero64) (fp.geq (fp.abs a) mulmin64) (fp.isNaN a))
    (or (fp.eq b zero64) (fp.geq (fp.abs b) mulmin64) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.mul rm a b))
)


;; RESTRICT DIVIDE PRE/POST

; divide, part 0
(define-fun restrict_div_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_div_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax)))
)

; divide, part 1
(define-fun restrict_div_f32_pre1 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_div_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax))) (not (= (fp.abs b) one)))
    (= ret (fp.div rm (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax)))
    (= (fp.abs ret) (fp.abs (fp.div rm (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax))))
  )
)

; divide, part 2
(define-fun restrict_div_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) mulmin) (fp.isNaN a))
  )
)
(define-fun restrict_div_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm (fp32_overflow a divmax) (fp32_clamp b mulmin divmax))) (not (= (fp.abs b) one)))
    (= ret (fp.div rm (fp32_overflow a divmax) (fp32_clamp b mulmin divmax)))
    (= (fp.abs ret) (fp.abs (fp.div rm (fp32_overflow a divmax) (fp32_clamp b mulmin divmax))))
  )
)

; divide, part 3
(define-fun restrict_div_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) mulmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm (fp32_overflow a divmax) (fp32_overflow b divmax))) (not (= (fp.abs b) one)))
    (= ret (fp.div rm (fp32_overflow a divmax) (fp32_overflow b divmax)))
    (= (fp.abs ret) (fp.abs (fp.div rm (fp32_overflow a divmax) (fp32_overflow b divmax))))
  )
)

; divide, part 4
(define-fun restrict_div_f32_pre4 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin) (fp.leq (fp.abs a) divmax)) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post4 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm a (fp32_overflow b divmax))) (not (= (fp.abs b) one)))
    (= ret (fp.div rm a (fp32_overflow b divmax)))
    (= (fp.abs ret) (fp.abs (fp.div rm a (fp32_overflow b divmax))))
  )
)

; divide, part 5
(define-fun restrict_div_f32_pre5 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin) (fp.leq (fp.abs a) divmax)) (fp.isNaN a))
    (or (fp.isZero b) (fp.isInfinite b) (and (fp.geq (fp.abs b) mulmin) (fp.leq (fp.abs b) divmax)) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post5 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm a b)) (not (= (fp.abs b) one)))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 6
(define-fun restrict_div_f32_pre6 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin) (fp.leq (fp.abs a) divmax)))
    (or (fp.isZero b) (fp.isInfinite b) (and (fp.geq (fp.abs b) mulmin) (fp.leq (fp.abs b) divmax)))
    (not (and (fp.isZero a) (fp.isZero b)))
    (not (and (fp.isInfinite a) (fp.isInfinite b)))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun restrict_div_f32_post6 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm a b)) (not (= (fp.abs b) one)))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 7
(define-fun restrict_div_f32_pre7 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin) (fp.leq (fp.abs a) divmax)))
    (or (fp.isZero b) (fp.isInfinite b) (and (fp.geq (fp.abs b) mulmin) (fp.leq (fp.abs b) divmax)))
    (not (fp.isInfinite a))
    (not (fp.isZero b))
  )
)
(define-fun restrict_div_f32_post7 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; division, part 8
(define-fun restrict_div_f32_pre8 ((a Float32) (b Float32)) Bool
  (and
    (and (fp.geq (fp.abs a) mulmin) (fp.leq (fp.abs a) divmax))
    (and (fp.geq (fp.abs b) mulmin) (fp.leq (fp.abs b) divmax))
  )
)
(define-fun restrict_div_f32_post8 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)
(define-fun restrict_div_f32_assume8_1 ((a Float32) (b Float32)) Bool
  (= 
    (fp.div rm
      (fp.div rm a ((_ to_fp 8 24) (concat (fp32_sign b) (fp32_exp b) zero23))) 
      ((_ to_fp 8 24) (concat #b001111111 (fp32_sig b)))) 
    (fp.div rm a b))
)

; division, part 9
(define-fun restrict_div_f32_pre9 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range (fp.abs a) divlo fltmax) (fp.isInfinite a) (fp.isZero a))
    (or (fp32_between b one two) (= b one))
  )
)
(define-fun restrict_div_f32_post9 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (=> (or (= b one) (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm a b)))
    (=> (not (or (= b one) (fp.isNormal (fp.div rm a b)))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; division, part 10
(define-fun restrict_div_f32_pre10 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range (fp.abs a) divlo fltmax) (fp.isInfinite a) (fp.isZero a))
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post10 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; division, part 11
(define-fun restrict_div_f32_pre11 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range (fp.abs a) divlo fltmax) (fp.isInfinite a))
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post11 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; division, part 12
(define-fun restrict_div_f32_pre12 ((a Float32) (b Float32)) Bool
  (and
    (fp32_range (fp.abs a) divlo fltmax)
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post12 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide f64, part 0
(define-fun restrict_div_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun restrict_div_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.div rm (fp64_clamp a mulmin64 divmax64) (fp64_clamp b mulmin64 divmax64)))
)

; divide f64, part 1
(define-fun restrict_div_f64_pre1 ((a Float64) (b Float64)) Bool
  true
)
(define-fun restrict_div_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (ite (and (fp.isNormal (fp.div rm (fp64_clamp a mulmin64 divmax64) (fp64_clamp b mulmin64 divmax64))) (not (= (fp.abs b) one64)))
    (= ret (fp.div rm (fp64_clamp a mulmin64 divmax64) (fp64_clamp b mulmin64 divmax64)))
    (= (fp.abs ret) (fp.abs (fp.div rm (fp64_clamp a mulmin64 divmax64) (fp64_clamp b mulmin64 divmax64))))
  )
)

; divide f64, part 2
(define-fun restrict_div_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) mulmin64) (fp.isNaN a))
  )
)
(define-fun restrict_div_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (ite (and (fp.isNormal (fp.div rm (fp64_overflow a divmax64) (fp64_clamp b mulmin64 divmax64))) (not (= (fp.abs b) one64)))
    (= ret (fp.div rm (fp64_overflow a divmax64) (fp64_clamp b mulmin64 divmax64)))
    (= (fp.abs ret) (fp.abs (fp.div rm (fp64_overflow a divmax64) (fp64_clamp b mulmin64 divmax64))))
  )
)

; divide f64, part 3
(define-fun restrict_div_f64_pre3 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) mulmin64) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) mulmin64) (fp.isNaN b))
  )
)
(define-fun restrict_div_f64_post3 ((ret Float64) (a Float64) (b Float64)) Bool
  (ite (and (fp.isNormal (fp.div rm (fp64_overflow a divmax64) (fp64_overflow b divmax64))) (not (= (fp.abs b) one64)))
    (= ret (fp.div rm (fp64_overflow a divmax64) (fp64_overflow b divmax64)))
    (= (fp.abs ret) (fp.abs (fp.div rm (fp64_overflow a divmax64) (fp64_overflow b divmax64))))
  )
)

; divide f64, part 4
(define-fun restrict_div_f64_pre4 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin64) (fp.leq (fp.abs a) divmax64)) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) mulmin64) (fp.isNaN b))
  )
)
(define-fun restrict_div_f64_post4 ((ret Float64) (a Float64) (b Float64)) Bool
  (ite (and (fp.isNormal (fp.div rm a (fp64_overflow b divmax64))) (not (= (fp.abs b) one64)))
    (= ret (fp.div rm a (fp64_overflow b divmax64)))
    (= (fp.abs ret) (fp.abs (fp.div rm a (fp64_overflow b divmax64))))
  )
)

; divide f64, part 5
(define-fun restrict_div_f64_pre5 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin64) (fp.leq (fp.abs a) divmax64)) (fp.isNaN a))
    (or (fp.isZero b) (fp.isInfinite b) (and (fp.geq (fp.abs b) mulmin64) (fp.leq (fp.abs b) divmax64)) (fp.isNaN b))
  )
)
(define-fun restrict_div_f64_post5 ((ret Float64) (a Float64) (b Float64)) Bool
  (ite (and (fp.isNormal (fp.div rm a b)) (not (= (fp.abs b) one64)))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide f64, part 6
(define-fun restrict_div_f64_pre6 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin64) (fp.leq (fp.abs a) divmax64)))
    (or (fp.isZero b) (fp.isInfinite b) (and (fp.geq (fp.abs b) mulmin64) (fp.leq (fp.abs b) divmax64)))
    (not (and (fp.isZero a) (fp.isZero b)))
    (not (and (fp.isInfinite a) (fp.isInfinite b)))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun restrict_div_f64_post6 ((ret Float64) (a Float64) (b Float64)) Bool
  (ite (and (fp.isNormal (fp.div rm a b)) (not (= (fp.abs b) one64)))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide f64, part 7
(define-fun restrict_div_f64_pre7 ((a Float64) (b Float64)) Bool
  (and
    (or (fp.isZero a) (fp.isInfinite a) (and (fp.geq (fp.abs a) mulmin64) (fp.leq (fp.abs a) divmax64)))
    (or (fp.isZero b) (fp.isInfinite b) (and (fp.geq (fp.abs b) mulmin64) (fp.leq (fp.abs b) divmax64)))
    (not (fp.isInfinite a))
    (not (fp.isZero b))
  )
)
(define-fun restrict_div_f64_post7 ((ret Float64) (a Float64) (b Float64)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; divide f64, part 8
(define-fun restrict_div_f64_pre8 ((a Float64) (b Float64)) Bool
  (and
    (and (fp.geq (fp.abs a) mulmin64) (fp.leq (fp.abs a) divmax64))
    (and (fp.geq (fp.abs b) mulmin64) (fp.leq (fp.abs b) divmax64))
  )
)
(define-fun restrict_div_f64_post8 ((ret Float64) (a Float64) (b Float64)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)
(define-fun restrict_div_f64_assume8_1 ((a Float64) (b Float64)) Bool
  (= 
    (fp.div rm
      (fp.div rm a ((_ to_fp 11 53) (concat (fp64_sign b) (fp64_exp b) zero52))) 
      ((_ to_fp 11 53) (concat #b001111111111 (fp64_sig b)))) 
    (fp.div rm a b))
)

; divide f64, part 9
(define-fun restrict_div_f64_pre9 ((a Float64) (b Float64)) Bool
  (and
    (or (fp64_range (fp.abs a) divlo64 dblmax) (fp.isInfinite a) (fp.isZero a))
    (or (fp64_between b one64 two64) (= b one64))
  )
)
(define-fun restrict_div_f64_post9 ((ret Float64) (a Float64) (b Float64)) Bool
  (and
    (=> (or (= b one64) (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm a b)))
    (=> (not (or (= b one64) (fp.isNormal (fp.div rm a b)))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; divide f64, part 10
(define-fun restrict_div_f64_pre10 ((a Float64) (b Float64)) Bool
  (and
    (or (fp64_range (fp.abs a) divlo64 dblmax) (fp.isInfinite a) (fp.isZero a))
    (fp64_between b one64 two64)
  )
)
(define-fun restrict_div_f64_post10 ((ret Float64) (a Float64) (b Float64)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; divide f64, part 11
(define-fun restrict_div_f64_pre11 ((a Float64) (b Float64)) Bool
  (and
    (or (fp64_range (fp.abs a) divlo64 dblmax) (fp.isInfinite a))
    (fp64_between b one64 two64)
  )
)
(define-fun restrict_div_f64_post11 ((ret Float64) (a Float64) (b Float64)) Bool
  (and
    (=> (fp.isNormal (fp.div rm a b)) (= ret (fp.div rm a b)))
    (=> (not (fp.isNormal (fp.div rm a b))) (= ret (fp.div rm (fp.abs a) (fp.abs b))))
  )
)

; divide f64, part 12
(define-fun restrict_div_f64_pre12 ((a Float64) (b Float64)) Bool
  (and
    (fp64_range (fp.abs a) divlo64 dblmax)
    (fp64_between b one64 two64)
  )
)
(define-fun restrict_div_f64_post12 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.div rm a b))
)


;; RESTRICT SQRT PRE/POST

; sqrt, part 0
(define-fun restrict_sqrt_f32_pre0 ((a Float32)) Bool
  true
)
(define-fun restrict_sqrt_f32_post0 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm (fp32_underflow a fltmin)))
)

; sqrt, part 1
(define-fun restrict_sqrt_f32_pre1 ((a Float32)) Bool
  (not (fp.isSubnormal (fp.sqrt rm a)))
)
(define-fun restrict_sqrt_f32_post1 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt, part 2
(define-fun restrict_sqrt_f32_pre2 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
  )
)
(define-fun restrict_sqrt_f32_post2 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt, part 3
(define-fun restrict_sqrt_f32_pre3 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf))
  )
)
(define-fun restrict_sqrt_f32_post3 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt, part 4
(define-fun restrict_sqrt_f32_pre4 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf))
    (fp.geq a zero)
  )
)
(define-fun restrict_sqrt_f32_post4 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt, part 5
(define-fun restrict_sqrt_f32_pre5 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf))
    (fp.gt a zero)
  )
)
(define-fun restrict_sqrt_f32_post5 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt, part 6
(define-fun restrict_sqrt_f32_pre6 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf))
    (fp.gt a zero)
    (not (fp32_ispow4 a))
  )
)
(define-fun restrict_sqrt_f32_post6 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt f64, part 0
(define-fun restrict_sqrt_f64_pre0 ((a Float64)) Bool
  true
)
(define-fun restrict_sqrt_f64_post0 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm (fp64_underflow a dblmin)))
)

; sqrt f64, part 1
(define-fun restrict_sqrt_f64_pre1 ((a Float64)) Bool
  (not (fp.isSubnormal (fp.sqrt rm a)))
)
(define-fun restrict_sqrt_f64_post1 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt f64, part 2
(define-fun restrict_sqrt_f64_pre2 ((a Float64)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
  )
)
(define-fun restrict_sqrt_f64_post2 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt f64, part 3
(define-fun restrict_sqrt_f64_pre3 ((a Float64)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf64))
  )
)
(define-fun restrict_sqrt_f64_post3 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt f64, part 4
(define-fun restrict_sqrt_f64_pre4 ((a Float64)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf64))
    (fp.geq a zero64)
  )
)
(define-fun restrict_sqrt_f64_post4 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt f64, part 5
(define-fun restrict_sqrt_f64_pre5 ((a Float64)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf64))
    (fp.gt a zero64)
  )
)
(define-fun restrict_sqrt_f64_post5 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

; sqrt f64, part 6
(define-fun restrict_sqrt_f64_pre6 ((a Float64)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt rm a)))
    (not (fp.isNaN a))
    (not (= a inf64))
    (fp.gt a zero64)
    (not (fp64_ispow4 a))
  )
)
(define-fun restrict_sqrt_f64_post6 ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

;; FULL ADDITION PRE/POST

; addition, part 0
(define-fun full_add_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun full_add_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.add rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; addition, part 1
(define-fun full_add_f32_pre1 ((a Float32) (b Float32)) Bool
  (not (fp.isSubnormal a))
)
(define-fun full_add_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.add rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; addition, part 2
(define-fun full_add_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
  )
)
(define-fun full_add_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.add rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; addition, part 3
(define-fun full_add_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.add rm a b)))
  )
)
(define-fun full_add_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.add rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; addition f64, part 0
(define-fun full_add_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun full_add_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.add rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)

; addition f64, part 1
(define-fun full_add_f64_pre1 ((a Float64) (b Float64)) Bool
  (not (fp.isSubnormal a))
)
(define-fun full_add_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.add rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)

; addition f64, part 2
(define-fun full_add_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
  )
)
(define-fun full_add_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.add rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)

; addition f64, part 3
(define-fun full_add_f64_pre3 ((a Float64) (b Float64)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.add rm a b)))
  )
)
(define-fun full_add_f64_post3 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.add rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)


;; FULL SUBTRACTION PRE/POST

; subtraction, part 0
(define-fun full_sub_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun full_sub_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.sub rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; subtraction, part 1
(define-fun full_sub_f32_pre1 ((a Float32) (b Float32)) Bool
  (not (fp.isSubnormal a))
)
(define-fun full_sub_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.sub rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; subtraction, part 2
(define-fun full_sub_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
  )
)
(define-fun full_sub_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.sub rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; subtraction, part 3
(define-fun full_sub_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.sub rm a b)))
  )
)
(define-fun full_sub_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.sub rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  )
)

; subtraction f64, part 0
(define-fun full_sub_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun full_sub_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.sub rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)

; subtraction f64, part 1
(define-fun full_sub_f64_pre1 ((a Float64) (b Float64)) Bool
  (not (fp.isSubnormal a))
)
(define-fun full_sub_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.sub rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)

; subtraction f64, part 2
(define-fun full_sub_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
  )
)
(define-fun full_sub_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.sub rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)

; subtraction f64, part 3
(define-fun full_sub_f64_pre3 ((a Float64) (b Float64)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.sub rm a b)))
  )
)
(define-fun full_sub_f64_post3 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.sub rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin)
  )
)


;; FULL MULTIPLICATION PRE/POST

; multiplication, part 0
(define-fun full_mul_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun full_mul_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
       (fp32_underflow (fp.mul rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin))
    ; Take into account double rounding issue
    (and
      (= ret (copysign zero (fp.mul rm a b)))
      (= (fp.abs (fp.mul rm a b)) fltmin)
    )
  )
)

; multiplication, part 1
(define-fun full_mul_f32_pre1 ((a Float32) (b Float32)) Bool
  (not (fp.isSubnormal a))
)
(define-fun full_mul_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
       (fp32_underflow (fp.mul rm a (fp32_underflow b fltmin)) fltmin))
    ; Take into account double rounding issue
    (and
      (= ret (copysign zero (fp.mul rm a b)))
      (= (fp.abs (fp.mul rm a b)) fltmin)
    )
  )
)

; multiplication, part 2
(define-fun full_mul_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
  )
)
(define-fun full_mul_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
       (fp32_underflow (fp.mul rm a b) fltmin))
    ; Take into account double rounding issue
    (and
      (= ret (copysign zero (fp.mul rm a b)))
      (= (fp.abs (fp.mul rm a b)) fltmin)
    )
  )
)
(define-fun full_mul_f32_assume2_1 ((a Float32) (b Float32)) Bool
  (ite
    (not (fp.lt
      (fp.abs (fp.mul rm (fp.mul rm a ((_ to_fp 8 24) #x7e800000)) b))
      one))
    (not (fp.isSubnormal (fp.mul rm a b)))
    (or (fp.isZero (fp32_underflow (fp.mul rm a b) fltmin)) (= (fp.abs (fp.mul rm a b)) fltmin))
  )
)

; multiplication, part 3
(define-fun full_mul_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.mul rm a b)))
  )
)
(define-fun full_mul_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.mul rm a b) fltmin)
  )
)

; multiplication f64, part 0
(define-fun full_mul_f64_pre0 ((a Float64) (b Float64)) Bool
  true
)
(define-fun full_mul_f64_post0 ((ret Float64) (a Float64) (b Float64)) Bool
  (or
    (= ret
       (fp64_underflow (fp.mul rm (fp64_underflow a dblmin) (fp64_underflow b dblmin)) dblmin))
    ; Take into account double rounding issue
    (and
      (= ret (fp64_copysign zero64 (fp.mul rm a b)))
      (= (fp.abs (fp.mul rm a b)) dblmin)
    )
  )
)

; multiplication f64, part 1
(define-fun full_mul_f64_pre1 ((a Float64) (b Float64)) Bool
  (not (fp.isSubnormal a))
)
(define-fun full_mul_f64_post1 ((ret Float64) (a Float64) (b Float64)) Bool
  (or
    (= ret
       (fp64_underflow (fp.mul rm a (fp64_underflow b dblmin)) dblmin))
    ; Take into account double rounding issue
    (and
      (= ret (fp64_copysign zero64 (fp.mul rm a b)))
      (= (fp.abs (fp.mul rm a b)) dblmin)
    )
  )
)

; multiplication f64, part 2
(define-fun full_mul_f64_pre2 ((a Float64) (b Float64)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
  )
)
(define-fun full_mul_f64_post2 ((ret Float64) (a Float64) (b Float64)) Bool
  (or
    (= ret
       (fp64_underflow (fp.mul rm a b) dblmin))
    ; Take into account double rounding issue
    (and
      (= ret (fp64_copysign zero64 (fp.mul rm a b)))
      (= (fp.abs (fp.mul rm a b)) dblmin)
    )
  )
)
(define-fun full_mul_f64_assume2_1 ((a Float64) (b Float64)) Bool
  (ite
    (not (fp.lt
      (fp.abs (fp.mul rm (fp.mul rm a (fp64_cast #x7fd0000000000000)) b))
      one64))
    (not (fp.isSubnormal (fp.mul rm a b)))
    (or (fp.isZero (fp64_underflow (fp.mul rm a b) dblmin)) (= (fp.abs (fp.mul rm a b)) dblmin))
  )
)

; multiplication f64, part 3
(define-fun full_mul_f64_pre3 ((a Float64) (b Float64)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.mul rm a b)))
  )
)
(define-fun full_mul_f64_post3 ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret
    (fp64_underflow (fp.mul rm a b) dblmin)
  )
)

;; FULL DIVIDE PRE/POST

; divide, part 0
(define-fun full_div_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun full_div_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
      (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
    )
    (and
      (= ret (copysign zero (fp.div rm a b)))
      (= (fp.abs (fp.div rm a b)) fltmin)
    )
  )
)

; divide, part 1
(define-fun full_div_f32_pre1 ((a Float32) (b Float32)) Bool
  true
)
(define-fun full_div_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    ; (ite (and (fp.isNormal ret) (not (= (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin) one)))
    ;   (= ret
    ;     (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
    ;   )
    ;   (= 
    ;     (fp.abs ret)
    ;     (fp.abs (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin))
    ;   )
    ; )
    (= 
      (fp.abs ret)
      (fp.abs (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)))
    (and
      (fp.isZero ret)
      (= (fp.abs (fp.div rm a b)) fltmin)
    )
  )
)

; divide, part 2
(define-fun full_div_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
  )
)
(define-fun full_div_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    ; (ite (and (fp.isNormal ret) (not (= (fp32_underflow (fp.div rm a (fp32_underflow b fltmin)) fltmin) one)))
    ;   (= ret
    ;     (fp32_underflow (fp.div rm a (fp32_underflow b fltmin)) fltmin)
    ;   )
    ; )
    (= 
      (fp.abs ret)
      (fp.abs (fp32_underflow (fp.div rm a (fp32_underflow b fltmin)) fltmin))
    )
    (and
      (fp.isZero ret)
      (= (fp.abs (fp.div rm a b)) fltmin)
    )
  )
)

; divide, part 3
(define-fun full_div_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))
  )
)
(define-fun full_div_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    ; (ite (and (fp.isNormal ret) (not (= (fp32_underflow (fp.div rm a b) fltmin) one)))
    ;   (= ret
    ;     (fp32_underflow (fp.div rm a b) fltmin)
    ;   )
    ;   (= 
    ;     (fp.abs ret)
    ;     (fp.abs (fp32_underflow (fp.div rm a b) fltmin))
    ;   )
    ; )
    (= 
      (fp.abs ret)
      (fp.abs (fp32_underflow (fp.div rm a b) fltmin))
    )
    (and
      (fp.isZero ret)
      (= (fp.abs (fp.div rm a b)) fltmin)
    )
  )
)
(define-fun full_div_f32_assume3 ((a Float32) (b Float32)) Bool
  (=>
    (and (fp.gt (fp.abs a) forth) (fp.gt (fp.abs b) forth))
    (= (fp.div rm a b)
       (fp.div rm (fp.mul rm a thirtytwoth)
                  (fp.mul rm b thirtytwoth))))
)

; divide, part 4
(define-fun full_div_f32_pre4 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))

    (or
      (or (fp.leq (fp.abs a) forth)
          (fp.leq (fp.abs b) forth))
      (and (or (fp.isInfinite a) (fp.leq (fp.abs a) fltmax32))
           (or (fp.isInfinite b) (fp.leq (fp.abs b) fltmax32)))
      (or (fp.isNaN a) (fp.isNaN b))
    )
  )
)
(define-fun full_div_f32_post4 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    ; (ite (and (fp.isNormal ret) (not (= (fp32_underflow (fp.div rm a b) fltmin) one)))
    ;   (= ret
    ;     (fp32_underflow (fp.div rm a b) fltmin)
    ;   )
    ;   (= 
    ;     (fp.abs ret)
    ;     (fp.abs (fp32_underflow (fp.div rm a b) fltmin))
    ;   )
    ; )
    (= 
      (fp.abs ret)
      (fp.abs (fp32_underflow (fp.div rm a b) fltmin))
    )
    (and
      (fp.isZero ret)
      (= (fp.abs (fp.div rm a b)) fltmin)
    )
  )
)
(define-fun full_div_f32_assume4 ((a Float32) (b Float32)) Bool
  (=>
    (and (fp.gt (fp.abs a) four) (fp.lt (fp.abs b) one))
    (= (fp.div rm a b)
       (fp.mul rm (fp.div rm a (fp.mul rm b four)) four))
  )
)

; divide, part 5
(define-fun full_div_f32_pre5 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))

    (or
      (fp.leq (fp.abs a) forth)
      (and (or (fp.isInfinite a) (fp.leq (fp.abs a) fltmax32))
           (or (fp.isInfinite b) (fp.leq (fp.abs b) fltmax32)))
      (and (fp.gt (fp.abs a) four)
           (and
             (or (fp.geq (fp.abs b) fltmin4) (fp.isZero b))
             (fp.lt (fp.abs b) four) 
           )
           (=>
             (fp.gt (fp.abs b) one)
             (or (fp.isInfinite a) (fp.leq (fp.abs a) fltmax32))
           )
           (or (fp.isInfinite b) (fp.leq (fp.abs b) fltmax32))
      )
      (or (fp.isNaN a) (fp.isNaN b))
    )
  )
)
(define-fun full_div_f32_post5 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (ite (fp.isNormal ret)
      (= 
        ret
        (fp32_underflow (fp.div rm a b) fltmin)
      )
      (= 
        (fp.abs ret)
        (fp.abs (fp32_underflow (fp.div rm a b) fltmin))
      )
    )
    (and
      (fp.isZero ret)
      (= (fp.abs (fp.div rm a b)) fltmin)
    )
  )
)
(define-fun full_div_f32_assume5_1 ((a Float32) (b Float32)) Bool
  (and
    (=> (fp.isZero (fp.div rm a b)) (or (fp.isZero a) (fp.isInfinite b)))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)

; divide, part 6
(define-fun full_div_f32_pre6 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (= (fp.abs a) onePt5) (fp.geq (fp.abs a) (fp.mul RNE (fp.mul RNE divmin divoff) divoff2)))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin))
    (=> (and (fp.gt (fp.abs a) (fp.mul RNE (fp.mul RNE fltmax32 divoff) divoff2)) (fp.gt (fp.abs b) fltmax32)) (or (fp.isInfinite a) (fp.isInfinite b)))
    (=> (and (fp.gt (fp.abs a) (fp.mul RNE (fp.mul RNE four divoff) divoff2)) (fp.lt (fp.abs b) divmin4)) (fp.isZero b))
    (not (and (fp.isInfinite a) (fp.isInfinite b)))
    (not (and (fp.isZero a) (fp.isZero b)))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post6 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm a b)) (not (fp32_ispow2 b)))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 7
(define-fun full_div_f32_pre7 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))

    (or
      (fp.leq (fp.abs a) forth)
      (and (or (fp.isInfinite a) (fp.leq a fltmax32))
           (or (fp.isInfinite b) (fp.leq b fltmax32)))
      (and (fp.gt (fp.abs a) four)
           (and
             (or (fp.geq (fp.abs b) fltmin4) (fp.isZero b))
             (fp.lt (fp.abs b) four) 
           )
      )
      (or (fp.isNaN a) (fp.isNaN b))
    )
    (=> (fp.isZero (fp.div rm a b)) (or (fp.isZero a) (fp.isInfinite b)))

    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post7 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 8
(define-fun full_div_f32_pre8 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))

    (or
      (fp.leq (fp.abs a) forth)
      (and (or (fp.isInfinite a) (fp.leq a fltmax32))
           (or (fp.isInfinite b) (fp.leq b fltmax32)))
      (and (fp.gt (fp.abs a) four)
           (and
             (or (fp.geq (fp.abs b) fltmin4) (fp.isZero b))
             (fp.lt (fp.abs b) four) 
           )
      )
      (or (fp.isNaN a) (fp.isNaN b))
    )
    (=> (fp.isZero (fp.div rm a b)) (or (fp.isZero a) (fp.isInfinite b)))

    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isSubnormal b))
    (not (fp.isNaN b))
    (not (fp.isSubnormal (fp.div rm a b)))
    (not (and (fp.isZero a) (fp.isZero b)))
    (not (and (fp.isInfinite a) (fp.isInfinite b)))
  )
)
(define-fun full_div_f32_post8 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 9
(define-fun full_div_f32_pre9 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))

    (or
      (fp.leq (fp.abs a) forth)
      (and (or (fp.isInfinite a) (fp.leq a fltmax32))
           (or (fp.isInfinite b) (fp.leq b fltmax32)))
      (and (fp.gt (fp.abs a) four)
           (and
             (or (fp.geq (fp.abs b) fltmin4) (fp.isZero b))
             (fp.lt (fp.abs b) four) 
           )
      )
      (or (fp.isNaN a) (fp.isNaN b))
    )
    (=> (fp.isZero (fp.div rm a b)) (or (fp.isZero a) (fp.isInfinite b)))
    
    (not (fp.isInfinite a))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isSubnormal b))
    (not (fp.isNaN b))
    (not (fp.isZero b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post9 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 10
(define-fun full_div_f32_pre10 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (fp.geq (fp.abs a) divmin) (fp.isNaN a))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin) (fp.isNaN b))

    (or
      (fp.leq (fp.abs a) forth)
      (and (or (fp.isInfinite a) (fp.leq a fltmax32))
           (or (fp.isInfinite b) (fp.leq b fltmax32)))
      (and (fp.gt (fp.abs a) four)
           (and
             (or (fp.geq (fp.abs b) fltmin4) (fp.isZero b))
             (fp.lt (fp.abs b) four) 
           )
      )
      (or (fp.isNaN a) (fp.isNaN b))
    )
    (=> (fp.isZero (fp.div rm a b)) (or (fp.isZero a) (fp.isInfinite b)))

    (not (fp.isInfinite a))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isZero a))
    (not (fp.isInfinite b))
    (not (fp.isSubnormal b))
    (not (fp.isNaN b))
    (not (fp.isZero b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post10 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)
(define-fun full_div_f32_assume10_1 ((a Float32) (b Float32)) Bool
  (not (fp.isSubnormal  
    (fp.div rm
      (fp.div rm a ((_ to_fp 8 24) (concat (fp32_sign b) (fp32_exp b) zero23))) 
      ((_ to_fp 8 24) (concat #b001111111 (fp32_sig b))))))
)
(define-fun full_div_f32_assume10_2 ((a Float32) (b Float32)) Bool
  (= 
    (fp.div rm
      (fp.div rm a ((_ to_fp 8 24) (concat (fp32_sign b) (fp32_exp b) zero23))) 
      ((_ to_fp 8 24) (concat #b001111111 (fp32_sig b)))) 
    (fp.div rm a b))
)

; divide, part 11
(define-fun full_div_f32_pre11 ((a Float32) (b Float32)) Bool
  (and
    (fp.isPositive b)
    (= (fp32_exp b) (_ bv127 8))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp_isspec_f32 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post11 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 12
(define-fun full_div_f32_pre12 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp_isspec_f32 b))
    (not (= (fp.abs b) one))
    (= (fp32_exp b) (_ bv127 8))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post12 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 13
(define-fun full_div_f32_pre13 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isZero a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post13 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; divide, part 14
(define-fun full_div_f32_pre14 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isInfinite a))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isZero a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post14 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; division, part 15
(define-fun full_div_f32_pre15 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (= (fp.abs a) onePt5) (fp.geq (fp.abs a) (fp.mul RNE (fp.mul RNE divmin divoff) divoff2)))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin))
    (=> (and (fp.gt (fp.abs a) (fp.mul RNE (fp.mul RNE fltmax32 divoff) divoff2)) (fp.gt (fp.abs b) fltmax32)) (or (fp.isInfinite a) (fp.isInfinite b)))
    (=> (and (fp.gt (fp.abs a) (fp.mul RNE (fp.mul RNE four divoff) divoff2)) (fp.lt (fp.abs b) divmin4)) (fp.isZero b))
    (not (fp.isInfinite a))
    (not (fp.isZero b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post15 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; division, part 16
(define-fun full_div_f32_pre16 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isZero a) (= (fp.abs a) onePt5) (fp.geq (fp.abs a) (fp.mul RNE (fp.mul RNE divmin divoff) divoff2)))
    (or (fp.isZero b) (fp.geq (fp.abs b) divmin))
    (=> (and (fp.gt (fp.abs a) (fp.mul RNE (fp.mul RNE fltmax32 divoff) divoff2)) (fp.gt (fp.abs b) fltmax32)) (or (fp.isInfinite a) (fp.isInfinite b)))
    (=> (and (fp.gt (fp.abs a) (fp.mul RNE (fp.mul RNE four divoff) divoff2)) (fp.lt (fp.abs b) divmin4)) (fp.isZero b))
    (not (fp.isInfinite a))
    (not (fp.isInfinite b))
    (not (fp.isZero a))
    (not (fp.isZero b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post16 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)
(define-fun full_div_f32_assume16 ((a Float32) (b Float32)) Bool
  (= 
    (fp.div rm
      (fp.div rm a ((_ to_fp 8 24) (concat (fp32_sign b) (fp32_exp b) zero23))) 
      ((_ to_fp 8 24) (concat #b001111111 (fp32_sig b)))) 
    (fp.div rm a b))
)

; division, part 17
(define-fun full_div_f32_pre17 ((a Float32) (b Float32)) Bool
  (and
    (= (fp32_exp b) (_ bv127 8))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp_isspec_f32 b))
    (not (fp.isSubnormal (fp.div rm a b)))
    (fp.isPositive b)
  )
)
(define-fun full_div_f32_post17 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (and (fp.isNormal (fp.div rm a b)))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; division, part 18
(define-fun full_div_f32_pre18 ((a Float32) (b Float32)) Bool
  (and
    (= (fp32_exp b) (_ bv127 8))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post18 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; division, part 19
(define-fun full_div_f32_pre19 ((a Float32) (b Float32)) Bool
  (and
    (= (fp32_exp b) (_ bv127 8))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isZero a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post19 ((ret Float32) (a Float32) (b Float32)) Bool
  (ite (fp.isNormal (fp.div rm a b))
    (= ret (fp.div rm a b))
    (= (fp.abs ret) (fp.abs (fp.div rm a b)))
  )
)

; division, part 20
(define-fun full_div_f32_pre20 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isInfinite a))
    (not (fp.isSubnormal a))
    (not (fp.isNaN a))
    (not (fp.isZero a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post20 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

;; PRIMITIVE OPERATION SAFETY

; fadd
(define-fun fadd32_pre ((a Float32) (b Float32)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	   (fp.isSubnormal (fp.add rm a b)))
  )
)
(define-fun fadd32_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add rm a b))
)
(define-fun fadd64_pre ((a Float64) (b Float64)) Bool
  (not (or (fp.isSubnormal a)
           (fp.isSubnormal b)
	   (fp.isSubnormal (fp.add rm a b)))
  )
)
(define-fun fadd64_post ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.add rm a b))
)

; fsub
(define-fun fsub32_pre ((a Float32) (b Float32)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	   (fp.isSubnormal (fp.sub rm a b)))
  )
)
(define-fun fsub32_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub rm a b))
)
(define-fun fsub64_pre ((a Float64) (b Float64)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	   (fp.isSubnormal (fp.sub rm a b)))
  )
)
(define-fun fsub64_post ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.sub rm a b))
)

; fmul
(define-fun fmul32_pre ((a Float32) (b Float32)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	         (fp.isSubnormal (fp.mul rm a b))
       )
  )
)
(define-fun fmul32_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul rm a b))
)
(define-fun fmul64_pre ((a Float64) (b Float64)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	         (fp.isSubnormal (fp.mul rm a b))
       )
  )
)
(define-fun fmul64_post ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.mul rm a b))
)

; fdiv exponent
(define-fun fdiv32exp_pre ((a Float32) (b Float32)) Bool
  (and
    (not (fp_isspec_f32 a))
    (not (fp_isspec_f32 b))
    (fp32_ispow2 b)
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun fdiv32exp_post ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= ret (fp.div rm a b))
  )
)
(define-fun fdiv64exp_pre ((a Float64) (b Float64)) Bool
  (and
    (not (fp_isspec_f64 a))
    (not (fp_isspec_f64 b))
    (fp64_ispow2 b)
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun fdiv64exp_post ((ret Float64) (a Float64) (b Float64)) Bool
  (and
    (= ret (fp.div rm a b))
  )
)

; fdiv significand
(define-fun fdiv32sig_pre ((a Float32) (b Float32)) Bool
  (and
    (not (fp_isspec_f32 a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun fdiv32sig_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)
(define-fun fdiv64sig_pre ((a Float64) (b Float64)) Bool
  (and
    (not (fp_isspec_f64 a))
    (not (fp_isspec_f64 b))
    (not (fp64_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun fdiv64sig_post ((ret Float64) (a Float64) (b Float64)) Bool
  (= ret (fp.div rm a b))
)

; fsqrt
(define-fun fsqrt32_pre ((a Float32)) Bool
  (and
    (fp.geq a zero)
    (not (= a inf))
    (not (fp32_ispow4 a))
    (not (fp.isSubnormal (fp.sqrt rm a)))
  )
)
(define-fun fsqrt32_post ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt rm a))
)
(define-fun fsqrt64_pre ((a Float64)) Bool
  (and
    (fp.geq a zero64)
    (not (= a inf64))
    (not (fp64_ispow4 a))
    (not (fp.isSubnormal (fp.sqrt rm a)))
  )
)
(define-fun fsqrt64_post ((ret Float64) (a Float64)) Bool
  (= ret (fp.sqrt rm a))
)

(define-fun fp_exponent ((a Float32)) (_ BitVec 8)
  ((_ extract 30 23) (to_ieee_bv a))
)

; Axiom experiment
; (assert (forall ((xxx Float32) (yyy Float32)) (=> (not (fp.lt (fp.mul rm (fp.mul rm xxx muloff) yyy) one)) (not (fp.isSubnormal (fp.mul rm xxx yyy))))))

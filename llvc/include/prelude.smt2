(set-logic QF_FPBV)

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
(define-const divmax Float32 ((_ to_fp 8 24) #x5e800000))
;(define-const divmax Float32 ((_ to_fp 8 24) #x5e800001)) ; FAILS!
;(define-const sqrtmin Float32 ((_ to_fp 8 24) #x00800000))
(define-const sqrtmin Float32 ((_ to_fp 8 24) #x007fffff)) ; FAILS!
(define-const zero Float32 ((_ to_fp 8 24) #x00000000))
(define-const one Float32 ((_ to_fp 8 24) #x3f800000))
(define-const two Float32 ((_ to_fp 8 24) #x40000000))
(define-const four Float32 ((_ to_fp 8 24) #x40800000))
(define-const forth Float32 ((_ to_fp 8 24) #x3e800000))
(define-const inf Float32 ((_ to_fp 8 24) #x7f800000))

(define-const fltmin Float32 ((_ to_fp 8 24) #x00800000))
(define-const fltmin4 Float32 ((_ to_fp 8 24) #x01800000))
(define-const fltmax Float32 ((_ to_fp 8 24) #x7f7fffff))
(define-const fltmax4 Float32 ((_ to_fp 8 24) #x7e7fffff))
(define-const divlo Float32 ((_ to_fp 8 24) #x01000000))
(define-const divcmp Float32 ((_ to_fp 8 24) #x40800000))

(define-const zero1 (_ BitVec 1) (_ bv0 1))
(define-const zero23 (_ BitVec 23) (_ bv0 23))
(define-const one8 (_ BitVec 8) (_ bv128 8))
(define-const bias (_ BitVec 8) (_ bv127 8))
(define-const muloff Float32 ((_ to_fp 8 24) #x7e800000))
(define-const divoff Float32 ((_ to_fp 8 24) #x7e800000))

(define-const one_point_zero Float32 ((_ to_fp 8 24) roundTowardZero 1.0))
(define-const zero_point_zero Float32 ((_ to_fp 8 24) roundTowardZero 0.0))

; (define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) (_ BitVec 32) a))
;    ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb))

;
(define-fun plus ((a Int) (b Int)) Int 
  (+ a b)
) 
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

; check if a value is a power-of-two
(define-fun fp32_ispow2 ((v Float32)) Bool
  (= #x00000000 (bvand (to_ieee_bv v) #x007fffff))
)

; check if a value is a power-of-four
(define-fun fp32_ispow4 ((v Float32)) Bool
  (= #x00800000 (bvand (to_ieee_bv v) #x00ffffff))
)

(define-fun fp32_exp ((v Float32)) (_ BitVec 8)
  ((_ extract 30 23) (to_ieee_bv v))
)

(define-fun fp32_sig ((v Float32)) (_ BitVec 23)
  ((_ extract 22 0) (to_ieee_bv v))
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

; clamp a value to the range `[lo,hi]`, over/under-flowing as needed
(define-fun fp32_clamp ((x Float32) (lo Float32) (hi Float32)) Float32
  (fp32_overflow (fp32_underflow x lo) hi)
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

; return true if inside a range, exclusive
(define-fun fp32_between ((val Float32) (lo Float32) (hi Float32)) Bool
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

; addition f32, part 0
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
  (and
    (or (fp.isPositive a) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul rm (fp32_underflow a mulmin) (fp32_underflow b mulmin)))
)

; multiplication, part 2
(define-fun restrict_mul_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul rm a (fp32_underflow b mulmin)))
)

; multiplication, part 3
(define-fun restrict_mul_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (= b zero) (fp.geq b mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
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
  (and
    (or (fp.isPositive a) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax)))
)

; divide, part 2
(define-fun restrict_div_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm (fp32_overflow a divmax) (fp32_clamp b mulmin divmax)))
)

; divide, part 3
(define-fun restrict_div_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (= b zero) (fp.geq b mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm (fp32_overflow a divmax) (fp32_overflow b divmax)))
)

; divide, part 4
(define-fun restrict_div_f32_pre4 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (= a inf) (and (fp.geq a mulmin) (fp.leq a divmax)) (fp.isNaN a))
    (or (= b zero) (fp.geq b mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post4 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a (fp32_overflow b divmax)))
)

; divide, part 5
(define-fun restrict_div_f32_pre5 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (= a inf) (and (fp.geq a mulmin) (fp.leq a divmax)) (fp.isNaN a))
    (or (= b zero) (= b inf) (and (fp.geq b mulmin) (fp.leq b divmax)) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post5 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 6
(define-fun restrict_div_f32_pre6 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (= a inf) (and (fp.geq a mulmin) (fp.leq a divmax)))
    (or (= b zero) (= b inf) (and (fp.geq b mulmin) (fp.leq b divmax)))
    (not (and (= a zero) (= b zero)))
    (not (and (= a inf) (= b inf)))
  )
)
(define-fun restrict_div_f32_post6 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 7
(define-fun restrict_div_f32_pre7 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (= a inf) (and (fp.geq a mulmin) (fp.leq a divmax)))
    (or (= b zero) (= b inf) (and (fp.geq b mulmin) (fp.leq b divmax)))
    (not (= a inf))
    (not (= b zero))
  )
)
(define-fun restrict_div_f32_post7 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; division, part 8
(define-fun restrict_div_f32_pre8 ((a Float32) (b Float32)) Bool
  (and
    (and (fp.geq a mulmin) (fp.leq a divmax))
    (and (fp.geq b mulmin) (fp.leq b divmax))
  )
)
(define-fun restrict_div_f32_post8 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)
(define-fun restrict_div_f32_assume8 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; division, part 9
(define-fun restrict_div_f32_pre9 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range a divlo fltmax) (= a inf) (= a zero))
    (or (fp32_between b one two) (= b one))
  )
)
(define-fun restrict_div_f32_post9 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)
(define-fun restrict_div_f32_assume9 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; division, part 10
(define-fun restrict_div_f32_pre10 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range a divlo fltmax) (= a inf) (= a zero))
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post10 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; division, part 11
(define-fun restrict_div_f32_pre11 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range a divlo fltmax) (= a inf))
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post11 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; division, part 12
(define-fun restrict_div_f32_pre12 ((a Float32) (b Float32)) Bool
  (and
    (fp32_range a divlo fltmax)
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post12 ((ret Float32) (a Float32) (b Float32)) Bool
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
  (and
    (or (fp.isPositive a) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun full_mul_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
       (fp32_underflow (fp.mul rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin))
    ; Take into account double rounding issue
    (and
      (= ret zero)
      (= (fp.mul rm a b) fltmin)
    )
  )
)

; multiplication, part 2
(define-fun full_mul_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin)(fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun full_mul_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
       (fp32_underflow (fp.mul rm a (fp32_underflow b fltmin)) fltmin))
    ; Take into account double rounding issue
    (and
      (= ret zero)
      (= (fp.mul rm a b) fltmin)
    )
  )
)

; multiplication, part 3
(define-fun full_mul_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (fp.isNaN a))
    (or (= b zero) (fp.geq b fltmin) (fp.isNaN b))
  )
)
(define-fun full_mul_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
       (fp32_underflow (fp.mul rm a b) fltmin))
    ; Take into account double rounding issue
    (and
      (= ret zero)
      (= (fp.mul rm a b) fltmin)
    )
  )
)
(define-fun full_mul_f32_assume3_1 ((a Float32) (b Float32)) Bool
  (not (fp.isSubnormal (fp.mul rm a b)))
)
(define-fun full_mul_f32_assume3_2 ((ret Float32) (a Float32) (b Float32)) Bool
  (=>
    (not
      (= ret (fp32_underflow (fp.mul rm a b) fltmin)))
    (= (fp.mul rm a b) fltmin)
  )
)

; multiplication, part 4
(define-fun full_mul_f32_pre4 ((a Float32) (b Float32)) Bool
  (and
    (not (fp.isSubnormal a))
    (not (fp.isSubnormal b))
    (not (fp.isSubnormal (fp.mul rm a b)))
  )
)
(define-fun full_mul_f32_post4 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow (fp.mul rm a b) fltmin)
  )
  ; (or
  ;   (= ret
  ;      (fp32_underflow (fp.mul rm a b) fltmin))
  ;   ; Take into account double rounding issue
  ;   (and
  ;     (= ret zero)
  ;     (= (fp.mul rm a b) fltmin)
  ;   )
  ; )
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
    (and (= ret (copysign zero (fp.div rm a b)))
         (= (fp.div rm (fp.abs a) (fp.abs b)) fltmin))
  )
)

; divide, part 1
(define-fun full_div_f32_pre1 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isPositive a) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun full_div_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  ; (= ret
  ;   (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
  ; )
  (or
    (= ret
      (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
    )
    (and (= ret zero)
         (= (fp.div rm a b) fltmin))
  )
)

; divide, part 2
(define-fun full_div_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun full_div_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
      (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
    )
    (and (= ret zero)
         (= (fp.div rm a b) fltmin))
  )
)

; divide, part 3
(define-fun full_div_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (fp.isNaN a))
    (or (= b zero) (fp.geq b fltmin) (fp.isNaN b))
  )
)
(define-fun full_div_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
      (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
    )
    (and (= ret zero)
         (= (fp.div rm a b) fltmin))
  )
)
(define-fun full_div_f32_assume3 ((ret Float32) (a Float32) (b Float32)) Bool
  (or
    (= ret
      (fp32_underflow (fp.div rm (fp32_underflow a fltmin) (fp32_underflow b fltmin)) fltmin)
    )
    (and (= ret zero)
         (= (fp.div rm a b) fltmin))
  )
)

; divide, part 4
(define-fun full_div_f32_pre4 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (fp.isNaN a) (= a inf))
    (or (= b zero) (fp.isNaN b) (= b inf)
      (ite (and (fp.gt a one) (fp.lt b one))
        (fp.geq b fltmin4)
        (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
      )
    )
  )
)
(define-fun full_div_f32_post4 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow
      (fp.div rm a b)
      (ite (and (fp.lt a four) (fp.gt b forth)) fltmin4 fltmin)
    )
  )
)
(define-fun full_div_f32_assume4 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret
    (fp32_underflow
      (fp.div rm a b)
      (ite (and (fp.lt a four) (fp.gt b forth)) fltmin4 fltmin)
    )
  )
)

; divide, part 5
(define-fun full_div_f32_pre5 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a (fp.mul rm fltmin divoff)) (= a inf))
    (or (= b zero) (= b inf)
      (ite (and (fp.gt a (fp.mul rm one divoff)) (fp.lt b one))
        (fp.geq b fltmin4)
        (ite (and (fp.lt a (fp.mul rm four divoff)) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
      )
    )
    (not (and (= a inf) (= b inf)))
    (not (and (= a zero) (= b zero)))
  )
)
(define-fun full_div_f32_post5 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)

; divide, part 6
(define-fun full_div_f32_pre6 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (fp.isNaN a) (= a inf))
    (or (= b zero) (fp.isNaN b) (= b inf)
      (ite (and (fp.gt a one) (fp.lt b one))
        (fp.geq b fltmin4)
        (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
      )
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (or (= b inf) (and (= a zero) (= b one))))
  )
)
(define-fun full_div_f32_post6 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 7
(define-fun full_div_f32_pre7 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (= a inf))
    (or (= b zero) (= b inf)
      (ite (and (fp.gt a one) (fp.lt b one))
        (fp.geq b fltmin4)
        (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
      )
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (or (= b inf) (and (= a zero) (= b one))))
    (not (and (= a inf) (= b inf)))
    (not (and (= a zero) (= b zero)))
  )
)
(define-fun full_div_f32_post7 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 8
(define-fun full_div_f32_pre8 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a fltmin) (= a inf))
    (or (= b inf)
      (ite (and (fp.gt a one) (fp.lt b one))
        (fp.geq b fltmin4)
        (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
      )
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (or (= b inf) (and (= a zero) (= b one))))
    (not (= a inf))
  )
)
(define-fun full_div_f32_post8 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 9
(define-fun full_div_f32_pre9 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (and (= a zero) (= b one)))
    (not (= a inf))
    (not (= b inf))
  )
)
(define-fun full_div_f32_post9 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)
(define-fun full_div_f32_assume9 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)
(define-fun full_div_f32_assume9_1 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (and (= a zero) (= b one)))
    (not (= b inf))
    (= (fp32_exp b) (_ bv127 8))
  )
)

; divide, part 10
(define-fun full_div_f32_pre10 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (and (= a zero) (= b one)))
    (not (= b inf))
    (= (fp32_exp b) (_ bv127 8))
  )
)
(define-fun full_div_f32_post10 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)
(define-fun full_div_f32_assume10 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 11
(define-fun full_div_f32_pre11 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (and (= a zero) (= b one)))
    (not (= b inf))
    (not (fp32_ispow2 b))
  )
)
(define-fun full_div_f32_post11 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 12
(define-fun full_div_f32_pre12 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (and (= a zero) (= b one)))
    (not (= b inf))
    (not (fp32_ispow2 b))
  )
)
(define-fun full_div_f32_post12 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 13
(define-fun full_div_f32_pre13 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp.isSubnormal (fp.div rm a b)))
    (=> (= (fp.div rm a b) zero) (and (= a zero) (= b one)))
    (not (= a inf))
    (not (= b inf))
    (not (fp32_ispow2 b))
  )
)
(define-fun full_div_f32_post13 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div rm a b))
)

; divide, part 14
(define-fun full_div_f32_pre14 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a (fp.mul rm fltmin divoff)))
    (or (= b inf)
      (ite (and (fp.gt a (fp.mul rm one divoff)) (fp.lt b one))
        (fp.geq b fltmin4)
        (ite (and (fp.lt a (fp.mul rm four divoff)) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
      )
    )
    (not (= a inf))
  )
)
(define-fun full_div_f32_post14 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)

; division, part 15
(define-fun full_div_f32_pre15 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a (fp.mul rm fltmin divoff))
    (ite (and (fp.gt a (fp.mul rm one divoff)) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a (fp.mul rm four divoff)) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (= a inf))
    (not (= b inf))
  )
)
(define-fun full_div_f32_post15 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)
(define-fun full_div_f32_assume15 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)

; division, part 16
(define-fun full_div_f32_pre16 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (= (fp32_exp b) (_ bv127 8))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post16 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)

; division, part 17
(define-fun full_div_f32_pre17 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.geq a fltmin) (= a zero))
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post17 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)

; division, part 18
(define-fun full_div_f32_pre18 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.geq a fltmin))
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (= b inf))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post18 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
)

; division, part 19
(define-fun full_div_f32_pre19 ((a Float32) (b Float32)) Bool
  (and
    (fp.geq a fltmin)
    (ite (and (fp.gt a one) (fp.lt b one))
      (fp.geq b fltmin4)
      (ite (and (fp.lt a four) (fp.gt b forth)) (fp32_range b fltmin fltmax4) (fp.geq b fltmin))
    )
    (not (fp_isspec_f32 a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div rm a b)))
  )
)
(define-fun full_div_f32_post19 ((ret Float32) (a Float32) (b Float32)) Bool
  (and
    (= (fp.lt ret divcmp) (fp.lt (fp.div rm a b) divcmp))
    (fp.isPositive ret)
  )
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
  (= ret (fp.div rm a b))
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

(define-fun fp_exponent ((a Float32)) (_ BitVec 8)
  ((_ extract 30 23) (to_ieee_bv a))
)

; Axiom experiment
; (assert (forall ((xxx Float32) (yyy Float32)) (=> (not (fp.lt (fp.mul rm (fp.mul rm xxx muloff) yyy) one)) (not (fp.isSubnormal (fp.mul rm xxx yyy))))))

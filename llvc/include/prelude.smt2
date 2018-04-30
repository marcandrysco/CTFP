(set-logic QF_FPBV)
(define-sort Int1    () Bool)
(define-sort Int32   () (_ BitVec 32))
(define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) a))
(define-fun fp_add ((a Float32) (b Float32)) Float32 (fp.add RNE a b))
(define-fun fp_sub ((a Float32) (b Float32)) Float32 (fp.sub RNE a b))
(define-fun fp_mul ((a Float32) (b Float32)) Float32 (fp.mul RNE a b))
(define-fun fp_sqrt ((a Float32)) Float32 (fp.sqrt RNE a))
(define-fun fp_div ((a Float32) (b Float32)) Float32 (fp.div RNE a b))
(define-const addmin Float32 ((_ to_fp 8 24) #x0c000000))
(define-const submin Float32 ((_ to_fp 8 24) #x0c000000))
(define-const mulmin Float32 ((_ to_fp 8 24) #x20000000))
(define-const divmax Float32 ((_ to_fp 8 24) #x5e800000))
(define-const sqrtmin Float32 ((_ to_fp 8 24) #x00800000))
(define-const zero Float32 ((_ to_fp 8 24) #x00000000))
(define-const one Float32 ((_ to_fp 8 24) #x3f800000))
(define-const two Float32 ((_ to_fp 8 24) #x40000000))
(define-const inf Float32 ((_ to_fp 8 24) #x7f800000))

(define-const fltmin Float32 ((_ to_fp 8 24) #x00800000))
(define-const fltmax Float32 ((_ to_fp 8 24) #x7f7fffff))
(define-const divlo Float32 ((_ to_fp 8 24) #x01000000))


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


;; HELPERS

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


; underflow a value below `lim` to zero
(define-fun fp32_underflow ((val Float32) (lim Float32)) Float32 
  (ite (fp.lt (fp.abs val) lim) (copysign zero val) val)
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
  (= ret (fp.add RNE (fp32_underflow a addmin) (fp32_underflow b addmin)))
)

; addition, part 1
(define-fun restrict_add_f32_pre1 ((a Float32) (b Float32)) Bool
  (or (fp.eq a zero) (fp.geq (fp.abs a) addmin))
)
(define-fun restrict_add_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add RNE a (fp32_underflow b addmin)))
)

; addition, part 2
(define-fun restrict_add_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.eq a zero) (fp.geq (fp.abs a) addmin))
    (or (fp.eq b zero) (fp.geq (fp.abs b) addmin))
  )
)
(define-fun restrict_add_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add RNE a b))
)


;; RESTRICT SUBTRACTION PRE/POST

; subtraction, part 0
(define-fun restrict_sub_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_sub_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub RNE (fp32_underflow a addmin) (fp32_underflow b addmin)))
)

; subtraction, part 1
(define-fun restrict_sub_f32_pre1 ((a Float32) (b Float32)) Bool
  (or (fp.eq a zero) (fp.geq (fp.abs a) addmin))
)
(define-fun restrict_sub_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub RNE a (fp32_underflow b addmin)))
)

; subtraction, part 2
(define-fun restrict_sub_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.eq a zero) (fp.geq (fp.abs a) addmin))
    (or (fp.eq b zero) (fp.geq (fp.abs b) addmin))
  )
)
(define-fun restrict_sub_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub RNE a b))
)


;; RESTRICT MULTIPLICATION SUBTRACTION PRE/POST

; multiplication, part 0
(define-fun restrict_mul_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_mul_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul RNE (fp32_underflow a mulmin) (fp32_underflow b mulmin)))
)

; multiplication, part 1
(define-fun restrict_mul_f32_pre1 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isPositive a) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul RNE (fp32_underflow a mulmin) (fp32_underflow b mulmin)))
)

; multiplication, part 2
(define-fun restrict_mul_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul RNE a (fp32_underflow b mulmin)))
)

; multiplication, part 3
(define-fun restrict_mul_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (= b zero) (fp.geq b mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_mul_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul RNE a b))
)


;; RESTRICT DIVIDE PRE/POST

; divide, part 0
(define-fun restrict_div_f32_pre0 ((a Float32) (b Float32)) Bool
  true
)
(define-fun restrict_div_f32_post0 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax)))
)

; divide, part 1
(define-fun restrict_div_f32_pre1 ((a Float32) (b Float32)) Bool
  (and
    (or (fp.isPositive a) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post1 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE (fp32_clamp a mulmin divmax) (fp32_clamp b mulmin divmax)))
)

; divide, part 2
(define-fun restrict_div_f32_pre2 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (fp.isPositive b) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post2 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE (fp32_overflow a divmax) (fp32_clamp b mulmin divmax)))
)

; divide, part 3
(define-fun restrict_div_f32_pre3 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (fp.geq a mulmin) (fp.isNaN a))
    (or (= b zero) (fp.geq b mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post3 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE (fp32_overflow a divmax) (fp32_overflow b divmax)))
)

; divide, part 4
(define-fun restrict_div_f32_pre4 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (= a inf) (and (fp.geq a mulmin) (fp.leq a divmax)) (fp.isNaN a))
    (or (= b zero) (fp.geq b mulmin) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post4 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a (fp32_overflow b divmax)))
)

; divide, part 5
(define-fun restrict_div_f32_pre5 ((a Float32) (b Float32)) Bool
  (and
    (or (= a zero) (= a inf) (and (fp.geq a mulmin) (fp.leq a divmax)) (fp.isNaN a))
    (or (= b zero) (= b inf) (and (fp.geq b mulmin) (fp.leq b divmax)) (fp.isNaN b))
  )
)
(define-fun restrict_div_f32_post5 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
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
  (= ret (fp.div RNE a b))
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
  (= ret (fp.div RNE a b))
)

; division, part 8
(define-fun restrict_div_f32_pre8 ((a Float32) (b Float32)) Bool
  (and
    (and (fp.geq a mulmin) (fp.leq a divmax))
    (and (fp.geq b mulmin) (fp.leq b divmax))
  )
)
(define-fun restrict_div_f32_post8 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)

; division, part 9
(define-fun restrict_div_f32_pre9 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range a divlo fltmax) (= a inf) (= a zero))
    (or (fp32_between b one two) (= b one))
  )
)
(define-fun restrict_div_f32_post9 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)

; division, part 10
(define-fun restrict_div_f32_pre10 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range a divlo fltmax) (= a inf) (= a zero))
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post10 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)

; division, part 11
(define-fun restrict_div_f32_pre11 ((a Float32) (b Float32)) Bool
  (and
    (or (fp32_range a divlo fltmax) (= a inf))
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post11 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)

; division, part 12
(define-fun restrict_div_f32_pre12 ((a Float32) (b Float32)) Bool
  (and
    (fp32_range a divlo fltmax)
    (fp32_between b one two)
  )
)
(define-fun restrict_div_f32_post12 ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)


;; RESTRICT SQRT PRE/POST

; sqrt, part 0
(define-fun restrict_sqrt_f32_pre0 ((a Float32)) Bool
  true
)
(define-fun restrict_sqrt_f32_post0 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE (fp32_underflow a fltmin)))
)

; sqrt, part 1
(define-fun restrict_sqrt_f32_pre1 ((a Float32)) Bool
  (not (fp.isSubnormal (fp.sqrt RNE a)))
)
(define-fun restrict_sqrt_f32_post1 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)

; sqrt, part 2
(define-fun restrict_sqrt_f32_pre2 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt RNE a)))
    (not (fp.isNaN a))
  )
)
(define-fun restrict_sqrt_f32_post2 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)

; sqrt, part 3
(define-fun restrict_sqrt_f32_pre3 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt RNE a)))
    (not (fp.isNaN a))
    (not (= a inf))
  )
)
(define-fun restrict_sqrt_f32_post3 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)

; sqrt, part 4
(define-fun restrict_sqrt_f32_pre4 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt RNE a)))
    (not (fp.isNaN a))
    (not (= a inf))
    (fp.geq a zero)
  )
)
(define-fun restrict_sqrt_f32_post4 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)

; sqrt, part 5
(define-fun restrict_sqrt_f32_pre5 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt RNE a)))
    (not (fp.isNaN a))
    (not (= a inf))
    (fp.gt a zero)
  )
)
(define-fun restrict_sqrt_f32_post5 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)

; sqrt, part 6
(define-fun restrict_sqrt_f32_pre6 ((a Float32)) Bool
  (and
    (not (fp.isSubnormal (fp.sqrt RNE a)))
    (not (fp.isNaN a))
    (not (= a inf))
    (fp.gt a zero)
    (not (fp32_ispow4 a))
  )
)
(define-fun restrict_sqrt_f32_post6 ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)


;; PRIMITIVE OPERATION SAFETY

; fadd
(define-fun fadd32_pre ((a Float32) (b Float32)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	   (fp.isSubnormal (fp.add RNE a b)))
  )
)
(define-fun fadd32_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.add RNE a b))
)

; fsub
(define-fun fsub32_pre ((a Float32) (b Float32)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	   (fp.isSubnormal (fp.add RNE a b)))
  )
)
(define-fun fsub32_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.sub RNE a b))
)

; fmul
(define-fun fmul32_pre ((a Float32) (b Float32)) Bool
  (not (or (fp.isSubnormal a) 
           (fp.isSubnormal b) 
	   (fp.isSubnormal (fp.add RNE a b)))
  )
)
(define-fun fmul32_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.mul RNE a b))
)

; fdiv exponent
(define-fun fdiv32exp_pre ((a Float32) (b Float32)) Bool
  (and
    (not (fp_isspec_f32 a))
    (not (fp_isspec_f32 b))
    (fp32_ispow2 b)
    (not (fp.isSubnormal (fp.div RNE a b)))
  )
)
(define-fun fdiv32exp_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)

; fdiv significand
(define-fun fdiv32sig_pre ((a Float32) (b Float32)) Bool
  (and
    (not (fp_isspec_f32 a))
    (not (fp_isspec_f32 b))
    (not (fp32_ispow2 b))
    (not (fp.isSubnormal (fp.div RNE a b)))
  )
)
(define-fun fdiv32sig_post ((ret Float32) (a Float32) (b Float32)) Bool
  (= ret (fp.div RNE a b))
)

; fsqrt
(define-fun fsqrt32_pre ((a Float32)) Bool
  (and
    (fp.geq a zero)
    (not (= a inf))
    (not (fp32_ispow4 a))
    (not (fp.isSubnormal (fp.sqrt RNE a)))
  )
)
(define-fun fsqrt32_post ((ret Float32) (a Float32)) Bool
  (= ret (fp.sqrt RNE a))
)

(define-fun fp_exponent ((a Float32)) (_ BitVec 8)
  ((_ extract 30 23) (to_ieee_bv a))
)

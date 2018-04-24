(set-logic QF_FPBV)
(define-sort Int1    () Bool)
(define-sort Int32   () (_ BitVec 32))
(define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) a))
(define-fun fp_add ((a Float32) (b Float32)) Float32 (fp.add RNE a b))
(define-fun fp_mul ((a Float32) (b Float32)) Float32 (fp.mul RNE a b))
(define-const addmin Float32 ((_ to_fp 8 24) #x0c000000))
(define-const mulmin Float32 ((_ to_fp 8 24) #x20000000))
(define-const zero Float32 ((_ to_fp 8 24) #x00000000))


(define-const one_point_zero Float32 ((_ to_fp 8 24) roundTowardZero 1.0))


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



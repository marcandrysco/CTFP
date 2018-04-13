(set-logic QF_FPBV)
(define-sort Int1    () Bool)
(define-sort Int32   () (_ BitVec 32))
(define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) RNE a))
(define-fun fp_add ((a Float32) (b Float32)) Float32 (fp.add RNE a b))
(define-const addmin Float32 ((_ to_fp 8 24) #x0c000000))
(define-const zero Float32 ((_ to_fp 8 24) #x00000000))

(define-fun lt    ((a Int32) (b Int32)) Bool (bvslt a b))
(define-fun rng   ((n Int32) (x Int32)) Bool (or (= #x00000000 x) (bvsle n x)))
(define-fun trunc ((n Int32) (x Int32)) Int32 (ite (bvslt x n) #x00000000 x))
(define-fun plus  ((a Int32) (b Int32)) Int32 (bvadd a b)) 

(define-fun copysign ((a Float32) (b Float32)) Float32  
  (to_fp_32 (bvor (bvand (to_ieee_bv a) #x7fffffff)                  
    		  (bvand (to_ieee_bv b) #x80000000))))


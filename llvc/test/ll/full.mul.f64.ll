; Function Attrs: nounwind readnone
declare double @llvm.fabs.f64(double) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare double @llvm.copysign.f64(double, double) #0
;@ requires true 
;@ ensures  (= %ret (fp64_copysign %arg0 %arg1))

; Function Attrs: nounwind readnone
declare float @scale_mul(float) #0
;@ requires true
;@ ensures (= %ret (ite (bvule (fp32_exp %arg0) one8) (to_fp_32 (concat zero1 (bvsub (bvadd (fp32_exp muloff) (fp32_exp %arg0)) bias) (fp32_sig %arg0))) inf))

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre0 %a %b)
;@ ensures  (full_mul_f64_post0 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = call double @llvm.fabs.f64(double %b)
  %3 = call double @ctfp_full_mul_f64v1_1(double %1, double %2)
  %4 = bitcast double %a to i64
  %5 = bitcast double %b to i64
  %6 = xor i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %3, double %7)
  ret double %8
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_1(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre1 %a %b)
;@ ensures  (full_mul_f64_post1 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %a to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @ctfp_full_mul_f64v1_2(double %7, double %b)
  ret double %8
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_2(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre2 %a %b)
;@ ensures  (full_mul_f64_post2 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %b to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @ctfp_full_mul_f64v1_3(double %a, double %7)
  ret double %8
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_3(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre3 %a %b)
;@ ensures  (full_mul_f64_post3 %ret %a %b)
  %1 = fmul double %a, 0x5FE0000000000000
  %2 = fmul double %1, %b
  %3 = call double @llvm.fabs.f64(double %2)
  %4 = fcmp olt double %3, 1.000000e+00
  %5 = select i1 %4, i64 -1, i64 0
  %6 = xor i64 %5, -1
  %7 = bitcast double %a to i64
  %8 = and i64 %6, %7
  %9 = bitcast i64 %8 to double
  %10 = bitcast double %b to i64
  %11 = and i64 %6, %10
  %12 = bitcast i64 %11 to double
  %13 = call double @ctfp_full_mul_f64v1_4(double %9, double %12)
  %14 = call double @llvm.copysign.f64(double %13, double %2)
  %15 = bitcast double %14 to i64
  %16 = and i64 %5, %15
  %17 = bitcast double %13 to i64
  %18 = and i64 %6, %17
  %19 = or i64 %16, %18
  %20 = bitcast i64 %19 to double
  ret double %20
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_4(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre4 %a %b)
;@ ensures  (full_mul_f64_post4 %ret %a %b)
  %1 = fmul double %a, %b
  ret double %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

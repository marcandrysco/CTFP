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
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %a to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %a)
  %9 = call double @ctfp_full_mul_f64v1_1(double %8, double %b)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_1(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre1 %a %b)
;@ ensures  (full_mul_f64_post1 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %b to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %b)
  %9 = call double @ctfp_full_mul_f64v1_2(double %a, double %8)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_2(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre2 %a %b)
;@ ensures  (full_mul_f64_post2 %ret %a %b)
  %1 = fmul double %a, 0x5FE0000000000000
  %2 = fmul double %1, %b
  %3 = call double @llvm.fabs.f64(double %2)
  %4 = fcmp ogt double %3, 0.000000e+00
  %5 = select i1 %4, i64 -1, i64 0
  %6 = fcmp olt double %3, 1.000000e+00
  %7 = select i1 %6, i64 -1, i64 0
  %8 = and i64 %5, %7
  %9 = xor i64 %8, -1
  %10 = bitcast double %a to i64
  %11 = and i64 %9, %10
  %12 = bitcast i64 %11 to double
  %13 = bitcast double %b to i64
  %14 = and i64 %9, %13
  %15 = bitcast i64 %14 to double
  %16 = call double @ctfp_full_mul_f64v1_3(double %12, double %15)
  %17 = call double @llvm.copysign.f64(double %16, double %2)
  %18 = bitcast double %17 to i64
  %19 = and i64 %8, %18
  %20 = bitcast double %16 to i64
  %21 = and i64 %9, %20
  %22 = or i64 %19, %21
  %23 = bitcast i64 %22 to double
  ret double %23
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_mul_f64v1_3(double %a, double %b) #2 {
;@ requires (full_mul_f64_pre3 %a %b)
;@ ensures  (full_mul_f64_post3 %ret %a %b)
  %1 = fmul double %a, %b
  ret double %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

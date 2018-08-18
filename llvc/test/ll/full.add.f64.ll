; Function Attrs: nounwind readnone
declare double @llvm.fabs.f64(double) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare double @llvm.copysign.f64(double, double) #0
;@ requires true 
;@ ensures  (= %ret (fp64_copysign %arg0 %arg1))


; Function Attrs: alwaysinline
define weak double @ctfp_full_add_f64v1(double %a, double %b) #2 {
;@ requires (full_add_f64_pre0 %a %b)
;@ ensures  (full_add_f64_post0 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %a to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %a)
  %9 = call double @ctfp_full_add_f64v1_1(double %8, double %b)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_add_f64v1_1(double %a, double %b) #2 {
;@ requires (full_add_f64_pre1 %a %b)
;@ ensures  (full_add_f64_post1 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %b to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %b)
  %9 = call double @ctfp_full_add_f64v1_2(double %a, double %8)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_add_f64v1_2(double %a, double %b) #2 {
;@ requires (full_add_f64_pre2 %a %b)
;@ ensures  (full_add_f64_post2 %ret %a %b)
  %1 = fmul double %a, 0x4350000000001198
  %2 = fmul double %b, 0x4350000000001198
  %3 = fadd double %1, %2
  %4 = call double @llvm.fabs.f64(double %3)
  %5 = fcmp ogt double %4, 0.000000e+00
  %6 = select i1 %5, i64 -1, i64 0
  %7 = fcmp olt double %4, 0x370000000000904
  %8 = select i1 %7, i64 -1, i64 0
;@ assert (split %7)
  %9 = and i64 %6, %8
  %10 = xor i64 %9, -1
  %11 = bitcast double %a to i64
  %12 = and i64 %10, %11
  %13 = bitcast i64 %12 to double
  %14 = bitcast double %b to i64
  %15 = and i64 %10, %14
  %16 = bitcast i64 %15 to double
  %17 = call double @ctfp_full_add_f64v1_3(double %13, double %16)
  %18 = call double @llvm.copysign.f64(double %17, double %3)
  %19 = bitcast double %18 to i64
  %20 = and i64 %9, %19
  %21 = bitcast double %17 to i64
  %22 = and i64 %10, %21
  %23 = or i64 %20, %22
  %24 = bitcast i64 %23 to double
  ret double %24
}

; Function Attrs: alwaysinline
define weak double @ctfp_full_add_f64v1_3(double %a, double %b) #2 {
;@ requires (full_add_f64_pre3 %a %b)
;@ ensures  (full_add_f64_post3 %ret %a %b)
  %1 = fadd double %a, %b
  ret double %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

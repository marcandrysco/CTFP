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
  %5 = fcmp olt double %4, 0x370000000000904
  %6 = select i1 %5, i64 -1, i64 0
  %7 = xor i64 %6, -1
  %8 = bitcast double %a to i64
  %9 = and i64 %7, %8
  %10 = bitcast i64 %9 to double
  %11 = bitcast double %b to i64
  %12 = and i64 %7, %11
  %13 = bitcast i64 %12 to double
  %14 = call double @ctfp_full_add_f64v1_3(double %10, double %13)
  %15 = call double @llvm.copysign.f64(double %14, double %3)
  %16 = bitcast double %15 to i64
  %17 = and i64 %6, %16
  %18 = bitcast double %14 to i64
  %19 = and i64 %7, %18
  %20 = or i64 %17, %19
  %21 = bitcast i64 %20 to double
  ret double %21
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

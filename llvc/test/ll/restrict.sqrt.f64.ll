; Function Attrs: nounwind readnone
declare double @llvm.fabs.f64(double) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare double @llvm.sqrt.f64(double) #0
;@ requires (fsqrt64_pre %a)
;@ ensures (fsqrt64_post %ret %a)

; Function Attrs: nounwind readnone
declare double @llvm.copysign.f64(double, double) #0
;@ requires true 
;@ ensures  (= %ret (fp64_copysign %arg0 %arg1))

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre0 %a)
;@ ensures  (restrict_sqrt_f64_post0 %ret %a)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp olt double %1, 0x10000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %a to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @ctfp_restrict_sqrt_f64v1_1(double %7)
  %9 = call double @llvm.copysign.f64(double %8, double %a)
  %10 = bitcast double %9 to i64
  %11 = and i64 %3, %10
  %12 = bitcast double %8 to i64
  %13 = and i64 %4, %12
  %14 = or i64 %11, %13
  %15 = bitcast i64 %14 to double
  ret double %15
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1_1(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre1 %a)
;@ ensures  (restrict_sqrt_f64_post1 %ret %a)
  %1 = fcmp une double %a, %a
  %2 = select i1 %1, i64 -1, i64 0
;@ assume (split %1)
  %3 = and i64 %2, 9221120237041090560
  %4 = xor i64 %2, -1
  %5 = and i64 %2, 4609434218613702656
  %6 = bitcast double %a to i64
  %7 = and i64 %4, %6
  %8 = or i64 %5, %7
  %9 = bitcast i64 %8 to double
  %10 = call double @ctfp_restrict_sqrt_f64v1_2(double %9)
  %11 = bitcast double %10 to i64
  %12 = and i64 %4, %11
  %13 = or i64 %3, %12
  %14 = bitcast i64 %13 to double
  ret double %14
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1_2(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre2 %a)
;@ ensures  (restrict_sqrt_f64_post2 %ret %a)
  %1 = fcmp oeq double %a, 0x7FF0000000000000
  %2 = select i1 %1, i64 -1, i64 0
;@ assume (split %1)
  %3 = and i64 %2, 9218868437227405312
  %4 = xor i64 %2, -1
  %5 = and i64 %2, 4609434218613702656
  %6 = bitcast double %a to i64
  %7 = and i64 %4, %6
  %8 = or i64 %5, %7
  %9 = bitcast i64 %8 to double
  %10 = call double @ctfp_restrict_sqrt_f64v1_3(double %9)
  %11 = bitcast double %10 to i64
  %12 = and i64 %4, %11
  %13 = or i64 %3, %12
  %14 = bitcast i64 %13 to double
  ret double %14
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1_3(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre3 %a)
;@ ensures  (restrict_sqrt_f64_post3 %ret %a)
  %1 = fcmp olt double %a, 0.000000e+00
  %2 = select i1 %1, i64 -1, i64 0
;@ assume (split %1)
  %3 = and i64 %2, 9221120237041090560
  %4 = xor i64 %2, -1
  %5 = and i64 %2, 4609434218613702656
  %6 = bitcast double %a to i64
  %7 = and i64 %4, %6
  %8 = or i64 %5, %7
  %9 = bitcast i64 %8 to double
  %10 = call double @ctfp_restrict_sqrt_f64v1_4(double %9)
  %11 = bitcast double %10 to i64
  %12 = and i64 %4, %11
  %13 = or i64 %3, %12
  %14 = bitcast i64 %13 to double
  ret double %14
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1_4(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre4 %a)
;@ ensures  (restrict_sqrt_f64_post4 %ret %a)
  %1 = fcmp oeq double %a, 0.000000e+00
  %2 = select i1 %1, i64 -1, i64 0
  %3 = bitcast double %a to i64
  %4 = and i64 %2, %3
  %5 = xor i64 %2, -1
  %6 = and i64 %2, 4609434218613702656
  %7 = and i64 %5, %3
  %8 = or i64 %6, %7
  %9 = bitcast i64 %8 to double
;@ assume (spliteq64 %a %9)
  %10 = call double @ctfp_restrict_sqrt_f64v1_5(double %9)
  %11 = bitcast double %10 to i64
  %12 = and i64 %5, %11
  %13 = or i64 %4, %12
  %14 = bitcast i64 %13 to double
  ret double %14
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1_5(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre5 %a)
;@ ensures  (restrict_sqrt_f64_post5 %ret %a)
  %1 = bitcast double %a to i64
  %2 = and i64 %1, 9007199254740991
  %3 = bitcast i64 %2 to double
  %4 = fcmp oeq double %3, 0x10000000000000
  %5 = select i1 %4, i64 -1, i64 0
;@ assume (split %4)
  %6 = or i64 %1, 1
  %7 = and i64 %5, %6
  %8 = xor i64 %5, -1
  %9 = and i64 %8, %1
  %10 = or i64 %7, %9
  %11 = bitcast i64 %10 to double
  %12 = call double @ctfp_restrict_sqrt_f64v1_6(double %11)
  %13 = bitcast double %12 to i64
  %14 = and i64 %13, -2
  %15 = and i64 %5, %14
  %16 = and i64 %8, %13
  %17 = or i64 %15, %16
  %18 = bitcast i64 %17 to double
  ret double %18
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_sqrt_f64v1_6(double %a) #2 {
;@ requires (restrict_sqrt_f64_pre6 %a)
;@ ensures  (restrict_sqrt_f64_post6 %ret %a)
  %1 = call double @llvm.sqrt.f64(double %a)
  ret double %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

; Function Attrs: nounwind readnone
declare double @llvm.fabs.f64(double) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare double @llvm.copysign.f64(double, double) #0
;@ requires true 
;@ ensures  (= %ret (fp64_copysign %arg0 %arg1))

declare double @fdiv_sig(double, double)
;@ requires (fdiv64sig_pre %arg0 %arg1)
;@ ensures (fdiv64sig_post %ret %arg0 %arg1)

declare double @fdiv_exp(double, double)
;@ requires (fdiv64exp_pre %arg0 %arg1)
;@ ensures (fdiv64exp_post %ret %arg0 %arg1)


; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre0 %a %b)
;@ ensures  (restrict_div_f64_post0 %ret %a %b)
  %1 = call double @ctfp_restrict_div_f64v1_1(double %a, double %b)
  %2 = bitcast double %a to i64
  %3 = bitcast double %b to i64
  %4 = xor i64 %2, %3
  %5 = bitcast i64 %4 to double
  %6 = call double @llvm.copysign.f64(double %1, double %5)
  ret double %6
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_1(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre1 %a %b)
;@ ensures  (restrict_div_f64_post1 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp olt double %1, 0x2000000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %a to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %a)
  %9 = call double @ctfp_restrict_div_f64v1_2(double %8, double %b)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_2(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre2 %a %b)
;@ ensures  (restrict_div_f64_post2 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp olt double %1, 0x2000000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %b to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %b)
  %9 = call double @ctfp_restrict_div_f64v1_3(double %a, double %8)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_3(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre3 %a %b)
;@ ensures  (restrict_div_f64_post3 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp ogt double %1, 0x5FD0000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = and i64 %3, 9218868437227405312
  %5 = xor i64 %3, -1
  %6 = bitcast double %a to i64
  %7 = and i64 %5, %6
  %8 = or i64 %4, %7
  %9 = bitcast i64 %8 to double
  %10 = call double @ctfp_restrict_div_f64v1_4(double %9, double %b)
  ret double %10
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_4(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre4 %a %b)
;@ ensures  (restrict_div_f64_post4 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp ogt double %1, 0x5FD0000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = and i64 %3, 9218868437227405312
  %5 = xor i64 %3, -1
  %6 = bitcast double %b to i64
  %7 = and i64 %5, %6
  %8 = or i64 %4, %7
  %9 = bitcast i64 %8 to double
  %10 = call double @ctfp_restrict_div_f64v1_5(double %a, double %9)
  ret double %10
}


; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_5(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre5 %a %b)
;@ ensures  (restrict_div_f64_post5 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp une double %1, %1
  %3 = select i1 %2, i64 -1, i64 0
  %4 = call double @llvm.fabs.f64(double %b)
  %5 = fcmp une double %4, %4
  %6 = select i1 %5, i64 -1, i64 0
;@ assume (split %5)
  %7 = fcmp oeq double 0x7FF0000000000000, %1
  %8 = select i1 %7, i64 -1, i64 0
;@ assume (split %7)
  %9 = fcmp oeq double 0x7FF0000000000000, %4
  %10 = select i1 %9, i64 -1, i64 0
;@ assume (split %9)
  %11 = and i64 %8, %10
  %12 = fcmp oeq double 0.000000e+00, %1
  %13 = select i1 %12, i64 -1, i64 0
  %14 = fcmp oeq double 0.000000e+00, %4
  %15 = select i1 %14, i64 -1, i64 0
;@ assume (split %14)
  %16 = and i64 %13, %15
  %17 = or i64 %11, %16
  %18 = or i64 %6, %17
  %19 = or i64 %3, %18
  %20 = and i64 %19, 9221120237041090560
  %21 = xor i64 %19, -1
  %22 = and i64 %19, 4609434218613702656
  %23 = bitcast double %a to i64
  %24 = and i64 %21, %23
  %25 = or i64 %22, %24
  %26 = bitcast i64 %25 to double
  %27 = bitcast double %b to i64
  %28 = and i64 %21, %27
  %29 = or i64 %22, %28
  %30 = bitcast i64 %29 to double
  %31 = call double @ctfp_restrict_div_f64v1_6(double %26, double %30)
  %64 = bitcast double %31 to i64
  %33 = and i64 %21, %64
  %34 = or i64 %20, %33
  %35 = bitcast i64 %34 to double
  ret double %35
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_6(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre6 %a %b)
;@ ensures  (restrict_div_f64_post6 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp oeq double 0x7FF0000000000000, %1
  %3 = select i1 %2, i64 -1, i64 0
  %4 = call double @llvm.fabs.f64(double %b)
  %5 = fcmp oeq double 0.000000e+00, %4
  %6 = select i1 %5, i64 -1, i64 0
  %7 = or i64 %3, %6
  %8 = and i64 %7, 9218868437227405312
  %9 = xor i64 %7, -1
  %10 = and i64 %7, 4609434218613702656
  %11 = bitcast double %a to i64
  %12 = and i64 %9, %11
  %13 = or i64 %10, %12
  %14 = bitcast i64 %13 to double
  %15 = bitcast double %b to i64
  %16 = and i64 %9, %15
  %17 = or i64 %10, %16
  %18 = bitcast i64 %17 to double
  %19 = call double @ctfp_restrict_div_f64v1_7(double %14, double %18)
  %20 = bitcast double %19 to i64
  %21 = and i64 %9, %20
  %22 = or i64 %8, %21
  %23 = bitcast i64 %22 to double
  ret double %23
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_7(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre7 %a %b)
;@ ensures  (restrict_div_f64_post7 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp oeq double 0.000000e+00, %1
  %3 = select i1 %2, i64 -1, i64 0
  %4 = call double @llvm.fabs.f64(double %b)
  %5 = fcmp oeq double 0x7FF0000000000000, %4
  %6 = select i1 %5, i64 -1, i64 0
  %7 = or i64 %3, %6
  %8 = xor i64 %7, -1
  %9 = and i64 %7, 4609434218613702656
  %10 = bitcast double %a to i64
  %11 = and i64 %8, %10
  %12 = or i64 %9, %11
  %13 = bitcast i64 %12 to double
  %14 = bitcast double %b to i64
  %15 = and i64 %8, %14
  %16 = or i64 %9, %15
  %17 = bitcast i64 %16 to double
  %18 = call double @ctfp_restrict_div_f64v1_8(double %13, double %17)
  %19 = bitcast double %18 to i64
  %20 = and i64 %8, %19
  %21 = bitcast i64 %20 to double
  ret double %21
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_8(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre8 %a %b)
;@ ensures  (restrict_div_f64_post8 %ret %a %b)
  %1 = bitcast double %b to i64
  %2 = and i64 %1, -4503599627370496
  %3 = bitcast i64 %2 to double
  %4 = call double @fdiv_exp(double %a, double %3)
  %5 = and i64 %1, 4503599627370495
  %6 = or i64 %5, 4607182418800017408
  %7 = bitcast i64 %6 to double
  %8 = call double @ctfp_restrict_div_f64v1_9(double %4, double %7)
;@ assume (restrict_div_f64_assume8_1 %a %b)
  ret double %8
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_9(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre9 %a %b)
;@ ensures  (restrict_div_f64_post9 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp oeq double %1, 1.000000e+00
  %3 = select i1 %2, i64 -1, i64 0
;@ assume (split %2)
  %4 = bitcast double %a to i64
  %5 = and i64 %3, %4
  %6 = xor i64 %3, -1
  %7 = and i64 %3, 4609434218613702656
  %8 = and i64 %6, %4
  %9 = or i64 %7, %8
  %10 = bitcast i64 %9 to double
  %11 = bitcast double %b to i64
  %12 = and i64 %6, %11
  %13 = or i64 %7, %12
  %14 = bitcast i64 %13 to double
  %15 = call double @ctfp_restrict_div_f64v1_10(double %10, double %14)
  %16 = bitcast double %15 to i64
  %17 = and i64 %6, %16
  %18 = or i64 %5, %17
  %19 = bitcast i64 %18 to double
  ret double %19
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_10(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre10 %a %b)
;@ ensures  (restrict_div_f64_post10 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp oeq double 0.000000e+00, %1
  %3 = select i1 %2, i64 -1, i64 0
;@ assume (split %2)
  %4 = xor i64 %3, -1
  %5 = and i64 %3, 4609434218613702656
  %6 = bitcast double %a to i64
  %7 = and i64 %4, %6
  %8 = or i64 %5, %7
  %9 = bitcast i64 %8 to double
  %10 = bitcast double %b to i64
  %11 = and i64 %4, %10
  %12 = or i64 %5, %11
  %13 = bitcast i64 %12 to double
  %14 = call double @ctfp_restrict_div_f64v1_11(double %9, double %13)
  %15 = bitcast double %14 to i64
  %16 = and i64 %4, %15
  %17 = bitcast i64 %16 to double
  ret double %17
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_11(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre11 %a %b)
;@ ensures  (restrict_div_f64_post11 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp oeq double 0x7FF0000000000000, %1
  %3 = select i1 %2, i64 -1, i64 0
;@ assume (split %2)
  %4 = and i64 %3, 9218868437227405312
  %5 = xor i64 %3, -1
  %6 = and i64 %3, 4609434218613702656
  %7 = bitcast double %a to i64
  %8 = and i64 %5, %7
  %9 = or i64 %6, %8
  %10 = bitcast i64 %9 to double
  %11 = bitcast double %b to i64
  %12 = and i64 %5, %11
  %13 = or i64 %6, %12
  %14 = bitcast i64 %13 to double
  %15 = call double @ctfp_restrict_div_f64v1_12(double %10, double %14)
  %16 = bitcast double %15 to i64
  %17 = and i64 %5, %16
  %18 = or i64 %4, %17
  %19 = bitcast i64 %18 to double
  ret double %19
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_div_f64v1_12(double %a, double %b) #2 {
;@ requires (restrict_div_f64_pre12 %a %b)
;@ ensures  (restrict_div_f64_post12 %ret %a %b)
  %1 = call double @fdiv_sig(double %a, double %b)
  ret double %1
}


attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 

declare float @fdiv_sig(float, float)
;@ requires (fdiv32sig_pre %arg0 %arg1)
;@ ensures (fdiv32sig_post %ret %arg0 %arg1)

declare float @fdiv_exp(float, float)
;@ requires (fdiv32exp_pre %arg0 %arg1)
;@ ensures (fdiv32exp_post %ret %arg0 %arg1)

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1(float %a, float %b) #2 {
;@ requires (full_div_f32_pre0 %a %b)
;@ ensures  (full_div_f32_post0 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = call float @llvm.fabs.f32(float %b)
  %3 = call float @ctfp_full_div_f32v1_1(float %1, float %2)
  %4 = bitcast float %a to i32
  %5 = bitcast float %b to i32
  %6 = xor i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %3, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_1(float %a, float %b) #2 {
;@ requires (full_div_f32_pre1 %a %b)
;@ ensures  (full_div_f32_post1 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %a to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_full_div_f32v1_2(float %7, float %b)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_2(float %a, float %b) #2 {
;@ requires (full_div_f32_pre2 %a %b)
;@ ensures  (full_div_f32_post2 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %b to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_full_div_f32v1_3(float %a, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_3(float %a, float %b) #2 {
;@ requires (full_div_f32_pre3 %a %b)
;@ ensures  (full_div_f32_post3 %ret %a %b)
  %1 = fcmp ogt float %a, 1.000000e+00
  %2 = select i1 %1, i32 -1, i32 0
  %3 = fcmp olt float %b, 1.000000e+00
  %4 = select i1 %3, i32 -1, i32 0
  %5 = and i32 %2, %4
  %6 = and i32 %5, 1082130432
  %7 = xor i32 %5, -1
  %8 = fcmp olt float %a, 4.000000e+00
  %9 = select i1 %8, i32 -1, i32 0
  %10 = fcmp ogt float %b, 2.500000e-01
  %11 = select i1 %10, i32 -1, i32 0
  %12 = and i32 %9, %11
  %13 = and i32 %12, 1048576000
  %14 = xor i32 %12, -1
  %15 = and i32 %14, 1065353216
  %16 = or i32 %13, %15
  %17 = and i32 %7, %16
  %18 = or i32 %6, %17
  %19 = bitcast i32 %18 to float
  %20 = fmul float %b, %19
  %21 = call float @ctfp_full_div_f32v1_4(float %a, float %20)
  %22 = fmul float %21, %19
  ret float %22
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_4(float %a, float %b) #2 {
;@ requires (full_div_f32_pre4 %a %b)
;@ ensures  (full_div_f32_post4 %ret %a %b)
  %1 = fmul float %a, 0x47D0000000000000
  %2 = fcmp une float %1, %1
  %3 = select i1 %2, i32 -1, i32 0
  %4 = fcmp une float %b, %b
  %5 = select i1 %4, i32 -1, i32 0
  %6 = fcmp oeq float 0x7FF0000000000000, %1
  %7 = select i1 %6, i32 -1, i32 0
  %8 = fcmp oeq float 0x7FF0000000000000, %b
  %9 = select i1 %8, i32 -1, i32 0
  %10 = and i32 %7, %9
  %11 = fcmp oeq float 0.000000e+00, %1
  %12 = select i1 %11, i32 -1, i32 0
  %13 = fcmp oeq float 0.000000e+00, %b
  %14 = select i1 %13, i32 -1, i32 0
  %15 = and i32 %12, %14
  %16 = or i32 %10, %15
  %17 = or i32 %5, %16
  %18 = or i32 %3, %17
  %19 = and i32 %18, 2143289344
  %20 = xor i32 %18, -1
  %21 = and i32 %18, 1069547520
  %22 = bitcast float %1 to i32
  %23 = and i32 %20, %22
  %24 = or i32 %21, %23
  %25 = bitcast i32 %24 to float
  %26 = bitcast float %b to i32
  %27 = and i32 %20, %26
  %28 = or i32 %21, %27
  %29 = bitcast i32 %28 to float
  %30 = call float @ctfp_full_div_f32v1_5(float %25, float %29)
  %31 = bitcast float %30 to i32
  %32 = and i32 %20, %31
  %33 = or i32 %19, %32
  %34 = bitcast i32 %33 to float
  %35 = call float @llvm.fabs.f32(float %34)
  %36 = fcmp olt float %35, 4.000000e+00
  %37 = select i1 %36, i32 -1, i32 0
  %38 = xor i32 %37, -1
  %39 = bitcast float %a to i32
  %40 = and i32 %38, %39
  %41 = bitcast i32 %40 to float
  %42 = and i32 %37, 1065353216
  %43 = and i32 %38, %26
  %44 = or i32 %42, %43
  %45 = bitcast i32 %44 to float
  %46 = call float @ctfp_full_div_f32v1_6(float %41, float %45)
  %47 = call float @llvm.copysign.f32(float %46, float %34)
  %48 = bitcast float %47 to i32
  %49 = and i32 %37, %48
  %50 = bitcast float %46 to i32
  %51 = and i32 %38, %50
  %52 = or i32 %49, %51
  %53 = bitcast i32 %52 to float
  ret float %53
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_6(float %a, float %b) #2 {
;@ requires (full_div_f32_pre6 %a %b)
;@ ensures  (full_div_f32_post6 %ret %a %b)
  %1 = fcmp une float %a, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = fcmp une float %b, %b
  %4 = select i1 %3, i32 -1, i32 0
  %5 = fcmp oeq float 0x7FF0000000000000, %a
  %6 = select i1 %5, i32 -1, i32 0
  %7 = fcmp oeq float 0x7FF0000000000000, %b
  %8 = select i1 %7, i32 -1, i32 0
  %9 = and i32 %6, %8
  %10 = fcmp oeq float 0.000000e+00, %a
  %11 = select i1 %10, i32 -1, i32 0
  %12 = fcmp oeq float 0.000000e+00, %b
  %13 = select i1 %12, i32 -1, i32 0
  %14 = and i32 %11, %13
  %15 = or i32 %9, %14
  %16 = or i32 %4, %15
  %17 = or i32 %2, %16
  %18 = and i32 %17, 2143289344
  %19 = xor i32 %17, -1
  %20 = and i32 %17, 1069547520
  %21 = bitcast float %a to i32
  %22 = and i32 %19, %21
  %23 = or i32 %20, %22
  %24 = bitcast i32 %23 to float
  %25 = bitcast float %b to i32
  %26 = and i32 %19, %25
  %27 = or i32 %20, %26
  %28 = bitcast i32 %27 to float
  %29 = call float @ctfp_full_div_f32v1_7(float %24, float %28)
  %30 = bitcast float %29 to i32
  %31 = and i32 %19, %30
  %32 = or i32 %18, %31
  %33 = bitcast i32 %32 to float
  ret float %33
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_7(float %a, float %b) #2 {
;@ requires (full_div_f32_pre7 %a %b)
;@ ensures  (full_div_f32_post7 %ret %a %b)
  %1 = fcmp oeq float 0x7FF0000000000000, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = fcmp oeq float 0.000000e+00, %b
  %4 = select i1 %3, i32 -1, i32 0
  %5 = or i32 %2, %4
  %6 = and i32 %5, 2139095040
  %7 = xor i32 %5, -1
  %8 = and i32 %5, 1069547520
  %9 = bitcast float %a to i32
  %10 = and i32 %7, %9
  %11 = or i32 %8, %10
  %12 = bitcast i32 %11 to float
  %13 = bitcast float %b to i32
  %14 = and i32 %7, %13
  %15 = or i32 %8, %14
  %16 = bitcast i32 %15 to float
  %17 = call float @ctfp_full_div_f32v1_8(float %12, float %16)
  %18 = bitcast float %17 to i32
  %19 = and i32 %7, %18
  %20 = or i32 %6, %19
  %21 = bitcast i32 %20 to float
  ret float %21
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_8(float %a, float %b) #2 {
;@ requires (full_div_f32_pre8 %a %b)
;@ ensures  (full_div_f32_post8 %ret %a %b)
  %1 = fcmp oeq float 0.000000e+00, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = fcmp oeq float 0x7FF0000000000000, %b
  %4 = select i1 %3, i32 -1, i32 0
  %5 = or i32 %2, %4
  %6 = xor i32 %5, -1
  %7 = and i32 %5, 1069547520
  %8 = bitcast float %a to i32
  %9 = and i32 %6, %8
  %10 = or i32 %7, %9
  %11 = bitcast i32 %10 to float
  %12 = bitcast float %b to i32
  %13 = and i32 %6, %12
  %14 = or i32 %7, %13
  %15 = bitcast i32 %14 to float
  %16 = call float @ctfp_full_div_f32v1_9(float %11, float %15)
  %17 = bitcast float %16 to i32
  %18 = and i32 %6, %17
  %19 = bitcast i32 %18 to float
  ret float %19
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_9(float %a, float %b) #2 {
;@ requires (full_div_f32_pre9 %a %b)
;@ ensures  (full_div_f32_post9 %ret %a %b)
  %1 = bitcast float %b to i32
  %2 = and i32 %1, 2139095040
  %3 = bitcast i32 %2 to float
  %4 = call float @fdiv_exp(float %a, float %3)
  %5 = and i32 %1, 8388607
  %6 = or i32 %5, 1065353216
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_full_div_f32v1_10(float %4, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_10(float %a, float %b) #2 {
;@ requires (full_div_f32_pre10 %a %b)
;@ ensures  (full_div_f32_post10 %ret %a %b)
  %1 = fcmp oeq float %b, 1.000000e+00
  %2 = select i1 %1, i32 -1, i32 0
  %3 = bitcast float %a to i32
  %4 = and i32 %2, %3
  %5 = xor i32 %2, -1
  %6 = and i32 %2, 1069547520
  %7 = and i32 %5, %3
  %8 = or i32 %6, %7
  %9 = bitcast i32 %8 to float
  %10 = bitcast float %b to i32
  %11 = and i32 %5, %10
  %12 = or i32 %6, %11
  %13 = bitcast i32 %12 to float
  %14 = call float @ctfp_full_div_f32v1_11(float %9, float %13)
  %15 = bitcast float %14 to i32
  %16 = and i32 %5, %15
  %17 = or i32 %4, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_11(float %a, float %b) #2 {
;@ requires (full_div_f32_pre11 %a %b)
;@ ensures  (full_div_f32_post11 %ret %a %b)
  %1 = fcmp oeq float 0.000000e+00, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = xor i32 %2, -1
  %4 = and i32 %2, 1069547520
  %5 = bitcast float %a to i32
  %6 = and i32 %3, %5
  %7 = or i32 %4, %6
  %8 = bitcast i32 %7 to float
  %9 = bitcast float %b to i32
  %10 = and i32 %3, %9
  %11 = or i32 %4, %10
  %12 = bitcast i32 %11 to float
  %13 = call float @ctfp_full_div_f32v1_12(float %8, float %12)
  %14 = bitcast float %13 to i32
  %15 = and i32 %3, %14
  %16 = bitcast i32 %15 to float
  ret float %16
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_12(float %a, float %b) #2 {
;@ requires (full_div_f32_pre12 %a %b)
;@ ensures  (full_div_f32_post12 %ret %a %b)
  %1 = fcmp oeq float 0x7FF0000000000000, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = and i32 %2, 2139095040
  %4 = xor i32 %2, -1
  %5 = and i32 %2, 1069547520
  %6 = bitcast float %a to i32
  %7 = and i32 %4, %6
  %8 = or i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = bitcast float %b to i32
  %11 = and i32 %4, %10
  %12 = or i32 %5, %11
  %13 = bitcast i32 %12 to float
  %14 = call float @ctfp_full_div_f32v1_13(float %9, float %13)
  %15 = bitcast float %14 to i32
  %16 = and i32 %4, %15
  %17 = or i32 %3, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_13(float %a, float %b) #2 {
;@ requires (full_div_f32_pre13 %a %b)
;@ ensures  (full_div_f32_post13 %ret %a %b)
  %1 = call float @fdiv_sig(float %a, float %b)
  ret float %1
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_5(float %a, float %b) #2 {
;@ requires (full_div_f32_pre5 %a %b)
;@ ensures  (full_div_f32_post5 %ret %a %b)
  %1 = fcmp oeq float 0x7FF0000000000000, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = fcmp oeq float 0.000000e+00, %b
  %4 = select i1 %3, i32 -1, i32 0
  %5 = or i32 %2, %4
  %6 = and i32 %5, 2139095040
  %7 = xor i32 %5, -1
  %8 = and i32 %5, 1069547520
  %9 = bitcast float %a to i32
  %10 = and i32 %7, %9
  %11 = or i32 %8, %10
  %12 = bitcast i32 %11 to float
  %13 = bitcast float %b to i32
  %14 = and i32 %7, %13
  %15 = or i32 %8, %14
  %16 = bitcast i32 %15 to float
  %17 = call float @ctfp_full_div_f32v1_14(float %12, float %16)
  %18 = bitcast float %17 to i32
  %19 = and i32 %7, %18
  %20 = or i32 %6, %19
  %21 = bitcast i32 %20 to float
  ret float %21
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_14(float %a, float %b) #2 {
;@ requires (full_div_f32_pre14 %a %b)
;@ ensures  (full_div_f32_post14 %ret %a %b)
  %1 = fcmp oeq float 0.000000e+00, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = fcmp oeq float 0x7FF0000000000000, %b
  %4 = select i1 %3, i32 -1, i32 0
  %5 = or i32 %2, %4
  %6 = xor i32 %5, -1
  %7 = and i32 %5, 1069547520
  %8 = bitcast float %a to i32
  %9 = and i32 %6, %8
  %10 = or i32 %7, %9
  %11 = bitcast i32 %10 to float
  %12 = bitcast float %b to i32
  %13 = and i32 %6, %12
  %14 = or i32 %7, %13
  %15 = bitcast i32 %14 to float
  %16 = call float @ctfp_full_div_f32v1_15(float %11, float %15)
  %17 = bitcast float %16 to i32
  %18 = and i32 %6, %17
  %19 = bitcast i32 %18 to float
  ret float %19
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_15(float %a, float %b) #2 {
;@ requires (full_div_f32_pre15 %a %b)
;@ ensures  (full_div_f32_post15 %ret %a %b)
  %1 = bitcast float %b to i32
  %2 = and i32 %1, 2139095040
  %3 = bitcast i32 %2 to float
  %4 = call float @fdiv_exp(float %a, float %3)
  %5 = and i32 %1, 8388607
  %6 = or i32 %5, 1065353216
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_full_div_f32v1_16(float %4, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_16(float %a, float %b) #2 {
;@ requires (full_div_f32_pre16 %a %b)
;@ ensures  (full_div_f32_post16 %ret %a %b)
  %1 = fcmp oeq float %b, 1.000000e+00
  %2 = select i1 %1, i32 -1, i32 0
  %3 = bitcast float %a to i32
  %4 = and i32 %2, %3
  %5 = xor i32 %2, -1
  %6 = and i32 %2, 1069547520
  %7 = and i32 %5, %3
  %8 = or i32 %6, %7
  %9 = bitcast i32 %8 to float
  %10 = bitcast float %b to i32
  %11 = and i32 %5, %10
  %12 = or i32 %6, %11
  %13 = bitcast i32 %12 to float
  %14 = call float @ctfp_full_div_f32v1_17(float %9, float %13)
  %15 = bitcast float %14 to i32
  %16 = and i32 %5, %15
  %17 = or i32 %4, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_17(float %a, float %b) #2 {
;@ requires (full_div_f32_pre17 %a %b)
;@ ensures  (full_div_f32_post17 %ret %a %b)
  %1 = fcmp oeq float 0.000000e+00, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = xor i32 %2, -1
  %4 = and i32 %2, 1069547520
  %5 = bitcast float %a to i32
  %6 = and i32 %3, %5
  %7 = or i32 %4, %6
  %8 = bitcast i32 %7 to float
  %9 = bitcast float %b to i32
  %10 = and i32 %3, %9
  %11 = or i32 %4, %10
  %12 = bitcast i32 %11 to float
  %13 = call float @ctfp_full_div_f32v1_18(float %8, float %12)
  %14 = bitcast float %13 to i32
  %15 = and i32 %3, %14
  %16 = bitcast i32 %15 to float
  ret float %16
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_18(float %a, float %b) #2 {
;@ requires (full_div_f32_pre18 %a %b)
;@ ensures  (full_div_f32_post18 %ret %a %b)
  %1 = fcmp oeq float 0x7FF0000000000000, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = and i32 %2, 2139095040
  %4 = xor i32 %2, -1
  %5 = and i32 %2, 1069547520
  %6 = bitcast float %a to i32
  %7 = and i32 %4, %6
  %8 = or i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = bitcast float %b to i32
  %11 = and i32 %4, %10
  %12 = or i32 %5, %11
  %13 = bitcast i32 %12 to float
  %14 = call float @ctfp_full_div_f32v1_19(float %9, float %13)
  %15 = bitcast float %14 to i32
  %16 = and i32 %4, %15
  %17 = or i32 %3, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_19(float %a, float %b) #2 {
;@ requires (full_div_f32_pre19 %a %b)
;@ ensures  (full_div_f32_post19 %ret %a %b)
  %1 = call float @fdiv_sig(float %a, float %b)
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

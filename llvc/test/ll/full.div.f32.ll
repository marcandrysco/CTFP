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
  %1 = call float @ctfp_full_div_f32v1_1(float %a, float %b)
  %2 = bitcast float %a to i32
  %3 = bitcast float %b to i32
  %4 = xor i32 %2, %3
  %5 = bitcast i32 %4 to float
  %6 = call float @llvm.copysign.f32(float %1, float %5)
  ret float %6
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
  %8 = call float @llvm.copysign.f32(float %7, float %a)
  %9 = call float @ctfp_full_div_f32v1_2(float %8, float %b)
  ret float %9
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
  %8 = call float @llvm.copysign.f32(float %7, float %b)
  %9 = call float @ctfp_full_div_f32v1_3(float %a, float %8)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_3(float %a, float %b) #2 {
;@ requires (full_div_f32_pre3 %a %b)
;@ ensures  (full_div_f32_post3 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp ogt float %1, 2.500000e-01
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp ogt float %4, 2.500000e-01
  %6 = select i1 %5, i32 -1, i32 0
;@ assume (split %5)
  %7 = and i32 %3, %6
  %8 = and i32 %7, 1023410176
  %9 = xor i32 %7, -1
  %10 = and i32 %9, 1065353216
  %11 = or i32 %8, %10
  %12 = bitcast i32 %11 to float
  %13 = fmul float %a, %12
  %14 = fmul float %b, %12
  %15 = call float @ctfp_full_div_f32v1_4(float %13, float %14)
  ret float %15
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_4(float %a, float %b) #2 {
;@ requires (full_div_f32_pre4 %a %b)
;@ ensures  (full_div_f32_post4 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp ogt float %1, 4.000000e+00
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp olt float %4, 1.000000e+00
  %6 = select i1 %5, i32 -1, i32 0
;@ assume (split %5)
  %7 = and i32 %3, %6
  %8 = and i32 %7, 1082130432
  %9 = xor i32 %7, -1
  %10 = and i32 %9, 1065353216
  %11 = or i32 %8, %10
  %12 = bitcast i32 %11 to float
  %13 = fmul float %b, %12
  %14 = call float @ctfp_full_div_f32v1_5(float %a, float %13)
  %15 = fmul float %14, %12
  ret float %15
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_5(float %a, float %b) #2 {
;@ requires (full_div_f32_pre5 %a %b)
;@ ensures  (full_div_f32_post5 %ret %a %b)
  %1 = fmul float %a, 0x47D0000000000000
  %2 = fmul float %1, 8.000000e+00
  %3 = call float @llvm.fabs.f32(float %2)
  %4 = fcmp une float %3, %3
  %5 = select i1 %4, i32 -1, i32 0
  %6 = call float @llvm.fabs.f32(float %b)
  %7 = fcmp une float %6, %6
  %8 = select i1 %7, i32 -1, i32 0
  %9 = fcmp oeq float 0x7FF0000000000000, %3
  %10 = select i1 %9, i32 -1, i32 0
  %11 = fcmp oeq float 0x7FF0000000000000, %6
  %12 = select i1 %11, i32 -1, i32 0
  %13 = and i32 %10, %12
  %14 = fcmp oeq float 0.000000e+00, %3
  %15 = select i1 %14, i32 -1, i32 0
  %16 = fcmp oeq float 0.000000e+00, %6
  %17 = select i1 %16, i32 -1, i32 0
  %18 = and i32 %15, %17
  %19 = or i32 %13, %18
  %20 = or i32 %8, %19
  %21 = or i32 %5, %20
  %22 = and i32 %21, 2143289344
  %23 = xor i32 %21, -1
  %24 = and i32 %21, 1069547520
  %25 = bitcast float %2 to i32
  %26 = and i32 %23, %25
  %27 = or i32 %24, %26
  %28 = bitcast i32 %27 to float
  %29 = bitcast float %b to i32
  %30 = and i32 %23, %29
  %31 = or i32 %24, %30
  %32 = bitcast i32 %31 to float
  %33 = call float @ctfp_full_div_f32v1_6(float %28, float %32)
  %34 = bitcast float %33 to i32
  %35 = and i32 %23, %34
  %36 = or i32 %22, %35
  %37 = bitcast i32 %36 to float
  %38 = call float @llvm.fabs.f32(float %37)
  %39 = fcmp ogt float %38, 0.000000e+00
  %40 = select i1 %39, i32 -1, i32 0
  %41 = fcmp olt float %38, 8.000000e+00
  %42 = select i1 %41, i32 -1, i32 0
  %43 = and i32 %40, %42
  %44 = xor i32 %43, -1
  %45 = bitcast float %a to i32
  %46 = and i32 %44, %45
  %47 = bitcast i32 %46 to float
  %48 = and i32 %43, 1065353216
  %49 = and i32 %44, %29
  %50 = or i32 %48, %49
  %51 = bitcast i32 %50 to float
  %52 = call float @ctfp_full_div_f32v1_7(float %47, float %51)
  %53 = call float @llvm.copysign.f32(float %52, float %37)
  %54 = bitcast float %53 to i32
  %55 = and i32 %43, %54
  %56 = bitcast float %52 to i32
  %57 = and i32 %44, %56
  %58 = or i32 %55, %57
  %59 = bitcast i32 %58 to float
  ret float %59
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_6(float %a, float %b) #2 {
;@ requires (full_div_f32_pre6 %a %b)
;@ ensures  (full_div_f32_post6 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0x7FF0000000000000, %1
  %3 = select i1 %2, i32 -1, i32 0
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp oeq float 0.000000e+00, %4
  %6 = select i1 %5, i32 -1, i32 0
  %7 = or i32 %3, %6
  %8 = and i32 %7, 2139095040
  %9 = xor i32 %7, -1
  %10 = and i32 %7, 1069547520
  %11 = bitcast float %a to i32
  %12 = and i32 %9, %11
  %13 = or i32 %10, %12
  %14 = bitcast i32 %13 to float
  %15 = bitcast float %b to i32
  %16 = and i32 %9, %15
  %17 = or i32 %10, %16
  %18 = bitcast i32 %17 to float
  %19 = call float @ctfp_full_div_f32v1_15(float %14, float %18)
  %20 = bitcast float %19 to i32
  %21 = and i32 %9, %20
  %22 = or i32 %8, %21
  %23 = bitcast i32 %22 to float
  ret float %23
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_7(float %a, float %b) #2 {
;@ requires (full_div_f32_pre7 %a %b)
;@ ensures  (full_div_f32_post7 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp une float %1, %1
  %3 = select i1 %2, i32 -1, i32 0
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp une float %4, %4
  %6 = select i1 %5, i32 -1, i32 0
  %7 = fcmp oeq float 0x7FF0000000000000, %1
  %8 = select i1 %7, i32 -1, i32 0
  %9 = fcmp oeq float 0x7FF0000000000000, %4
  %10 = select i1 %9, i32 -1, i32 0
  %11 = and i32 %8, %10
  %12 = fcmp oeq float 0.000000e+00, %1
  %13 = select i1 %12, i32 -1, i32 0
  %14 = fcmp oeq float 0.000000e+00, %4
  %15 = select i1 %14, i32 -1, i32 0
  %16 = and i32 %13, %15
  %17 = or i32 %11, %16
  %18 = or i32 %6, %17
  %19 = or i32 %3, %18
  %20 = and i32 %19, 2143289344
  %21 = xor i32 %19, -1
  %22 = and i32 %19, 1069547520
  %23 = bitcast float %a to i32
  %24 = and i32 %21, %23
  %25 = or i32 %22, %24
  %26 = bitcast i32 %25 to float
  %27 = bitcast float %b to i32
  %28 = and i32 %21, %27
  %29 = or i32 %22, %28
  %30 = bitcast i32 %29 to float
;@ assume (spliteq32 %a %26)
;@ assume (spliteq32 %b %30)
  %31 = call float @ctfp_full_div_f32v1_8(float %26, float %30)
  %32 = bitcast float %31 to i32
  %33 = and i32 %21, %32
  %34 = or i32 %20, %33
  %35 = bitcast i32 %34 to float
  ret float %35
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_8(float %a, float %b) #2 {
;@ requires (full_div_f32_pre8 %a %b)
;@ ensures  (full_div_f32_post8 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0x7FF0000000000000, %1
  %3 = select i1 %2, i32 -1, i32 0
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp oeq float 0.000000e+00, %4
  %6 = select i1 %5, i32 -1, i32 0
  %7 = or i32 %3, %6
  %8 = and i32 %7, 2139095040
  %9 = xor i32 %7, -1
  %10 = and i32 %7, 1069547520
  %11 = bitcast float %a to i32
  %12 = and i32 %9, %11
  %13 = or i32 %10, %12
  %14 = bitcast i32 %13 to float
  %15 = bitcast float %b to i32
  %16 = and i32 %9, %15
  %17 = or i32 %10, %16
  %18 = bitcast i32 %17 to float
;@ assume (spliteq32 %a %14)
;@ assume (spliteq32 %b %18)
  %19 = call float @ctfp_full_div_f32v1_9(float %14, float %18)
  %20 = bitcast float %19 to i32
  %21 = and i32 %9, %20
  %22 = or i32 %8, %21
  %23 = bitcast i32 %22 to float
  ret float %23
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_9(float %a, float %b) #2 {
;@ requires (full_div_f32_pre9 %a %b)
;@ ensures  (full_div_f32_post9 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0.000000e+00, %1
  %3 = select i1 %2, i32 -1, i32 0
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp oeq float 0x7FF0000000000000, %4
  %6 = select i1 %5, i32 -1, i32 0
  %7 = or i32 %3, %6
  %8 = xor i32 %7, -1
  %9 = and i32 %7, 1069547520
  %10 = bitcast float %a to i32
  %11 = and i32 %8, %10
  %12 = or i32 %9, %11
  %13 = bitcast i32 %12 to float
  %14 = bitcast float %b to i32
  %15 = and i32 %8, %14
  %16 = or i32 %9, %15
  %17 = bitcast i32 %16 to float
;@ assume (spliteq32 %a %13)
;@ assume (spliteq32 %b %17)
  %18 = call float @ctfp_full_div_f32v1_10(float %13, float %17)
  %19 = bitcast float %18 to i32
  %20 = and i32 %8, %19
  %21 = bitcast i32 %20 to float
  ret float %21
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_10(float %a, float %b) #2 {
;@ requires (full_div_f32_pre10 %a %b)
;@ ensures  (full_div_f32_post10 %ret %a %b)
  %1 = bitcast float %b to i32
  %2 = and i32 %1, -8388608
  %3 = bitcast i32 %2 to float
  %4 = call float @fdiv_exp(float %a, float %3)
  %5 = and i32 %1, 8388607
  %6 = or i32 %5, 1065353216
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_full_div_f32v1_11(float %4, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_11(float %a, float %b) #2 {
;@ requires (full_div_f32_pre11 %a %b)
;@ ensures  (full_div_f32_post11 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp oeq float %1, 1.000000e+00
  %3 = select i1 %2, i32 -1, i32 0
  %4 = bitcast float %a to i32
  %5 = and i32 %3, %4
  %6 = xor i32 %3, -1
  %7 = and i32 %3, 1069547520
  %8 = and i32 %6, %4
  %9 = or i32 %7, %8
  %10 = bitcast i32 %9 to float
  %11 = bitcast float %b to i32
  %12 = and i32 %6, %11
  %13 = or i32 %7, %12
  %14 = bitcast i32 %13 to float
  %15 = call float @ctfp_full_div_f32v1_12(float %10, float %14)
  %16 = bitcast float %15 to i32
  %17 = and i32 %6, %16
  %18 = or i32 %5, %17
  %19 = bitcast i32 %18 to float
  ret float %19
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_12(float %a, float %b) #2 {
;@ requires (full_div_f32_pre12 %a %b)
;@ ensures  (full_div_f32_post12 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0.000000e+00, %1
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = xor i32 %3, -1
  %5 = and i32 %3, 1069547520
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
  %17 = bitcast i32 %16 to float
  ret float %17
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_13(float %a, float %b) #2 {
;@ requires (full_div_f32_pre13 %a %b)
;@ ensures  (full_div_f32_post13 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0x7FF0000000000000, %1
  %3 = select i1 %2, i32 -1, i32 0
  %4 = and i32 %3, 2139095040
  %5 = xor i32 %3, -1
  %6 = and i32 %3, 1069547520
  %7 = bitcast float %a to i32
  %8 = and i32 %5, %7
  %9 = or i32 %6, %8
  %10 = bitcast i32 %9 to float
  %11 = bitcast float %b to i32
  %12 = and i32 %5, %11
  %13 = or i32 %6, %12
  %14 = bitcast i32 %13 to float
  %15 = call float @ctfp_full_div_f32v1_14(float %10, float %14)
  %16 = bitcast float %15 to i32
  %17 = and i32 %5, %16
  %18 = or i32 %4, %17
  %19 = bitcast i32 %18 to float
  ret float %19
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_14(float %a, float %b) #2 {
;@ requires (full_div_f32_pre14 %a %b)
;@ ensures  (full_div_f32_post14 %ret %a %b)
  %1 = call float @fdiv_sig(float %a, float %b)
  ret float %1
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_15(float %a, float %b) #2 {
;@ requires (full_div_f32_pre15 %a %b)
;@ ensures  (full_div_f32_post15 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0.000000e+00, %1
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = call float @llvm.fabs.f32(float %b)
  %5 = fcmp oeq float 0x7FF0000000000000, %4
  %6 = select i1 %5, i32 -1, i32 0
;@ assume (split %5)
  %7 = or i32 %3, %6
  %8 = xor i32 %7, -1
  %9 = and i32 %7, 1069547520
  %10 = bitcast float %a to i32
  %11 = and i32 %8, %10
  %12 = or i32 %9, %11
  %13 = bitcast i32 %12 to float
  %14 = bitcast float %b to i32
  %15 = and i32 %8, %14
  %16 = or i32 %9, %15
  %17 = bitcast i32 %16 to float
;@ assume (spliteq32 %13 %a)
;@ assume (spliteq32 %17 %b)
  %18 = call float @ctfp_full_div_f32v1_16(float %13, float %17)
  %19 = bitcast float %18 to i32
  %20 = and i32 %8, %19
  %21 = bitcast i32 %20 to float
  ret float %21
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_16(float %a, float %b) #2 {
;@ requires (full_div_f32_pre16 %a %b)
;@ ensures  (full_div_f32_post16 %ret %a %b)
  %1 = bitcast float %b to i32
  %2 = and i32 %1, -8388608
  %3 = bitcast i32 %2 to float
  %4 = call float @fdiv_exp(float %a, float %3)
  %5 = and i32 %1, 8388607
  %6 = or i32 %5, 1065353216
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_full_div_f32v1_17(float %4, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_17(float %a, float %b) #2 {
;@ requires (full_div_f32_pre17 %a %b)
;@ ensures  (full_div_f32_post17 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp oeq float %1, 1.000000e+00
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = bitcast float %a to i32
  %5 = and i32 %3, %4
  %6 = xor i32 %3, -1
  %7 = and i32 %3, 1069547520
  %8 = and i32 %6, %4
  %9 = or i32 %7, %8
  %10 = bitcast i32 %9 to float
  %11 = bitcast float %b to i32
  %12 = and i32 %6, %11
  %13 = or i32 %7, %12
  %14 = bitcast i32 %13 to float
  %15 = call float @ctfp_full_div_f32v1_18(float %10, float %14)
  %16 = bitcast float %15 to i32
  %17 = and i32 %6, %16
  %18 = or i32 %5, %17
  %19 = bitcast i32 %18 to float
  ret float %19
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_18(float %a, float %b) #2 {
;@ requires (full_div_f32_pre18 %a %b)
;@ ensures  (full_div_f32_post18 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0.000000e+00, %1
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = xor i32 %3, -1
  %5 = and i32 %3, 1069547520
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
  %17 = bitcast i32 %16 to float
  ret float %17
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_19(float %a, float %b) #2 {
;@ requires (full_div_f32_pre19 %a %b)
;@ ensures  (full_div_f32_post19 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp oeq float 0x7FF0000000000000, %1
  %3 = select i1 %2, i32 -1, i32 0
;@ assume (split %2)
  %4 = and i32 %3, 2139095040
  %5 = xor i32 %3, -1
  %6 = and i32 %3, 1069547520
  %7 = bitcast float %a to i32
  %8 = and i32 %5, %7
  %9 = or i32 %6, %8
  %10 = bitcast i32 %9 to float
  %11 = bitcast float %b to i32
  %12 = and i32 %5, %11
  %13 = or i32 %6, %12
  %14 = bitcast i32 %13 to float
  %15 = call float @ctfp_full_div_f32v1_20(float %10, float %14)
  %16 = bitcast float %15 to i32
  %17 = and i32 %5, %16
  %18 = or i32 %4, %17
  %19 = bitcast i32 %18 to float
  ret float %19
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_div_f32v1_20(float %a, float %b) #2 {
;@ requires (full_div_f32_pre20 %a %b)
;@ ensures  (full_div_f32_post20 %ret %a %b)
  %1 = call float @fdiv_sig(float %a, float %b)
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

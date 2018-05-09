; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.sqrt.f32(float) #0
;@ requires (fsqrt32_pre %a)
;@ ensures (fsqrt32_post %ret %a)

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre0 %a)
;@ ensures  (restrict_sqrt_f32_post0 %ret %a)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %a to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_restrict_sqrt_f32v1_1(float %7)
  %9 = call float @llvm.copysign.f32(float %8, float %a)
  %10 = bitcast float %9 to i32
  %11 = and i32 %3, %10
  %12 = bitcast float %8 to i32
  %13 = and i32 %4, %12
  %14 = or i32 %11, %13
  %15 = bitcast i32 %14 to float
  ret float %15
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1_1(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre1 %a)
;@ ensures  (restrict_sqrt_f32_post1 %ret %a)
  %1 = fcmp une float %a, %a
  %2 = select i1 %1, i32 -1, i32 0
  %3 = and i32 %2, 2143289344
  %4 = xor i32 %2, -1
  %5 = and i32 %2, 1069547520
  %6 = bitcast float %a to i32
  %7 = and i32 %4, %6
  %8 = or i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = call float @ctfp_restrict_sqrt_f32v1_2(float %9)
  %11 = bitcast float %10 to i32
  %12 = and i32 %4, %11
  %13 = or i32 %3, %12
  %14 = bitcast i32 %13 to float
  ret float %14
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1_2(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre2 %a)
;@ ensures  (restrict_sqrt_f32_post2 %ret %a)
  %1 = fcmp oeq float %a, 0x7FF0000000000000
  %2 = select i1 %1, i32 -1, i32 0
  %3 = and i32 %2, 2139095040
  %4 = xor i32 %2, -1
  %5 = and i32 %2, 1069547520
  %6 = bitcast float %a to i32
  %7 = and i32 %4, %6
  %8 = or i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = call float @ctfp_restrict_sqrt_f32v1_3(float %9)
  %11 = bitcast float %10 to i32
  %12 = and i32 %4, %11
  %13 = or i32 %3, %12
  %14 = bitcast i32 %13 to float
  ret float %14
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1_3(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre3 %a)
;@ ensures  (restrict_sqrt_f32_post3 %ret %a)
  %1 = fcmp olt float %a, 0.000000e+00
  %2 = select i1 %1, i32 -1, i32 0
  %3 = and i32 %2, 2143289344
  %4 = xor i32 %2, -1
  %5 = and i32 %2, 1069547520
  %6 = bitcast float %a to i32
  %7 = and i32 %4, %6
  %8 = or i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = call float @ctfp_restrict_sqrt_f32v1_4(float %9)
  %11 = bitcast float %10 to i32
  %12 = and i32 %4, %11
  %13 = or i32 %3, %12
  %14 = bitcast i32 %13 to float
  ret float %14
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1_4(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre4 %a)
;@ ensures  (restrict_sqrt_f32_post4 %ret %a)
  %1 = fcmp oeq float %a, 0.000000e+00
  %2 = select i1 %1, i32 -1, i32 0
  %3 = bitcast float %a to i32
  %4 = and i32 %2, %3
  %5 = xor i32 %2, -1
  %6 = and i32 %2, 1069547520
  %7 = and i32 %5, %3
  %8 = or i32 %6, %7
  %9 = bitcast i32 %8 to float
  %10 = call float @ctfp_restrict_sqrt_f32v1_5(float %9)
  %11 = bitcast float %10 to i32
  %12 = and i32 %5, %11
  %13 = or i32 %4, %12
  %14 = bitcast i32 %13 to float
  ret float %14
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1_5(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre5 %a)
;@ ensures  (restrict_sqrt_f32_post5 %ret %a)
  %1 = bitcast float %a to i32
  %2 = and i32 %1, 16777215
  %3 = bitcast i32 %2 to float
  %4 = fcmp oeq float %3, 0x3810000000000000
  %5 = select i1 %4, i32 -1, i32 0
  %6 = or i32 %1, 1
  %7 = and i32 %5, %6
  %8 = xor i32 %5, -1
  %9 = and i32 %8, %1
  %10 = or i32 %7, %9
  %11 = bitcast i32 %10 to float
  %12 = call float @ctfp_restrict_sqrt_f32v1_6(float %11)
  %13 = bitcast float %12 to i32
  %14 = and i32 %13, -2
  %15 = and i32 %5, %14
  %16 = and i32 %8, %13
  %17 = or i32 %15, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_sqrt_f32v1_6(float %a) #2 {
;@ requires (restrict_sqrt_f32_pre6 %a)
;@ ensures  (restrict_sqrt_f32_post6 %ret %a)
  %1 = call float @llvm.sqrt.f32(float %a)
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

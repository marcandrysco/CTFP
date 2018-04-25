; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (fp.eq %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 

declare float @fdiv_sig(float, float)
;@ requires (fdiv32sig_pre %a %b)
;@ ensures (fdiv32sig_post %ret %a %b)


; Function Attrs: alwaysinline
define weak float @ctfp_restrict_div_f32v1_8(float %a, float %b) #2 {
;@ requires (restrict_div_f32_pre8 %a %b)
;@ ensures  (restrict_div_f32_post8 %ret %a %b)
  %1 = bitcast float %b to i32
  %2 = and i32 %1, 2139095040
  %3 = bitcast i32 %2 to float
  %4 = fdiv float %a, %3
  %5 = and i32 %1, 8388607
  %6 = or i32 %5, 1065353216
  %7 = bitcast i32 %6 to float
  %8 = call float @ctfp_restrict_div_f32v1_9(float %4, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_div_f32v1_9(float %a, float %b) #2 {
;@ requires (restrict_div_f32_pre9 %a %b)
;@ ensures  (restrict_div_f32_post9 %ret %a %b)
  %1 = fcmp oeq float %b, 0x3FF0000000000000
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
  %14 = call float @ctfp_restrict_div_f32v1_10(float %9, float %13)
  %15 = bitcast float %14 to i32
  %16 = and i32 %5, %15
  %17 = or i32 %4, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_div_f32v1_10(float %a, float %b) #2 {
;@ requires (restrict_div_f32_pre10 %a %b)
;@ ensures  (restrict_div_f32_post10 %ret %a %b)
  %1 = fcmp oeq float %a, 0x0000000000000000
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
  %13 = call float @ctfp_restrict_div_f32v1_11(float %8, float %12)
  %14 = bitcast float %13 to i32
  %15 = and i32 %3, %14
  %16 = bitcast i32 %15 to float
  ret float %16
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_div_f32v1_11(float %a, float %b) #2 {
;@ requires (restrict_div_f32_pre11 %a %b)
;@ ensures  (restrict_div_f32_post11 %ret %a %b)
  %1 = fcmp oeq float %a, 0x7FF0000000000000
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
  %14 = call float @ctfp_restrict_div_f32v1_12(float %9, float %13)
  %15 = bitcast float %14 to i32
  %16 = and i32 %4, %15
  %17 = or i32 %3, %16
  %18 = bitcast i32 %17 to float
  ret float %18
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_div_f32v1_12(float %a, float %b) #2 {
;@ requires (restrict_div_f32_pre12 %a %b)
;@ ensures  (restrict_div_f32_post12 %ret %a %b)
  %1 = call float @fdiv_sig(float %a, float %b)
  ret float %1
}


attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

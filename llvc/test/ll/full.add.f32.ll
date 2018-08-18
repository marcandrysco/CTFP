; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 


; Function Attrs: alwaysinline
define weak float @ctfp_full_add_f32v1(float %a, float %b) #2 {
;@ requires (full_add_f32_pre0 %a %b)
;@ ensures  (full_add_f32_post0 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %a to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %a)
  %9 = call float @ctfp_full_add_f32v1_1(float %8, float %b)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_add_f32v1_1(float %a, float %b) #2 {
;@ requires (full_add_f32_pre1 %a %b)
;@ ensures  (full_add_f32_post1 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %b to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %b)
  %9 = call float @ctfp_full_add_f32v1_2(float %a, float %8)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_add_f32v1_2(float %a, float %b) #2 {
;@ requires (full_add_f32_pre2 %a %b)
;@ ensures  (full_add_f32_post2 %ret %a %b)
  %1 = fmul float %a, 0x4170000000000000
  %2 = fmul float %b, 0x4170000000000000
  %3 = fadd float %1, %2
  %4 = call float @llvm.fabs.f32(float %3)
  %5 = fcmp ogt float %4, 0.000000e+00
  %6 = select i1 %5, i32 -1, i32 0
  %7 = fcmp olt float %4, 0x3990000000000000
  %8 = select i1 %7, i32 -1, i32 0
;@ assume (split %7)
  %9 = and i32 %6, %8
  %10 = xor i32 %9, -1
  %11 = bitcast float %a to i32
  %12 = and i32 %10, %11
  %13 = bitcast i32 %12 to float
  %14 = bitcast float %b to i32
  %15 = and i32 %10, %14
  %16 = bitcast i32 %15 to float
  %17 = call float @ctfp_full_add_f32v1_3(float %13, float %16)
  %18 = call float @llvm.copysign.f32(float %17, float %3)
  %19 = bitcast float %18 to i32
  %20 = and i32 %9, %19
  %21 = bitcast float %17 to i32
  %22 = and i32 %10, %21
  %23 = or i32 %20, %22
  %24 = bitcast i32 %23 to float
  ret float %24
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_add_f32v1_3(float %a, float %b) #2 {
;@ requires (full_add_f32_pre3 %a %b)
;@ ensures  (full_add_f32_post3 %ret %a %b)
  %1 = fadd float %a, %b
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

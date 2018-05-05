; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (fp.eq %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 


; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre0 %a %b)
;@ ensures  (full_mul_f32_post0 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = call float @llvm.fabs.f32(float %b)
  %3 = call float @ctfp_full_mul_f32v1_1(float %1, float %2)
  %4 = bitcast float %a to i32
  %5 = bitcast float %b to i32
  %6 = xor i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %3, float %7)
  ret float %8
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_1(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre1 %a %b)
;@ ensures  (full_mul_f32_post1 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %a to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %a)
  %9 = call float @ctfp_full_mul_f32v1_2(float %8, float %b)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_2(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre2 %a %b)
;@ ensures  (full_mul_f32_post2 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %b to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %b)
  %9 = call float @ctfp_full_mul_f32v1_3(float %a, float %8)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_3(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre3 %a %b)
;@ ensures  (full_mul_f32_post3 %ret %a %b)
  %1 = fmul float %a, 0x47D0000000000000
  %2 = fmul float %1, %b
  %3 = call float @llvm.fabs.f32(float %2)
  %4 = fcmp olt float %3, 1.000000e+00
  %5 = select i1 %4, i32 -1, i32 0
  %6 = xor i32 %5, -1
  %7 = bitcast float %a to i32
  %8 = and i32 %6, %7
  %9 = bitcast i32 %8 to float
  %10 = bitcast float %b to i32
  %11 = and i32 %6, %10
  %12 = bitcast i32 %11 to float
  %13 = call float @ctfp_full_mul_f32v1_4(float %9, float %12)
  ret float %13
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_4(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre4 %a %b)
;@ ensures  (full_mul_f32_post4 %ret %a %b)
  %1 = fmul float %a, %b
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

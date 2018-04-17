; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0


; Function Attrs: alwaysinline
define weak float @ctfp_restrict_mul_f32v1(float %a, float %b) #2 {
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3C00000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %a to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %a)
  %9 = call float @ctfp_restrict_mul_f32v1_1(float %8, float %b)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_mul_f32v1_1(float %a, float %b) #2 {
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3C00000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %b to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %b)
  %9 = call float @ctfp_restrict_mul_f32v1_2(float %a, float %8)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_mul_f32v1_2(float %a, float %b) #2 {
  %1 = fmul float %a, %b
  ret float %1
}


attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

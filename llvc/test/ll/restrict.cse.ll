; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (fp.eq %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures  (= %ret (copysign %arg0 %arg1)) 

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_add_f32v1(float %a, float %b) #1 {
;@ requires true 
;@ ensures  (= %ret (fp_add (fp_trunc addmin %a) (fp_trunc addmin %b)))
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3980000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = bitcast i32 %3 to float
  %5 = xor i32 %3, -1
  %6 = bitcast i32 %5 to float
  %7 = bitcast float %a to i32
  %8 = and i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = call float @llvm.copysign.f32(float %9, float %a)
  %11 = call float @ctfp_restrict_add_f32v1_1(float %10, float %b)
  ret float %11
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_add_f32v1_1(float %a, float %b) #1 {
;@ requires (fp_rng addmin %a)
;@ ensures  (= %ret (fp_add %a (fp_trunc addmin %b)))
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3980000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = bitcast i32 %3 to float
  %5 = bitcast float %4 to i32
  %6 = xor i32 %5, -1
  %7 = bitcast i32 %6 to float
  %8 = bitcast float %7 to i32
  %9 = bitcast float %b to i32
  %10 = and i32 %8, %9
  %11 = bitcast i32 %10 to float
  %12 = call float @llvm.copysign.f32(float %11, float %b)
  %13 = call float @ctfp_restrict_add_f32v1_2(float %a, float %12)
  ret float %13
}

; Function Attrs: alwaysinline
define weak float @ctfp_restrict_add_f32v1_2(float %a, float %b) #1 {
;@ requires (and (fp_rng addmin %a) (fp_rng addmin %b))
;@ ensures  (= %ret (fp_add %a %b))
  %1 = fadd float %a, %b
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }


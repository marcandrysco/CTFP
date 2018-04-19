; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (fp.eq %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 


; Function Attrs: alwaysinline
define weak float @ctfp_restrict_add_f32v1(float %a, float %b) #1 {
;@ requires true 
;@ ensures  (= %ret (fp_add (fp_trunc addmin %a) (fp_trunc addmin %b)))
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3980000000000000
  ;@ assert (= 5 (plus 20 3))
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

define weak float @ctfp_restrict_add_f32v1_1(float %a, float %b) #2 {
;@ requires (fp_rng addmin %a)
;@ ensures  (= %ret (fp_add %a (fp_trunc addmin %b)))
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3980000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = bitcast i32 %3 to float
  %5 = xor i32 %3, -1
  ; %6 = bitcast i32 %5 to float
  %7 = bitcast float %b to i32
  %8 = and i32 %5, %7
  %9 = bitcast i32 %8 to float
  %10 = call float @llvm.copysign.f32(float %9, float %b)
  %11 = call float @ctfp_restrict_add_f32v1_2(float %a, float %10)
  ret float %11
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


; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f32(float, float) #0
;@ requires true 
;@ ensures (= (to_ieee_bv %ret) (bvor (bvand (to_ieee_bv %arg0) #x7fffffff) (bvand (to_ieee_bv %arg1) #x80000000))) 

; Function Attrs: nounwind readnone
declare float @scale_mul(float) #0
;@ requires true
;@ ensures (= %ret (ite (bvule (fp32_exp %arg0) one8) (to_fp_32 (concat zero1 (bvsub (bvadd (fp32_exp muloff) (fp32_exp %arg0)) bias) (fp32_sig %arg0))) inf))

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre0 %a %b)
;@ ensures  (full_mul_f32_post0 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %a)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %a to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %a)
  %9 = call float @ctfp_full_mul_f32v1_1(float %8, float %b)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_1(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre1 %a %b)
;@ ensures  (full_mul_f32_post1 %ret %a %b)
  %1 = call float @llvm.fabs.f32(float %b)
  %2 = fcmp olt float %1, 0x3810000000000000
  %3 = select i1 %2, i32 -1, i32 0
  %4 = xor i32 %3, -1
  %5 = bitcast float %b to i32
  %6 = and i32 %4, %5
  %7 = bitcast i32 %6 to float
  %8 = call float @llvm.copysign.f32(float %7, float %b)
  %9 = call float @ctfp_full_mul_f32v1_2(float %a, float %8)
  ret float %9
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_2(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre2 %a %b)
;@ ensures  (full_mul_f32_post2 %ret %a %b)
  %1 = fmul float %a, 0x47D0000000000000
  %2 = fmul float %1, %b
  %3 = call float @llvm.fabs.f32(float %2)
  %4 = fcmp ogt float %3, 0.000000e+00
  %5 = select i1 %4, i32 -1, i32 0
  %6 = fcmp olt float %3, 1.000000e+00
  %7 = select i1 %6, i32 -1, i32 0
  %8 = and i32 %5, %7
  %9 = xor i32 %8, -1
  %10 = bitcast float %a to i32
  %11 = and i32 %9, %10
  %12 = bitcast i32 %11 to float
  %13 = bitcast float %b to i32
  %14 = and i32 %9, %13
  %15 = bitcast i32 %14 to float
  %16 = call float @ctfp_full_mul_f32v1_3(float %12, float %15)
  %17 = call float @llvm.copysign.f32(float %16, float %2)
  %18 = bitcast float %17 to i32
  %19 = and i32 %8, %18
  %20 = bitcast float %16 to i32
  %21 = and i32 %9, %20
  %22 = or i32 %19, %21
  %23 = bitcast i32 %22 to float
  ret float %23
}

; Function Attrs: alwaysinline
define weak float @ctfp_full_mul_f32v1_3(float %a, float %b) #2 {
;@ requires (full_mul_f32_pre3 %a %b)
;@ ensures  (full_mul_f32_post3 %ret %a %b)
  %1 = fmul float %a, %b
  ret float %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

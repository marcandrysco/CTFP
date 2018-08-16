; Function Attrs: nounwind readnone
declare float @llvm.fabs.f64(float) #0
;@ requires true 
;@ ensures  (= %ret (fp.abs %arg0))

; Function Attrs: nounwind readnone
declare float @llvm.copysign.f64(float, float) #0
;@ requires true 
;@ ensures  (= %ret (fp64_copysign %arg0 %arg1))


; Function Attrs: alwaysinline
define weak double @ctfp_restrict_add_f64v1(double %a, double %b) #2 {
;@ requires (restrict_add_f64_pre0 %a %b)
;@ ensures  (restrict_add_f64_post0 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %a)
  %2 = fcmp olt double %1, 0x360000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %a to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %a)
  %9 = call double @ctfp_restrict_add_f64v1_1(double %8, double %b)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_add_f64v1_1(double %a, double %b) #2 {
;@ requires (restrict_add_f64_pre1 %a %b)
;@ ensures  (restrict_add_f64_post1 %ret %a %b)
  %1 = call double @llvm.fabs.f64(double %b)
  %2 = fcmp olt double %1, 0x360000000000000
  %3 = select i1 %2, i64 -1, i64 0
  %4 = xor i64 %3, -1
  %5 = bitcast double %b to i64
  %6 = and i64 %4, %5
  %7 = bitcast i64 %6 to double
  %8 = call double @llvm.copysign.f64(double %7, double %b)
  %9 = call double @ctfp_restrict_add_f64v1_2(double %a, double %8)
  ret double %9
}

; Function Attrs: alwaysinline
define weak double @ctfp_restrict_add_f64v1_2(double %a, double %b) #2 {
;@ requires (restrict_add_f64_pre2 %a %b)
;@ ensures  (restrict_add_f64_post2 %ret %a %b)
  %1 = fadd double %a, %b
  ret double %1
}

attributes #0 = { nounwind readnone }
attributes #1 = { alwaysinline }

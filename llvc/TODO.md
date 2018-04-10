define weak float @ctfp_restrict_add_f32v1(float %a, float %b) #2 {
    ; (declare-const a Float32)
    ; (declare-const b Float32)
  %1 = call float @llvm.fabs.f32(float %a)
    ; (declare-const r1 Float32)
    ; (assert (fp.eq r1 (fp.abs a)))
  %2 = fcmp olt float %1, 0x3980000000000000
    ; (declare-const r2 Bool)
    ; (assert (= r2 (fp.lt r1 a)))
  %3 = select i1 %2, i32 -1, i32 0
    ; (declare-const r3 Int32)
    ; (assert (= r3 (ite r2 #xffffffff #x00000000)))
  %4 = bitcast i32 %3 to float
    ; (declare-const r4 Float32)
    ; (assert (fp.eq r4 ((_ to_fp 8 24) RNE r3)))
  %5 = xor i32 %3, -1
    ; (declare-const r5 Int32)
    ; (assert (= r5 (bvxor r3 #xffffffff)))
  %6 = bitcast i32 %5 to float
    ; (declare-const r6 Float32)
    ; (assert (fp.eq r6 ((_ to_fp 8 24) RNE r5)))
  %7 = bitcast float %a to i32
    ; (declare-const r7 Int32)
    ; (assert (= r7 (to_ieee_bv a)))
  %8 = and i32 %5, %7
    ; (declare-const r8 Int32)
    ; (assert (= r8 (bvand r5 r7)))
  %9 = bitcast i32 %8 to float
    ; (declare-const r9 Float32)
    ; (assert (fp.eq r9 ((_ to_fp 8 24) RNE r8)))
  %10 = call float @llvm.copysign.f32(float %9, float %a)
  %11 = call float @ctfp_restrict_add_f32v1_1(float %10, float %b)
  ret float %11
}

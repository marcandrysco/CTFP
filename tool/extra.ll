define weak float @ctfp_add1_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_add1_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_sub1_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_sub1_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_mul1_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_mul1_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_div1_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_div1_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_add2_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_add2_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_sub2_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_sub2_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_mul2_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_mul2_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}

define weak float @ctfp_div2_f1_f4(float %a, float %b) {
	%a1 = insertelement <4 x float> undef, float %a, i32 0
	%b1 = insertelement <4 x float> undef, float %b, i32 0
	%r1 = call <4 x float> @ctfp_div2_f4(<4 x float> %a1, <4 x float> %b1)
	%r  = extractelement <4 x float> %r1, i32 0
	ret float %r
}



define weak double @ctfp_add1_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_add1_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_sub1_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_sub1_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_mul1_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_mul1_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_div1_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_div1_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_add2_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_add2_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_sub2_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_sub2_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_mul2_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_mul2_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

define weak double @ctfp_div2_d1_d2(double %a, double %b) {
	%a1 = insertelement <2 x double> undef, double %a, i32 0
	%b1 = insertelement <2 x double> undef, double %b, i32 0
	%r1 = call <2 x double> @ctfp_div2_d2(<2 x double> %a1, <2 x double> %b1)
	%r  = extractelement <2 x double> %r1, i32 0
	ret double %r
}

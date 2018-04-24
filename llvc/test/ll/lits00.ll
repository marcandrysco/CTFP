; Function Attrs: alwaysinline
define weak float @silly(float %a) #1 {
;@ requires true
;@ ensures  (or (= %ret one_point_zero) (= %ret zero_point_zero))
  %1  = fcmp olt float %a, 1.0 
  %2  = select i1 %1, float 0.0, float 1.0 ; make the 1.0 a 10.0 to see UNSAFE
  ret float %2
}

; attributes #0 = { nounwind readnone }
; attributes #1 = { alwaysinline }


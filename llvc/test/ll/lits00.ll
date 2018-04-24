; Function Attrs: alwaysinline
define weak float @silly(float %a) #1 {
;@ requires true
;@ ensures  true
  %1  = fcmp olt float %a, 1.0 
  ret float %1
}

; attributes #0 = { nounwind readnone }
; attributes #1 = { alwaysinline }


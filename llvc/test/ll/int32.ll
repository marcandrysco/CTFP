declare i32 @i32add(i32, i32) #0
;@ requires (and (rng32 #x00000005 %arg0) (rng32 #x0000000a %arg1))
;@ ensures  (= %ret (plus32 %arg0 %arg1))

define i32 @add_1(i32 %a, i32 %b) #0 {
;@ requires true
;@ ensures  (= %ret (plus32 (trunc32 #x00000005 %a) (trunc32 #x0000000a %b)))
  %1 = icmp slt i32 %a, 5
  %2 = select i1 %1, i32 0, i32 %a
  %3 = call i32 @add_2(i32 %2, i32 %b)
  ret i32 %3
}

define i32 @add_2(i32 %a, i32 %b){
;@ requires (rng32 #x00000005 %a)
;@ ensures  (= %ret (plus32 %a (trunc32 #x0000000a %b)))
  %1 = icmp slt i32 %b, 10
  %2 = select i1 %1, i32 0, i32 %b
  %3 = call i32 @add_3(i32 %a, i32 %2)
  ret i32 %3
}

define i32 @add_3(i32 %a, i32 %b){
;@ requires (and (rng32 #x00000005 %a) (rng32 #x0000000a %b))
;@ ensures  (= %ret (plus32 %a %b))
  %1 = call i32 @i32add(i32 %a, i32 %b)
  ret i32 %1
}
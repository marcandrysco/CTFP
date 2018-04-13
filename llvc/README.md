# README


## Build 

- `stack build` 

## Run 

First, generate the .smt2 files, one per function defined in the `.ll` file

```sh
stack exec -- llvc path/to/file.ll
```

Then, run `z3` on the files

```sh
z3 path/to/file.ll.function.smt2
```

## Writing Contracts

Each function must be decorated with a comment describing its pre- and post- condition.
(We can put these elsewhere, use a separate file or whatever later.) 

### Declarations

```ll
; Function Attrs: nounwind readnone
declare float @llvm.fabs.f32(float) #0
;@ requires true 
;@ ensures  (fp.eq %ret (fp.abs %arg0))
```

### Definitions 

```ll
define weak float @ctfp_restrict_add_f32v1(float %a, float %b) #1 {
;@ requires true 
;@ ensures  true
...
}
```

```ll
declare i32 @i32add(i32 %a, i32 %b)
;@ requires (and (rng 5 %a) (rng 10 %b))
;@ ensures  (= %ret (add a b))

definition add_1(i32 %a, i32 %b){
;@ requires true
;@ ensures  (= %ret (plus %a (trunc b))
  %1 = cmp olt %a, 5
  %2 = select i1 %1, i32 0, i32 %a
  %3 = call i32 add_2(i32 %2, %b)
  ret i32 %3
}

definition add_2(i32 %a, i32 %b){
;@ requires (rng 5 %a)
;@ ensures  (= %ret (plus %a (trunc b))
  %1 = cmp olt %b, 10
  %2 = select i1 %1, i32 0, i32 %b
  %3 = call i32 add_3(i32 %a, i32 %2)
  ret i32 %3
}

defintion add_3(i32 %a, i32 %b){
;@ requires (and (rng 5 %a) (rng 10 %b))
;@ ensures  (= %ret (plus a b))
  %1 = i32add i32 %a, %b
  ret i32 %1
}
```
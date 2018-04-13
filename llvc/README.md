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

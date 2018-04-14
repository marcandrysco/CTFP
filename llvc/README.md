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

## Running `llvc`

You can check **all** the functions in a file 

```
$ stack exec -- llvc test/ll/restrict.cse.ll
```

or check a **subset** of the functions 

```
$ stack exec -- llvc test/ll/restrict.cse.ll @ctfp_restrict_add_f32v1
```
rjhala@borscht ~/r/C/llvc (CHECKPOINT)> stack exec -- llvc test/ll/restrict.cse.ll @ctfp_restrict_add_f32v1

llvc: checking "test/ll/restrict.cse.ll"

Goals: @ctfp_restrict_add_f32v1

Yikes, errors found!

test/ll/restrict.cse.ll:27:13-16: Failed ensures check!

        27|    ret float %11
                         ^^^^

(model
  (define-fun r2 () Bool
    false)
  (define-fun r7 () (_ BitVec 32)
    #x7f800000)
  (define-fun r8 () (_ BitVec 32)
    #x7f800000)
  (define-fun rb () Float32
    (_ -oo 8 24))
  (define-fun r9 () Float32
    (fp #b0 #x9d #b11111110000000000000000))
  (define-fun r3 () (_ BitVec 32)
    #x00000000)
  (define-fun r11 () Float32
    (_ -oo 8 24))
  (define-fun ra () Float32
    (_ +oo 8 24))
  (define-fun r4 () Float32
    (_ +zero 8 24))
  (define-fun r5 () (_ BitVec 32)
    #xffffffff)
  (define-fun r10 () Float32
    (fp #b0 #x9d #b00111011111111000000000))
  (define-fun r1 () Float32
    (_ +oo 8 24))
  (define-fun r6 () Float32
    (fp #b1 #x7f #b00000000000000000000000))
  (define-fun fp.to_ieee_bv ((x!0 Float32)) (_ BitVec 32)
    (ite (= x!0 (_ +oo 8 24)) #x7f800004
    (ite (= x!0 (fp #b0 #x9d #b11111110000000000000000)) #x7f804000
      #x7f800004)))
)


## Errors and Models 

If there are **failed** verification conditions, `llvc` will print out 

- the relevant _line_
- the SMT _model_

corresponding to the values that yield the failed check.

```bash

llvc: checking "test/ll/restrict.cse.ll"

Goals: @ctfp_restrict_add_f32v1_1, @ctfp_restrict_add_f32v1_2, @ctfp_restrict_add_f32v1

Yikes, errors found!

test/ll/restrict.cse.ll:27:13-16: Failed ensures check!

        27|    ret float %11
                         ^^^^

(model
  (define-fun r2 () Bool
    false)
  (define-fun r7 () (_ BitVec 32)
    #x7f800000)
  (define-fun r8 () (_ BitVec 32)
    #x7f800000)
  (define-fun rb () Float32
    (_ -oo 8 24))
  (define-fun r9 () Float32
    (fp #b0 #x9d #b11111110000000000000000))
  (define-fun r3 () (_ BitVec 32)
    #x00000000)
  (define-fun r11 () Float32
    (_ -oo 8 24))
  (define-fun ra () Float32
    (_ +oo 8 24))
  (define-fun r4 () Float32
    (_ +zero 8 24))
  (define-fun r5 () (_ BitVec 32)
    #xffffffff)
  (define-fun r10 () Float32
    (fp #b0 #x9d #b00111011111111000000000))
  (define-fun r1 () Float32
    (_ +oo 8 24))
  (define-fun r6 () Float32
    (fp #b1 #x7f #b00000000000000000000000))
  (define-fun fp.to_ieee_bv ((x!0 Float32)) (_ BitVec 32)
    (ite (= x!0 (_ +oo 8 24)) #x7f800004
    (ite (= x!0 (fp #b0 #x9d #b11111110000000000000000)) #x7f804000
      #x7f800004)))
)

test/ll/restrict.cse.ll:47:13-16: Failed ensures check!

        47|    ret float %13
                         ^^^^


(model
  (define-fun r8 () (_ BitVec 32)
    #xbf800000)
  (define-fun r12 () Float32
    (_ +zero 8 24))
  (define-fun r10 () (_ BitVec 32)
    #x00000000)
  (define-fun r6 () (_ BitVec 32)
    #xffffffff)
  (define-fun r2 () Bool
    false)
  (define-fun rb () Float32
    (fp #b0 #x80 #b00000000000100000000000))
  (define-fun r7 () Float32
    (fp #b1 #x7f #b00000000000000000000000))
  (define-fun r9 () (_ BitVec 32)
    #x40000800)
  (define-fun r3 () (_ BitVec 32)
    #x00000000)
  (define-fun r11 () Float32
    (_ +zero 8 24))
  (define-fun ra () Float32
    (fp #b0 #x82 #b00000010001001100000000))
  (define-fun r4 () Float32
    (_ +zero 8 24))
  (define-fun r5 () (_ BitVec 32)
    #x00000000)
  (define-fun r1 () Float32
    (fp #b0 #x80 #b00000000000100000000000))
  (define-fun r13 () Float32
    (fp #b0 #x82 #b00000010001001100000000))
  (define-fun fp.to_ieee_bv ((x!0 Float32)) (_ BitVec 32)
    (ite (= x!0 (fp #b1 #x7f #b00000000000000000000000)) #x7f808000
    (ite (= x!0 (fp #b0 #x80 #b00000000000100000000000)) #x7f801000
    (ite (= x!0 (_ +zero 8 24)) #x7f820000
      #x7f808000))))
)
```
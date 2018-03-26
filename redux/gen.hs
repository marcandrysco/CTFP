{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}


--debug = False
debug = True

prelude =
  "target datalayout = \"e-m:e-i64:64-f80:128-n8:16:32:64-S128\"\n" ++
  "target triple = \"x86_64-pc-linux-gnu\"\n" ++
  "declare float @dbg_fadd_f32(float %a, float %b)\n" ++
  "declare float @dbg_fsub_f32(float %a, float %b)\n" ++
  "declare float @dbg_fmul_f32(float %a, float %b)\n" ++
  "declare float @dbg_fdiv_sig_f32(float %a, float %b)\n" ++
  "declare float @dbg_fdiv_exp_f32(float %a, float %b)\n" ++
  "" ++
  "declare float @llvm.fabs.f32(float %a)\n" ++
  "declare < 2 x float > @llvm.fabs.v2f32(< 2 x float > %a)\n" ++
  "declare < 4 x float > @llvm.fabs.v4f32(< 4 x float > %a)\n" ++
  "declare double @llvm.fabs.f64(double %a)\n" ++
  "declare < 2 x double > @llvm.fabs.v2f64(< 2 x double > %a)\n" ++
  "" ++
  "declare float @llvm.copysign.f32(float %a, float %b)\n" ++
  "declare < 2 x float > @llvm.copysign.v2f32(< 2 x float > %a, < 2 x float > %b)\n" ++
  "declare < 4 x float > @llvm.copysign.v4f32(< 4 x float > %a, < 4 x float > %b)\n" ++
  "declare double @llvm.copysign.f64(double %a, double %b)\n" ++
  "declare < 2 x double > @llvm.copysign.v2f64(< 2 x double > %a, < 2 x double > %b)\n" ++
  "\n"

main = 
  do putStr prelude
     gen_func restrict_add Float1 "ctfp_restrict_add"
     gen_func restrict_sub Float1 "ctfp_restrict_sub"
     gen_func restrict_mul Float1 "ctfp_restrict_mul"
     gen_func restrict_div Float1 "ctfp_restrict_div"
     putStr "\n"


-- Create a call from a function and arguments
func :: ((Expr, Expr) -> Expr) -> (Expr, Expr) -> Expr
func fn (a, b) =
  Call (fn (Arg "a", Arg "b"), a, b)


data Expr
  = Arg      String
  | Int      (String, String)
  | Float    (String, String)
  | Not      (Expr)
  | Abs      (Expr)
  | Or       (Expr, Expr)
  | And      (Expr, Expr)
  | Xor      (Expr, Expr)
  | FAdd     (Expr, Expr)
  | FSub     (Expr, Expr)
  | FMul     (Expr, Expr)
  | FDivSig  (Expr, Expr)
  | FDivExp  (Expr, Expr)
  | FcmpOEQ  (Expr, Expr)
  | FCmpUNE  (Expr, Expr)
  | FcmpOLT  (Expr, Expr)
  | FcmpOGT  (Expr, Expr)
  | CopySign (Expr, Expr)
  | Call     (Expr, Expr, Expr)
  deriving Eq

data Type
  = Float1
  | Float2
  | Float4
  | Double1
  | Double2


-- Function type
--   name :: Int   The function index name.
--   expr :: Expr  The function body.
type Func = (Int, Expr)

-- Queue type
--   idx :: Int     The current index name.
--   fns :: [Func]  The list of queued functions.
type Queue = (Int, [Func])

-- Environment type
--   reg  :: Int     The current register index.
--   ty   :: Type    The generation type.
--   q    :: Queue   The queue of named functions.
--   name :: String  The base function name.
type Env = (Int, Type, Queue, String)


-- get the type from the environment
env_type :: Env -> Type
env_type (_,ty,_,_) = ty

-- gee the function name from the environment
env_func :: Env -> String
env_func (_,_,_,name) = name


class WithBlind e f | e -> f where
  withBlind :: (e -> Expr)    -- ^ test
            -> (e -> e)       -- ^ blinder
            -> f              -- ^ fixer
            -> (e -> Expr)    -- ^ operation
            -> (e -> Expr)    -- ^ blinded-operation

instance WithBlind Expr (Expr -> Expr -> Expr) where
  withBlind cond blind fix op v =
    let b   = cond v
        tmp = ite b (blind v) v
        res = op tmp
        out = ite b (fix v res) res
    in out

instance WithBlind (Expr, Expr) ((Expr, Expr) -> Expr -> Expr) where
  withBlind cond blind fix op v =
    let b   = cond v
        tmp = ite2 b (blind v) v
        res = func op tmp
        out = ite b (fix v res) res
    in out

type FP1   = Expr
type FP2   = (FP1, FP1)
type UnOp  = FP1 -> FP1
type BinOp = FP2 -> FP2




infixr 8 @@

(@@):: ((a -> b) -> (a -> b)) -> (a -> b) -> (a -> b)
tx @@ f = tx f


-- ## HELPERS ## --

-- create a conditional using logic operations
ite :: Expr -> Expr -> Expr -> Expr
ite b x y = 
  if x == y
    then x
    else Or (And (b, x), And (Not b, y))

-- create a conditional on two expressions
ite2 :: Expr -> (Expr,Expr) -> (Expr,Expr) -> (Expr,Expr)
ite2 b (x1,x2) (y1,y2) = (ite b x1 y1, ite b x2 y2)

-- extract the exponent component
get_exp :: Expr -> Expr
get_exp e =
  And (e, Int ("0x7F800000", "0x7FF0000000000000") )

-- extract the significand component
get_sig :: Expr -> Expr
get_sig e =
  Or ( And (e, Int ("0x007FFFFF", "0x000FFFFFFFFFFFFF") ), val_one )

-- compute the sign explicitly for mul/div
do_sign :: (FP2 -> FP1) -> FP2 -> FP1
do_sign op (a, b) =
  withBlind
    (\_ -> val_true)
    (\(u,v) -> (Abs(u), Abs(v)))
    (\_ r -> CopySign(r, Xor (a, b)))
    op
    (a, b)


-- ## STRATEGIES ## --

-- underflow with one input
with_underflow :: FP1 -> (FP1 -> FP1) -> FP1 -> FP1
with_underflow lim =
  withBlind
    (\v -> FcmpOLT(Abs(v), lim))
    (\v -> val_zero)
    (\v r -> CopySign(r, v))

-- underflow only on the first input
with_underflow1 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_underflow1 lim =
  withBlind
    (\(v,_) -> FcmpOLT(Abs(v), lim))
    (\(v, w) -> (CopySign(val_zero, v), w))
    (\_ r -> r)

-- underflow only on the second input
with_underflow2 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_underflow2 lim =
  withBlind
    (\(_,v) -> FcmpOLT(Abs(v), lim))
    (\(w,v) -> (w, CopySign(val_zero, v)))
    (\_ r -> r)

-- overflow only on the first input
with_overflow1 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_overflow1 lim =
  withBlind
    (\(v,_) -> FcmpOGT(Abs(v), lim))
    (\(v, w) -> (val_inf, w))
    (\v r -> r)

-- overflow only on the second input
with_overflow2 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_overflow2 lim =
  withBlind
    (\(_,v) -> FcmpOGT(Abs(v), lim))
    (\(w,v) -> (w, val_inf))
    (\_ r -> r)


with_dummy1 :: FP1 -> FP1 -> FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_dummy1 badIn badOut safeIn op (a, b) =
  withBlind
    (\(v,w) -> FcmpOEQ (v, badIn))
    (\(v,w) -> (safeIn, w))
    (\_ _ -> CopySign(badOut, a))
    op
    (a, b)

cmp_eq (a, b) =
  if a == val_nan
    then FCmpUNE (b, b)
    else if b == val_nan
      then FCmpUNE (a, a)
      else FcmpOEQ (a, b)

-- compare and replace both inputs if matching the bad input
with_dummy' :: FP2 -> FP1 -> FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_dummy' badIn badOut safeIn op (a, b) =
  withBlind
    (\(v,w) -> And(cmp_eq (v, fst badIn), cmp_eq (w, snd badIn)))
    (\(v,w) -> (safeIn, safeIn))
    (\_ _ -> badOut)
    op
    (a, b)

with_dummy1' :: FP1 -> FP1 -> FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_dummy1' badIn badOut safeIn op (a, b) =
  withBlind
    (\(v,_) -> cmp_eq (v, badIn))
    (\(v,w) -> (safeIn, safeIn))
    (\_ _ -> badOut)
    op
    (a, b)

with_dummy2' :: FP1 -> FP1 -> FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_dummy2' badIn badOut safeIn op (a, b) =
  withBlind
    (\(_,w) -> cmp_eq (w, badIn))
    (\(v,w) -> (safeIn, safeIn))
    (\_ _ -> badOut)
    op
    (a, b)

-- divide only by the exponent component of the inputs
div_exp :: (FP2 -> FP1) -> FP2 -> FP1
div_exp =
  withBlind
    (\_ -> val_true)
    (\(w,v) -> (FDivExp(w, get_exp v), get_sig v))
    --(\(w,v) -> (w, get_exp(v)))
    (\v r -> r)

-- prevent division by one using a dummy
div_noop op (a, b) =
  withBlind
    (\(u,v) -> FcmpOEQ(v, val_one))
    (\_ -> (val_dummy, val_dummy))
    (\_ _ -> a)
    op
    (a, b)

-- values
val_true = Int ("-1", "-1")
val_false = Int ("0", "0")
val_zero = Float ( "0.0", "0.0" )
val_one = Float ( "1.0", "1.0" )
val_dummy = Float ( "1.5", "1.5" )
val_nan = Int ("0x7FC00000", "0x7FF8000000000000")
val_inf = Int ("0x7F800000", "0x7FF0000000000000")

-- constants
addmin = Float ( "9.86076131526264760e-32", "2.00416836000897278e-292" )
mulmin = Float ( "1.08420217248550443e-19", "1.49166814624004135e-154" )
divmin = Float ( "1.08420217248550443e-19", "1.49166814624004135e-154" )
divmax = Float ( "9.22337203685477581e+18", "6.70390396497129855e+153" )
fltmin = Float ( "1.17549435082228751e-38", "2.22507385850720138e-308" )

-- ## RESTRICT ## --

-- addition
restrict_add :: FP2 -> FP1
restrict_add =
  with_underflow1 addmin @@
  with_underflow2 addmin @@
  FAdd

-- subtraction
restrict_sub :: FP2 -> FP1
restrict_sub =
  with_underflow1 addmin @@
  with_underflow2 addmin @@
  FSub

-- multiplication
restrict_mul :: FP2 -> FP1
restrict_mul =
  with_underflow1 mulmin @@
  with_underflow2 mulmin @@
  FMul

-- division
restrict_div :: FP2 -> FP1
restrict_div =
  do_sign @@
  with_underflow1 divmin @@
  with_underflow2 divmin @@
  with_overflow1 divmax @@
  with_overflow2 divmax @@
  with_dummy1' val_nan val_nan val_dummy @@
  with_dummy2' val_nan val_nan val_dummy @@
  with_dummy' (val_zero, val_zero) val_nan val_dummy @@
  with_dummy' (val_inf, val_inf) val_nan val_dummy @@
  with_dummy1' val_zero val_zero val_dummy @@
  with_dummy1' val_inf val_inf val_dummy @@
  with_dummy2' val_zero val_inf val_dummy @@
  with_dummy2' val_inf val_zero val_dummy @@
  div_exp @@
  div_noop @@
  with_dummy1' val_zero val_zero val_dummy @@
  with_dummy1' val_inf val_inf val_dummy @@
  --with_dummy2' val_zero val_inf val_dummy @@
  --with_dummy2' val_inf val_zero val_dummy @@
  FDivSig


-- get a name
name :: Env -> Expr -> (Env, String)
name (i, t, (name, fns), n) expr =
  let env' = (i, t, (name+1, (name, expr):fns), n) in
    (env', show name)

-- allocate a register from the environment
alloc :: Env -> (Env, String)
alloc (i, t, q, n) = ((i+1, t, q, n), "%"++(show i))

-- allocate an array of registers from the environment
allocs :: Env -> Int -> (Env, [String])
allocs e n =
  if n == 0
    then (e, [])
    else let ((i,t,q,f),ns) = allocs e (n-1) in
      ((i+1,t,q,f),ns++["%"++(show i)])


-- create a floating point value string
floats :: Env -> String -> String
floats env val =
  case env_type env of
    Float1 -> val
    Float2 -> "< float " ++ val ++ ", float " ++ val ++ " >"
    Float4 -> "< float " ++ val ++ ", float " ++ val ++ ", float " ++ val ++ ", float " ++ val ++ " >"
    Double1 -> val
    Double2 -> "< double " ++ val ++ ", double " ++ val ++ " >"

-- create an integer value string
ints :: Env -> String -> String
ints env val =
  case env_type env of
    Float1 -> val
    Float2 -> "< i32 " ++ val ++ ", i32 " ++ val ++ " >"
    Float4 -> "< i32 " ++ val ++ ", i32 " ++ val ++ ", i32 " ++ val ++ ", i32 " ++ val ++ " >"
    Double1 -> val
    Double2 -> "< i64 " ++ val ++ ", i64 " ++ val ++ " >"


-- create an integer values of all ones
ones :: Env -> String
ones e = ints e "-1"

-- create an integer values of all zeros
zeros :: Env -> String
zeros e = ints e "0"


-- select a string using the type
type2sel :: Type -> (String, String) -> String
type2sel Float1 p = fst p
type2sel Float2 p = fst p
type2sel Float4 p = fst p
type2sel Double1 p = snd p
type2sel Double2 p = snd p

-- select a string using the environment
env2sel :: Env -> (String, String) -> String
env2sel env p = type2sel (env_type env) p

-- convert a type to the floating-point type string
type2flt :: Type -> String
type2flt Float1 = "float"
type2flt Float2 = "< 2 x float >"
type2flt Float4 = "< 4 x float >"
type2flt Double1 = "double"
type2flt Double2 = "< 2 x double >"

-- generate float type string from the environment
env2flt :: Env -> String
env2flt env = type2flt (env_type env)

-- convert a type to the integer type string
type2int :: Type -> String
type2int Float1 = "i32"
type2int Float2 = "< 2 x i32 >"
type2int Float4 = "< 4 x i32 >"
type2int Double1 = "i64"
type2int Double2 = "< 2 x i64 >"

-- generate integer type string from the environment
env2int :: Env -> String
env2int env = type2int (env_type env)

-- convert a type to the boolean type string
type2bool :: Type -> String
type2bool Float1 = "i1"
type2bool Float2 = "< 2 x i1 >"
type2bool Float4 = "< 4 x i1 >"
type2bool Double1 = "i1"
type2bool Double2 = "< 2 x i1 >"

-- generate boolean type string from the environment
env2bool :: Env -> String
env2bool env = type2bool (env_type env)

-- convert a type to the vectorized builtin string
type2vec :: Type -> String
type2vec Float1 = "f32"
type2vec Float2 = "v2f32"
type2vec Float4 = "v4f32"
type2vec Double1 = "f64"
type2vec Double2 = "v2f64"

-- generate vectorized name from the environment
env2vec :: Env -> String
env2vec env = type2vec (env_type env)


gen_unnamed :: [Func] -> Type -> Int -> String -> IO ()
gen_unnamed [] _ _ _ = return ()
gen_unnamed ((nam, expr):fns) t idx fn =
  let ty = type2flt t in
    do putStr $ "define weak " ++ ty ++ " @"++fn++"_" ++ (show nam) ++ "(" ++ ty ++ " %a, " ++ ty ++ " %b) {\n"
       (r,(_,_,(idx',fns'),_)) <- gen_expr (expr, (1, t, (idx, fns), fn))
       putStr $ "ret " ++ ty ++ " " ++ r ++ "\n}\n"
       gen_unnamed fns' t idx' fn

-- generate the code for a function
gen_func :: ((Expr, Expr) -> Expr) -> Type -> String -> IO ()
gen_func f t n = 
  let ty = type2flt t in
    do
       putStr $ "define weak " ++ ty ++ " @" ++ n ++ "(" ++ ty ++ " %a, " ++ ty ++ " %b) {\n"
       (r,(_,_,(idx,fns),n)) <- gen_expr (f (Arg "a", Arg "b"), (1, t, (1, []), n))
       putStr $ "ret " ++ ty ++ " " ++ r ++ "\n}\n"
       gen_unnamed fns t idx n

-- generate code for an arbitrary expression
gen_expr :: (Expr, Env) -> IO (String, Env)
gen_expr (Arg s, env) = return ("%" ++ s, env)
gen_expr (Int val, env) = gen_int (env2sel env val, env)
gen_expr (Float val, env) = return (floats env (env2sel env val), env)
gen_expr (Not a, env) = gen_not (a, env)
gen_expr (Abs a, env) = gen_call1("llvm.fabs." ++ (env2vec env), a, env);
gen_expr (Or (a, b), env) = gen_iop2 ("or", a, b, env)
gen_expr (And (a, b), env) = gen_iop2 ("and", a, b, env)
gen_expr (Xor (a, b), env) = gen_iop2 ("xor", a, b, env)
gen_expr (FAdd (a, b), env) = if debug then gen_call2 ("dbg_fadd_" ++ (env2vec env), a, b, env) else gen_fop2 ("fadd", a, b, env)
gen_expr (FSub (a, b), env) = if debug then gen_call2 ("dbg_fsub_" ++ (env2vec env), a, b, env) else gen_fop2 ("fsub", a, b, env)
gen_expr (FMul (a, b), env) = if debug then gen_call2 ("dbg_fmul_" ++ (env2vec env), a, b, env) else gen_fop2 ("fmul", a, b, env)
gen_expr (FDivSig (a, b), env) = if debug then gen_call2 ("dbg_fdiv_sig_" ++ (env2vec env), a, b, env) else gen_fop2 ("fdiv", a, b, env)
gen_expr (FDivExp (a, b), env) = if debug then gen_call2 ("dbg_fdiv_exp_" ++ (env2vec env), a, b, env) else gen_fop2 ("fdiv", a, b, env)
gen_expr (FcmpOEQ (a, b), env) = gen_fcmp ("fcmp oeq", a, b, env)
gen_expr (FcmpOLT (a, b), env) = gen_fcmp ("fcmp olt", a, b, env)
gen_expr (FcmpOGT (a, b), env) = gen_fcmp ("fcmp ogt", a, b, env)
gen_expr (FCmpUNE (a, b), env) = gen_fcmp ("fcmp une", a, b, env)
gen_expr (CopySign (a, b), env) = gen_call2 ("llvm.copysign." ++ (env2vec env), a, b, env)
gen_expr (Call (fn, a, b),  env) = gen_call (fn, a, b, env)

gen_call :: (Expr, Expr, Expr, Env) -> IO (String, Env)
gen_call (fn, a, b, env) =
  do (ra, env) <- gen_expr (a, env)
     (rb, env) <- gen_expr (b, env)
     let (env',r) = alloc env in
       let (env'',func) = name env' fn in
         let flt = env2flt env'' in 
           do putStr $ r++" = call "++flt++" @"++(env_func env'')++"_"++func++"("++flt++" "++ra++", "++flt++" "++rb++")\n"
              return (r, env'')

-- generate an integer constant
gen_int :: (String, Env) -> IO (String, Env)
gen_int (int, env) =
  let (env',r) = alloc env in
    do putStr $ r++" = bitcast "++(env2int env')++" "++(show (read int::Int))++" to "++(env2flt env')++"\n"
       return (r, env')

-- generate a bitwise not
gen_not :: (Expr, Env) -> IO (String, Env)
gen_not (a, env) =
  do (ra, env) <- gen_expr (a, env)
     let (env',[ra',rt,ro]) = allocs env 3 in
       do putStr $ ra'++" = bitcast "++(env2flt env')++" "++ra++" to "++(env2int env')++"\n"
          putStr $ rt++" = xor "++(env2int env')++" "++ra'++", "++(ones env')++"\n"
          putStr $ ro++" = bitcast "++(env2int env')++" "++rt++" to "++(env2flt env')++"\n"
          return (ro, env')

-- generate code for a two-operand integer operation
gen_iop2 :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_iop2 (op, a, b, env) =
  do (ra, env) <- gen_expr (a, env)
     (rb, env) <- gen_expr (b, env)
     let (env',[ra',rb',rt,ro]) = allocs env 4 in
       do putStr $ ra'++" = bitcast "++(env2flt env)++" "++ra++" to "++(env2int env)++"\n"
          putStr $ rb'++" = bitcast "++(env2flt env)++" "++rb++" to "++(env2int env)++"\n"
          putStr $ rt++" = "++op++" "++(env2int env)++" "++ra'++", "++rb'++"\n"
          putStr $ ro++" = bitcast "++(env2int env)++" "++rt++" to "++(env2flt env)++"\n"
          return (ro, env')

-- generate code for a two-operand floating-point operation
gen_fop2 :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_fop2 (op, a, b, env) =
  do (ra, env) <- gen_expr (a, env)
     (rb, env) <- gen_expr (b, env)
     let (env',ro) = alloc env in
       do putStr $ ro++" = "++op++" "++(env2flt env)++" "++ra++", "++rb++"\n"
          return (ro, env')

-- generate code for a floating-point comparison
gen_fcmp :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_fcmp (cmp, a, b, env) =
  do (ra, env) <- gen_expr (a, env)
     (rb, env) <- gen_expr (b, env)
     let (env', [rt,rs,ro]) = allocs env 3 in
       do putStr $ rt++" = "++cmp++" "++(env2flt env')++" "++ra++", "++rb++"\n"
          putStr $ rs++" = select "++(env2bool env')++" "++rt++", "++(env2int env')++" "++(ones env')++", "++(env2int env')++" "++(zeros env')++"\n"
          putStr $ ro++" = bitcast "++(env2int env')++" "++rs++" to "++(env2flt env')++"\n"
          return (ro, env')

-- create a function call with one argument
gen_call1 :: (String, Expr, Env) -> IO (String, Env)
gen_call1 (fn, a, env) =
  do (ra, env) <- gen_expr (a, env)
     let (env', r) = alloc env in
       do putStr $ r++" = call "++(env2flt env')++" @"++fn++"("++(env2flt env')++" "++ra++")\n"
          return (r, env')

-- create a function call with one argument
gen_call2 :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_call2 (fn, a, b, env) =
  do (ra, env) <- gen_expr (a, env)
     (rb, env) <- gen_expr (b, env)
     let (env', r) = alloc env in
       do putStr $ r++" = call "++(env2flt env')++" @"++fn++"("++(env2flt env')++" "++ra++", "++(env2flt env')++" "++rb++")\n"
          return (r, env')

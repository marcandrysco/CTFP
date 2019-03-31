{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

import Data.List
import System.Environment
import Data.Map (Map)
import qualified Data.Map as Map

-- main entry, just dispatches based on desired generator
main =
  do args <- getArgs
     case args of
       []        -> llvm_main False
       ["debug"] -> llvm_main True
       ["z3"]    -> z3_main
       _         -> putStr "Invalid arguments\n"

-- list of all types we generate
typelist = [Float1, Float2, Float4, Float8, Float16, Double1, Double2, Double4, Double8]
--typelist = [Float1, Float2, Float4, Double1, Double2]
--typelist = [Float1]


bar (a, b) = FMul (FAdd (a, a), FAdd (a, a))
foo (a, b) = FAdd (bar (a, b), Call (bar (Arg "a", Arg "b"), a, b))

main' = llvm_func2 foo Float1 "foo" False


---- ## DATA TYPES ## ----

-- AST data type
data Expr
  = Arg      String
  | Zero
  | One
  | Ones
  | Int      (String, String)
  | Float    (String, String)
  | Not      Expr
  | Abs      Expr
  | Or       (Expr, Expr)
  | And      (Expr, Expr)
  | Xor      (Expr, Expr)
  | FSqrt    Expr
  | FAdd     (Expr, Expr)
  | FSub     (Expr, Expr)
  | FMul     (Expr, Expr)
  | FDivSig  (Expr, Expr)
  | FDivExp  (Expr, Expr)
  | FCmpOEQ  (Expr, Expr)
  | ICmp     (Expr, Expr)
  | FCmpUNE  (Expr, Expr)
  | FCmpOLT  (Expr, Expr)
  | FCmpULT  (Expr, Expr)
  | FCmpOGT  (Expr, Expr)
  | CopySign (Expr, Expr)
  | Call1    (Expr, Expr)
  | Call     (Expr, Expr, Expr)
  | Seq      (Expr, Expr)
  deriving (Eq, Show, Ord)

-- Floating point target type
data Type
  = Float1
  | Float2
  | Float4
  | Float8
  | Float16
  | Double1
  | Double2
  | Double4
  | Double8


-- Function type
--   name :: Int   The function index name.
--   expr :: Expr  The function body.
type Func = (Int, Expr)

-- Queue type
--   idx :: Int     The current index name.
--   fns :: [Func]  The list of queued functions.
type Queue = (Int, [Func])

-- Bind type
--   id  :: String  The variable name.
--   reg :: String  The register name.
type Bind = (String, String)

-- CSE map type
--   map :: Map Expr String   The map from expressions to registers.
type CSE = Map Expr String

-- Environment type
--   reg  :: Int     The current register index.
--   ty   :: Type    The generation type.
--   q    :: Queue   The queue of named functions.
--   name :: String  The base function name.
--   bind :: [Bind]  List of bindings.
--   dbg  :: Bool    Debug flag.
--   cse  :: CSE     CSE map.
type Env = (Int, Type, Queue, String, [Bind], Bool, CSE)


---- ## Z3 GENERATION ## ----

-- main function for z3
z3_main :: IO ()
z3_main =
  do z3_func (testfunc (Arg "a", Arg "b")) Float1 "testfunc"
     return ()

testfunc :: (Expr, Expr) -> Expr
testfunc (a, b) =
  FAdd (a, b)

-- create z3 queries from a function
z3_func :: Expr -> Type -> String -> IO ()
z3_func fn ty nam =
  do putStr "(declare-const a Float32)\n"
     putStr "(declare-const b Float32)\n"
     z3_expr (fn, (env_init ty nam False))
     return ()

-- generate z3 code from an expression
z3_expr :: (Expr, Env) -> IO (String, Env)
z3_expr (Arg nam, env) = return (nam, env)
z3_expr (FAdd (a, b), env) = z3_op2 ("fp.add RNE", a, b, env)
z3_expr (FSub (a, b), env) = z3_op2 ("fp.sub RNE", a, b, env)
z3_expr (FMul (a, b), env) = z3_op2 ("fp.mul RNE", a, b, env)
z3_expr (FDivExp (a, b), env) = z3_op2 ("fp.div RNE", a, b, env)
z3_expr (FDivSig (a, b), env) = z3_op2 ("fp.div RNE", a, b, env)
z3_expr (Or (a, b), env) = z3_op2 ("or32", a, b, env)
z3_expr (And (a, b), env) = z3_op2 ("and32", a, b, env)
z3_expr (Xor (a, b), env) = z3_op2 ("xor32", a, b, env)
z3_expr (Not a, env) = z3_op1 ("xor32", a, env)
z3_expr (Call (fn, a, b),  env) = z3_call (fn, a, b, env)

-- generate z3 code for a one-operand operation
z3_op1 :: (String, Expr, Env) -> IO (String, Env)
z3_op1 (op, a, env) =
  let (env', _:res) = alloc env in
    do (x, env') <- z3_expr (a, env')
       putStr $ "(define-const t"++res++" Float32 ("++op++" "++x++"))\n"
       return (res, env')

-- generate z3 code for a two-operand operation
z3_op2 :: (String, Expr, Expr, Env) -> IO (String, Env)
z3_op2 (op, a, b, env) =
  let (env', _:res) = alloc env in
    do (x, env') <- z3_expr (a, env')
       (y, env') <- z3_expr (b, env')
       putStr $ "(define-const t"++res++" Float32 ("++op++" "++x++" "++y++"))\n"
       return (res, env')

-- generate z3 coe for a call
z3_call :: (Expr, Expr, Expr, Env) -> IO (String, Env)
z3_call (fn, a, b, env) =
  do (x, env) <- z3_expr (a, env)
     (y, env) <- z3_expr (b, env)
     return ("", env)


---- ## LLVM GENERATION ## ----

-- main function for llvm
llvm_main :: Bool -> IO ()
llvm_main dbg = 
  let
    -- fns1 = [ "restrict_sqrt", "full_sqrt" {-, "fast_sqrt"-} ]
    -- fns2 = [ "restrict_add", "restrict_sub", "restrict_mul", "restrict_div", "full_add", "full_sub", "full_mul", "full_div" {-, "fast_add", "fast_sub", "fast_mul", "fast_div"-} ]
    fns1 = [ "restrict_sqrt", "full_sqrt", "fast_sqrt" ]
    fns2 = [ "restrict_add", "restrict_sub", "restrict_mul", "restrict_div", "full_add", "full_sub", "full_mul", "full_div", "fast_add", "fast_sub", "fast_mul", "fast_div" ]
    f ty =
      let
        post = type2post ty
      in
        do llvm_func2 restrict_add  ty ( "ctfp_restrict_add_"  ++ post) dbg
           llvm_func2 restrict_sub  ty ( "ctfp_restrict_sub_"  ++ post) dbg
           llvm_func2 restrict_mul  ty ( "ctfp_restrict_mul_"  ++ post) dbg
           llvm_func2 restrict_div  ty ( "ctfp_restrict_div_"  ++ post) dbg
           llvm_func1 restrict_sqrt ty ( "ctfp_restrict_sqrt_" ++ post) dbg
           llvm_func2 full_add ty  ( "ctfp_full_add_"  ++ post) dbg
           llvm_func2 full_sub ty  ( "ctfp_full_sub_"  ++ post) dbg
           llvm_func2 full_mul ty  ( "ctfp_full_mul_"  ++ post) dbg
           llvm_func2 full_div ty  ( "ctfp_full_div_"  ++ post) dbg
           llvm_func1 full_sqrt ty ( "ctfp_full_sqrt_" ++ post) dbg
           llvm_func2 fast_add ty  ( "ctfp_fast_add_"  ++ post) dbg
           llvm_func2 fast_sub ty  ( "ctfp_fast_sub_"  ++ post) dbg
           llvm_func2 fast_mul ty  ( "ctfp_fast_mul_"  ++ post) dbg
           llvm_func2 fast_div ty  ( "ctfp_fast_div_"  ++ post) dbg
           llvm_func1 fast_sqrt ty ( "ctfp_fast_sqrt_" ++ post) dbg
  in
    do llvm_prelude
       mapM f typelist
       mapM llvm_hack32_1 fns1
       mapM llvm_hack32 fns2
       mapM llvm_hack64_1 fns1
       mapM llvm_hack64 fns2
       return ()

llvm_prelude :: IO ()
llvm_prelude = 
  do putStr $ "target datalayout = \"e-m:e-i64:64-f80:128-n8:16:32:64-S128\"\n"
     putStr $ "target triple = \"x86_64-pc-linux-gnu\"\n"
     putStr $ "attributes #0 = { alwaysinline }\n"
     putStr $ "attributes #1 = { alwaysinline }\n"
     mapM llvm_decls typelist
     return ()
  
llvm_decls :: Type -> IO ()
llvm_decls ty =
  let
    flt = type2flt ty
    post = type2post ty
    vec = type2vec ty
  in
    do putStr $ "declare "++flt++" @dbg_fadd_"++vec++"("++flt++" %a, "++flt++" %b) readnone\n"
       putStr $ "declare "++flt++" @dbg_fsub_"++vec++"("++flt++" %a, "++flt++" %b) readnone\n"
       putStr $ "declare "++flt++" @dbg_fmul_"++vec++"("++flt++" %a, "++flt++" %b) readnone\n"
       putStr $ "declare "++flt++" @dbg_fdiv_sig_"++vec++"("++flt++" %a, "++flt++" %b) readnone\n"
       putStr $ "declare "++flt++" @dbg_fdiv_exp_"++vec++"("++flt++" %a, "++flt++" %b) readnone\n"
       putStr $ "declare "++flt++" @dbg_fsqrt_"++vec++"("++flt++" %a) readnone\n"
       putStr $ "declare "++flt++" @llvm.sqrt."++vec++"("++flt++" %a) readnone\n"
       putStr $ "declare "++flt++" @llvm.fabs."++vec++"("++flt++" %a) readnone\n"
       putStr $ "declare "++flt++" @llvm.copysign."++vec++"("++flt++" %b, "++flt++" %a) readnone\n"

-- hack for generating vectorized functions
llvm_hack32 :: String -> IO ()
llvm_hack32 op =
  do putStr $ "define weak float @ctfp_"++op++"_f32v1_hack(float %a, float %b) #0 {\n"
     putStr $ "  %a1 = insertelement <4 x float> undef, float %a, i32 0\n"
     putStr $ "  %b1 = insertelement <4 x float> undef, float %b, i32 0\n"
     putStr $ "  %r1 = call <4 x float> @ctfp_"++op++"_f32v4(<4 x float> %a1, <4 x float> %b1)\n"
     putStr $ "  %r  = extractelement <4 x float> %r1, i32 0\n"
     putStr $ "  ret float %r\n"
     putStr $ "}\n"
llvm_hack32_1 :: String -> IO ()
llvm_hack32_1 op =
  do putStr $ "define weak float @ctfp_"++op++"_f32v1_hack(float %a) #0 {\n"
     putStr $ "  %a1 = insertelement <4 x float> undef, float %a, i32 0\n"
     putStr $ "  %r1 = call <4 x float> @ctfp_"++op++"_f32v4(<4 x float> %a1)\n"
     putStr $ "  %r  = extractelement <4 x float> %r1, i32 0\n"
     putStr $ "  ret float %r\n"
     putStr $ "}\n"

-- hack for generating vectorized functions
llvm_hack64 :: String -> IO ()
llvm_hack64 op =
  do putStr $ "define weak double @ctfp_"++op++"_f64v1_hack(double %a, double %b) #0 {\n"
     putStr $ "  %a1 = insertelement <2 x double> undef, double %a, i64 0\n"
     putStr $ "  %b1 = insertelement <2 x double> undef, double %b, i64 0\n"
     putStr $ "  %r1 = call <2 x double> @ctfp_"++op++"_f64v2(<2 x double> %a1, <2 x double> %b1)\n"
     putStr $ "  %r  = extractelement <2 x double> %r1, i64 0\n"
     putStr $ "  ret double %r\n"
     putStr $ "}\n"
llvm_hack64_1 :: String -> IO ()
llvm_hack64_1 op =
  do putStr $ "define weak double @ctfp_"++op++"_f64v1_hack(double %a) #0 {\n"
     putStr $ "  %a1 = insertelement <2 x double> undef, double %a, i64 0\n"
     putStr $ "  %r1 = call <2 x double> @ctfp_"++op++"_f64v2(<2 x double> %a1)\n"
     putStr $ "  %r  = extractelement <2 x double> %r1, i64 0\n"
     putStr $ "  ret double %r\n"
     putStr $ "}\n"

-- generate the code for a function
llvm_func :: Expr -> Int -> Type -> String -> Bool -> IO ()
llvm_func fn nargs ty nam dbg = 
  let
    tnam = type2flt ty
    argl = map (\x -> tnam ++ " %" ++ x) ["a","b","c","d"]
  in
    do putStr $ "define weak " ++ tnam ++ " @" ++ nam ++ "(" ++ (intercalate ", " (take nargs argl)) ++ ") #0 {\n"
       (r,(_,_,(idx,fns),n,_,_,_)) <- llvm_expr (fn, env_init ty nam dbg)
       putStr $ "ret " ++ tnam ++ " " ++ r ++ "\n}\n"
       gen_unnamed fns nargs ty idx nam dbg

-- helper for 1-argument functions
llvm_func1 :: (Expr -> Expr) -> Type -> String -> Bool -> IO ()
llvm_func1 fn = llvm_func (fn (Arg "a")) 1

-- helper for 2-argument functions
llvm_func2 :: ((Expr, Expr) -> Expr) -> Type -> String -> Bool -> IO ()
llvm_func2 fn = llvm_func (fn (Arg "a", Arg "b")) 2

-- Create a call from a function and arguments
func :: ((Expr, Expr) -> Expr) -> (Expr, Expr) -> Expr
func fn (a, b) =
  Call (fn (Arg "a", Arg "b"), a, b)


-- ## ENVIRONMENT ## --

-- initialize an environment
env_init :: Type -> String -> Bool -> Env
env_init ty nam dbg = (1, ty, (1, []), nam, [], dbg, Map.empty)

-- get the type from the environment
env_type :: Env -> Type
env_type (_,ty,_,_,_,_,_) = ty

-- get the function name from the environment
env_func :: Env -> String
env_func (_,_,_,name,_,_,_) = name

-- retrieve the debug flag
env_dbg :: Env -> Bool
env_dbg (_,_,_,_,_,dbg,_) = dbg

-- get/put the bindings from the environment
env_get_vars :: Env -> [Bind]
env_get_vars (_,_,_,_,vars,_,_) = vars
env_put_vars :: Env -> Bind -> Env
env_put_vars (a,b,c,d,vars,e,f) bind = (a,b,c,d,bind:vars,e,f)

-- get/put the cse map on the environment
env_get_cse :: Env -> CSE
env_get_cse (_,_,_,_,_,_,cse) = cse
env_put_cse :: Env -> CSE -> Env
env_put_cse (a,b,c,d,e,f,_) env = (a,b,c,d,e,f,env)

-- binding a variable to the environment
env_bind :: Env -> Bind -> Env
env_bind env bind = env_put_vars env bind

-- lookup a variable in the environment
env_lookup :: Env -> String -> String
env_lookup env id =
  let
    find xs =
      case xs of
        (id',reg):ys -> if id == id' then reg else find ys
        [] -> ""
  in
    find (env_get_vars env)

-- try to find a register in the cse map
cse_find :: Env -> Expr -> Maybe String
cse_find env expr = Map.lookup expr (env_get_cse env)

-- add a register to the cse map
cse_add :: Env -> Expr -> String -> Env
cse_add env expr reg = env_put_cse env (Map.insert expr reg (env_get_cse env))


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
        res = Call1 (op (Arg "a"), tmp)
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


-- ## OPTIMIZED PRIMITIVES ## --

-- create an optimized and expression
mk_and :: Expr -> Expr -> Expr
mk_and x Ones = x
mk_and Ones y = y
mk_and x Zero = Zero
mk_and Zero y = Zero
mk_and x y    = if x == y then x else And (x, y)

-- create an optimized or expression
mk_or :: Expr -> Expr -> Expr
mk_or x Ones = Ones
mk_or Ones y = Ones
mk_or x Zero = x
mk_or Zero y = y
mk_or x y    = if x == y then x else Or (x, y)

-- compare for equality that works on not-a-number
mk_cmp (a, b)
  | a == val_nan  = FCmpUNE (b, b)
  | b == val_nan  = FCmpUNE (a, a)
  | otherwise     = FCmpOEQ (a, b)


-- ## HELPERS ## --

-- create a left or right value for with_dummies
left val = (Just val, Nothing)
right val = (Nothing, Just val)

-- create a conditional using logic operations
ite :: Expr -> Expr -> Expr -> Expr
ite b Zero y = And (Not(b), y)
ite b x Zero = And (b, x)
ite Ones x y = x
ite Zero x y = y
ite b x (CopySign (Zero, v)) = 
  if x == v
    then CopySign(And (b, x), x)
    else Or (And (b, x), And (Not b, CopySign (Zero, v)))
ite b (CopySign (Zero, v)) y = 
  if y == v
    then CopySign(And (Not(b), y), y)
    else Or (And (b, CopySign (Zero, v)), And (Not b, y))
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
  And (e, Int (dec "0xFF800000", dec "0xFFF0000000000000") )

-- extract the significand component
get_sig :: Expr -> Expr
get_sig e =
  Or (And (e, Int (dec "0x007FFFFF", dec "0x000FFFFFFFFFFFFF") ), val_one)

-- compute the sign explicitly for mul/div
do_sign :: (FP2 -> FP1) -> FP2 -> FP1
do_sign op (a, b) =
  withBlind
    (\_ -> val_true)
    (\(u,v) -> (Abs(u), Abs(v)))
    (\_ r -> CopySign(r, Xor (a, b)))
    op
    (a, b)
do_sign2 :: (FP2 -> FP1) -> FP2 -> FP1
do_sign2 op (a, b) =
  withBlind
    (\_ -> val_true)
    (\(u,v) -> (u, v))
    (\_ r -> CopySign(r, Xor (a, b)))
    op
    (a, b)

-- handle extreme numbers by shifting them(only division)
do_extreme2 :: (FP2 -> FP1) -> FP2 -> FP1
do_extreme2 op (a, b) =
  let
    isbig  = And (FCmpOGT (Abs a, val_four), FCmpOLT (Abs b, val_one))
    scale = ite isbig val_four val_one
  in
    withBlind
      (\_     -> val_true)
      (\(u,v) -> (u, FMul (v, scale)))
      (\_ r   -> FMul (r, scale))
      op
      (a, b)

do_extreme :: (FP2 -> FP1) -> FP2 -> FP1
do_extreme op (a, b) =
  let 
    cond = And (FCmpOGT (Abs a, val_forth), FCmpOGT (Abs b, val_forth))
    scale = ite cond (Float ("0.03125", "0.03125")) val_one
  in
  withBlind
      (\_     -> val_true)
      (\(u,v) -> (FMul(u, scale), FMul (v, scale)))
      (\_ r   -> r)
      op
      (a, b)

-- ## STRATEGIES ## --

-- underflow with one input
with_underflow :: FP1 -> (FP1 -> FP1) -> FP1 -> FP1
with_underflow lim =
  withBlind
    (\v -> FCmpOLT(Abs(v), lim))
    (\v -> val_zero)
    (\v r -> CopySign(r, v))

-- underflow only on the first input
with_underflow1 :: FP1 -> Bool -> (FP2 -> FP1) -> FP2 -> FP1
with_underflow1 lim sgn =
  withBlind
    (\(v,_) -> FCmpOLT(Abs(v), lim))
    (\(v, w) -> (if sgn then CopySign(val_zero, v) else val_zero, w))
    (\_ r -> r)

-- underflow only on the second input
with_underflow2 :: FP1 -> Bool -> (FP2 -> FP1) -> FP2 -> FP1
with_underflow2 lim sgn =
  withBlind
    (\(_,v) -> FCmpOLT(Abs(v), lim))
    (\(w,v) -> (w, if sgn then CopySign(val_zero, v) else val_zero))
    (\_ r -> r)

-- overflow only on the first input
with_overflow1 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_overflow1 lim =
  withBlind
    (\(v,_) -> FCmpOGT(Abs(v), lim))
    (\(v, w) -> (val_inf, w))
    (\v r -> r)

-- overflow only on the second input
with_overflow2 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_overflow2 lim =
  withBlind
    (\(_,v) -> FCmpOGT(Abs(v), lim))
    (\(w,v) -> (w, val_inf))
    (\_ r -> r)

-- perform dummy computation for a single value
with_dummy :: FP1 -> FP1 -> FP1 -> (FP1 -> FP1) -> FP1 -> FP1
with_dummy badIn badOut safeIn =
  withBlind
    (\v   -> mk_cmp (v, badIn))
    (\v   -> safeIn)
    (\_ _ -> badOut)

-- perform with dummy using a list of unsafe inputs
with_dummies :: [(Maybe Expr, Maybe Expr)] -> FP1 -> FP1 -> (FP2 -> FP1) -> FP2 -> FP1
with_dummies unsafe ans safe op (a, b) =
  let
    g x val = case x of
      Just expr -> mk_cmp(expr, Abs val)
      Nothing   -> val_true
    f xs (x,y) =
      case xs of
        (a,b):ys -> mk_or (mk_and (g a x) (g b y)) (f ys (x,y))
        []       -> val_false
  in
    withBlind
      (\(x,y) -> f unsafe (x, y))
      (\(x,y) -> (safe, safe))
      (\_ _   -> ans)
      op
      (a, b)


-- ## DIVISION STRATEGIES ## --

-- perform a division that is safe for all special (non suborn) values
safediv =
  let
    nans = [
      (Just val_nan,  Nothing      ),
      (Nothing,       Just val_nan ),
      (Just val_inf,  Just val_inf ),
      (Just val_zero, Just val_zero)]
    infs = [
      (Just val_inf,  Nothing       ),
      (Nothing     ,  Just val_zero )]
    zeros = [
      (Just val_zero, Nothing       ),
      (Nothing      , Just val_inf )]
  in
    with_dummies nans val_nan val_dummy @@
    with_dummies infs val_inf val_dummy @@
    with_dummies zeros val_zero val_dummy @@
    div_exp @@
    div_noop @@
    with_dummies [left val_zero] val_zero val_dummy @@
    with_dummies [left val_inf] val_inf val_dummy @@
    FDivSig

-- divide only by the exponent component of the inputs
div_exp :: (FP2 -> FP1) -> FP2 -> FP1
div_exp =
  withBlind
    (\_ -> val_true)
    (\(w,v) -> (FDivExp(w, get_exp v), get_sig v))
    (\v r -> r)

-- prevent division by one using a dummy
div_noop op (a, b) =
  withBlind
    (\(u,v) -> FCmpOEQ(Abs(v), val_one))
    (\_ -> (val_dummy, val_dummy))
    (\_ _ -> a)
    op
    (a, b)


-- ## SQRT STRATEGIES ## --

-- handle square root of negative numbers
neg_sqrt :: (FP1 -> FP1) -> FP1 -> FP1
neg_sqrt =
  withBlind
    (\v   -> FCmpOLT (v, val_zero))
    (\v   -> val_dummy)
    (\_ _ -> val_nan)

-- handle square root of zero (must preserve sign)
zero_sqrt :: (FP1 -> FP1) -> FP1 -> FP1
zero_sqrt =
  withBlind
    (\v   -> FCmpOEQ (v, val_zero))
    (\v   -> val_dummy)
    (\v _ -> v)

-- blind the square root on powers-of-four
blind_sqrt :: (FP1 -> FP1) -> FP1 -> FP1
blind_sqrt =
  withBlind
    (\v   -> FCmpOEQ (And (v, val_pow4), val_oddexp))
    (\v   -> Or (v, val_blind))
    (\_ r -> And (r, val_unblind))
  

-- ## TRIAL STRATEGIES ## --

-- general trial strategy, needs safety function, limit, and safe input
trial :: (Expr -> Expr -> Expr) -> Expr -> (Expr, Expr) -> Bool -> (FP2 -> FP1) -> FP2 -> FP1
trial fn lim safe zero =
  withBlind
    (\(u,v)   -> And (if zero then FCmpOGT (Abs (fn u v), val_zero) else val_true, FCmpOLT (Abs (fn u v), lim)))
    (\(u,v)   -> safe)
    (\(u,v) r -> CopySign(r, fn u v))

-- trial addition
tryadd :: (FP2 -> FP1) -> FP2 -> FP1
tryadd =
  trial
    (\v w -> FAdd (FMul (v, addoff), FMul (w, addoff)))
    addcmp
    (val_zero, val_zero)
    True

-- trial subtraction
trysub :: (FP2 -> FP1) -> FP2 -> FP1
trysub =
  trial
    (\v w -> FSub (FMul (v, addoff), FMul (w, addoff)))
    addcmp
    (val_zero, val_zero)
    True

-- trial multiplication
trymul :: (FP2 -> FP1) -> FP2 -> FP1
trymul =
  trial
    (\v w -> FMul (FMul (v, muloff), w))
    mulcmp
    (val_zero, val_zero)
    False

-- trial division
trydiv :: (FP2 -> FP1) -> FP2 -> FP1
trydiv op (a, b) =
  trial
    (\v w -> safediv (FMul(FMul (v, divoff), divoff2), w))
    divoff2
    (val_zero, val_one)
    False
    op
    (a, b)


-- ## CONSTANTS ## --

-- convert hex string to decimal string
dec :: String -> String
dec str = show ((read str)::Int)

-- values
val_true = Ones
val_false = Zero
val_zero = Zero
val_one = One
val_dummy = Float ( "1.5", "1.5" )
val_half = Float ( "0.5", "0.5" )
val_forth = Float ( "0.25", "0.25" )
val_two = Float ( "2.0", "2.0" )
val_four = Float ( "4.0", "4.0" )
val_nan = Int ( dec "0x7FC00000", dec "0x7FF8000000000000")
val_inf = Int ( dec "0x7F800000", dec "0x7FF0000000000000")
val_blind = Int ( "1", "1" )
val_unblind = Int ( dec "0xFFFFFFFE", dec "0xFFFFFFFFFFFFFFFE" )
val_oddexp = Int ( dec "0x00800000", dec " 0x0010000000000000" )
val_pow4 = Int ( dec "0x00FFFFFF", dec "0x001FFFFFFFFFFFFF" )

-- constants
addmin  = Float ( "9.86076131526264760e-32", "2.00416836000897278e-292" )
mulmin  = Float ( "1.08420217248550443e-19", "1.49166814624004135e-154" )
divmin  = Float ( "1.08420217248550443e-19", "1.49166814624004135e-154" )
divmax  = Float ( "4.61168601842738790e+18", "3.35195198248564927e+153" )
fltmin  = Float ( "1.17549435082228751e-38", "2.22507385850720138e-308" )

addoff = Float ( "1.67772160000000000e+07", "9.007199254740992e+15" )
addcmp = Float ( "1.97215226305252951e-31", "2.004168360008973e-292" )

muloff = Float ( "8.50705917302346159e+37", "4.49423283715578976e+307" )
mulcmp = Float ( "1.0", "1.0" )

divoff = Float ( "8.50705917302346159e+37", "4.49423283715578976e+307" )
divoff2 = Float ( "8.0", "8.0" )
divcmp = Float ( "1.0", "1.0" )
--divoff = Float ( "1.0633823966279327e+37", "1.0633823966279327e+37" )
--divcmp = Float ( "0.25", "0.25" )


-- ## RESTRICT ## --

-- addition
restrict_add :: FP2 -> FP1
restrict_add =
  with_underflow1 addmin True @@
  with_underflow2 addmin True @@
  FAdd

-- subtraction
restrict_sub :: FP2 -> FP1
restrict_sub =
  with_underflow1 addmin True @@
  with_underflow2 addmin True @@
  FSub

-- multiplication
restrict_mul :: FP2 -> FP1
restrict_mul =
  --do_sign @@
  with_underflow1 mulmin True @@
  with_underflow2 mulmin True @@
  FMul

-- division
restrict_div :: FP2 -> FP1
restrict_div =
  do_sign2 @@
  with_underflow1 divmin True @@
  with_underflow2 divmin True @@
  with_overflow1 divmax @@
  with_overflow2 divmax @@
  safediv

-- sqrt
restrict_sqrt :: FP1 -> FP1
restrict_sqrt =
  with_underflow fltmin @@
  with_dummy val_nan  val_nan  val_dummy @@
  with_dummy val_inf  val_inf  val_dummy @@
  neg_sqrt @@
  zero_sqrt @@
  blind_sqrt @@
  FSqrt


-- ## FULL ## --

-- addition
full_add :: FP2 -> FP1
full_add =
  with_underflow1 fltmin True @@
  with_underflow2 fltmin True @@
  tryadd @@
  FAdd

-- subtraction
full_sub :: FP2 -> FP1
full_sub =
  with_underflow1 fltmin True @@
  with_underflow2 fltmin True @@
  trysub @@
  FSub

-- multiplication
full_mul :: FP2 -> FP1
full_mul =
  with_underflow1 fltmin True @@
  with_underflow2 fltmin True @@
  trymul @@
  FMul

-- division
full_div :: FP2 -> FP1
full_div =
  do_sign2 @@
  with_underflow1 fltmin True @@
  with_underflow2 fltmin True @@
  do_extreme @@
  do_extreme2 @@
  trydiv @@
  safediv

-- sqrt
full_sqrt :: FP1 -> FP1
full_sqrt = restrict_sqrt


-- ## FAST ## --

-- addition
fast_add :: FP2 -> FP1
fast_add =
  --with_underflow1 fastmin True @@
  --with_underflow2 fastmin True @@
  FAdd

-- subtraction
fast_sub :: FP2 -> FP1
fast_sub =
  --with_underflow1 fastmin True @@
  --with_underflow2 fastmin True @@
  FSub

-- multiplication
fast_mul :: FP2 -> FP1
fast_mul =
  --do_sign @@
  --with_underflow1 fastmin True @@
  --with_underflow2 fastmin True @@
  FMul

-- division
fast_div :: FP2 -> FP1
fast_div =
  --do_sign2 @@
  --with_underflow1 divmin True @@
  --with_underflow2 divmin True @@
  --with_overflow1 divmax @@
  --with_overflow2 divmax @@
  safediv

-- sqrt
fast_sqrt :: FP1 -> FP1
fast_sqrt =
  --with_underflow fltmin @@
  with_dummy val_nan  val_nan  val_dummy @@
  with_dummy val_inf  val_inf  val_dummy @@
  neg_sqrt @@
  zero_sqrt @@
  blind_sqrt @@
  FSqrt


-- get a name
name :: Env -> Expr -> (Env, String)
name (i, t, (name, fns), n, vars, dbg, cse) expr =
  let env' = (i, t, (name+1, (name, expr):fns), n, vars, dbg, cse) in
    (env', show name)

-- allocate a register from the environment
alloc :: Env -> (Env, String)
alloc (i, t, q, n, vars, dbg, cse) = ((i+1, t, q, n, vars, dbg, cse), "%"++(show i))

-- allocate an array of registers from the environment
allocs :: Env -> Int -> (Env, [String])
allocs e n =
  if n == 0
    then (e, [])
    else let ((i,t,q,f,vars,dbg,cse),ns) = allocs e (n-1) in
      ((i+1,t,q,f,vars,dbg,cse),ns++["%"++(show i)])


-- create a floating point value string
floats :: Env -> String -> String
floats env val =
  let
    vec val cnt = "< " ++ (intercalate " , " (replicate cnt val)) ++ " >"
  in
    case env_type env of
      Float1 -> val
      Float2 -> vec ("float " ++ val) 2
      Float4 -> vec ("float " ++ val) 4
      Float8 -> vec ("float " ++ val) 8
      Float16 -> vec ("float " ++ val) 16
      Double1 -> val
      Double2 -> vec ("double " ++ val) 2
      Double4 -> vec ("double " ++ val) 4
      Double8 -> vec ("double " ++ val) 8

-- create an integer value string
ints :: Env -> String -> String
ints env val =
  let
    vec val cnt = "< " ++ (intercalate " , " (replicate cnt val)) ++ " >"
  in
    case env_type env of
      Float1 -> val
      Float2 -> vec ("i32 " ++ val) 2
      Float4 -> vec ("i32 " ++ val) 4
      Float8 -> vec ("i32 " ++ val) 8
      Float16 -> vec ("i32 " ++ val) 16
      Double1 -> val
      Double2 -> vec ("i64 " ++ val) 2
      Double4 -> vec ("i64 " ++ val) 4
      Double8 -> vec ("i64 " ++ val) 8


-- create an integer values of all ones
ones :: Env -> String
ones e = ints e "-1"

-- create an integer values of all zeros
zeros :: Env -> String
zeros e = ints e "0"


gen_unnamed :: [Func] -> Int -> Type -> Int -> String -> Bool -> IO ()
gen_unnamed [] _ _ _ _ _ = return ()
gen_unnamed ((nam, expr):fns) nargs t idx fn dbg =
  let
    ty = type2flt t
    argl = intercalate ", " $ take nargs (map (\x -> ty ++ " %" ++ x) ["a","b","c","d"])
  in
    do putStr $ "define weak " ++ ty ++ " @"++fn++"_" ++ (show nam) ++ "(" ++ argl ++ ") #1 {\n"
       (r,(_,_,(idx',fns'),_,_,_,_)) <- llvm_expr (expr, (1, t, (idx, fns), fn, [], dbg, Map.empty))
       putStr $ "ret " ++ ty ++ " " ++ r ++ "\n}\n"
       gen_unnamed fns' nargs t idx' fn dbg

llvm_expr :: (Expr, Env) -> IO (String, Env)
llvm_expr (expr, env) =
  case cse_find env expr of
    Just reg ->
      return (reg, env);
      --do (reg, env) <- gen_expr (expr, env)
         --return (reg, cse_add env expr reg)
    Nothing ->
      do (reg, env) <- gen_expr (expr, env)
         return (reg, cse_add env expr reg)
{-
      case expr of
        Arg s -> return ("%" ++ s, env)
        Int val -> gen_int (ints env (env2sel env val), env)
        Float val -> return (floats env (env2sel env val), env)
        Zero -> return (floats env "0.0", env)
        One -> return (floats env "1.0", env)
        Ones -> gen_int (ints env "-1", env)
        Not a -> gen_not (a, env)
        Abs a -> gen_call1("llvm.fabs." ++ (env2vec env), a, env);
        Or (a, b) -> gen_iop2 ("or", a, b, env)
        And (a, b) -> gen_iop2 ("and", a, b, env)
        Xor (a, b) -> gen_iop2 ("xor", a, b, env)
        FSqrt a -> gen_call1 ( if env_dbg env then "dbg_fsqrt_" ++ (env2vec env) else "llvm.sqrt." ++ (env2vec env), a, env)
        FAdd (a, b) -> if env_dbg env then gen_call2 ("dbg_fadd_" ++ (env2vec env), a, b, env) else gen_fop2 ("fadd", a, b, env)
        FSub (a, b) -> if env_dbg env then gen_call2 ("dbg_fsub_" ++ (env2vec env), a, b, env) else gen_fop2 ("fsub", a, b, env)
        FMul (a, b) -> if env_dbg env then gen_call2 ("dbg_fmul_" ++ (env2vec env), a, b, env) else gen_fop2 ("fmul", a, b, env)
        FDivSig (a, b) -> if env_dbg env then gen_call2 ("dbg_fdiv_sig_" ++ (env2vec env), a, b, env) else gen_fop2 ("fdiv", a, b, env)
        FDivExp (a, b) -> if env_dbg env then gen_call2 ("dbg_fdiv_exp_" ++ (env2vec env), a, b, env) else gen_fop2 ("fdiv", a, b, env)
        FCmpOEQ (a, b) -> gen_fcmp ("fcmp oeq", a, b, env)
        FCmpOLT (a, b) -> gen_fcmp ("fcmp olt", a, b, env)
        FCmpOGT (a, b) -> gen_fcmp ("fcmp ogt", a, b, env)
        FCmpUNE (a, b) -> gen_fcmp ("fcmp une", a, b, env)
        CopySign (a, b) -> gen_call2 ("llvm.copysign." ++ (env2vec env), a, b, env)
        Call (fn, a, b) -> gen_call (fn, a, b, env)
        Let (id, val) -> llvm_let id val env
        Var id -> llvm_var id env
        Seq (a, b) -> llvm_seq a b env
-}

-- generate code for an arbitrary expression
gen_expr :: (Expr, Env) -> IO (String, Env)
gen_expr (Arg s, env) = return ("%" ++ s, env)
gen_expr (Int val, env) = gen_int (ints env (env2sel env val), env)
gen_expr (Float val, env) = return (floats env (env2sel env val), env)
gen_expr (Zero, env) = return (floats env "0.0", env)
gen_expr (One, env) = return (floats env "1.0", env)
gen_expr (Ones, env) = gen_int (ints env "-1", env)
gen_expr (Not a, env) = gen_not (a, env)
gen_expr (Abs a, env) = gen_call1("llvm.fabs." ++ (env2vec env), a, env);
gen_expr (Or (a, b), env) = gen_iop2 ("or", a, b, env)
gen_expr (And (a, b), env) = gen_iop2 ("and", a, b, env)
gen_expr (Xor (a, b), env) = gen_iop2 ("xor", a, b, env)
gen_expr (FSqrt a, env) = gen_call1 ( if env_dbg env then "dbg_fsqrt_" ++ (env2vec env) else "llvm.sqrt." ++ (env2vec env), a, env)
gen_expr (FAdd (a, b), env) = if env_dbg env then gen_call2 ("dbg_fadd_" ++ (env2vec env), a, b, env) else gen_fop2 ("fadd", a, b, env)
gen_expr (FSub (a, b), env) = if env_dbg env then gen_call2 ("dbg_fsub_" ++ (env2vec env), a, b, env) else gen_fop2 ("fsub", a, b, env)
gen_expr (FMul (a, b), env) = if env_dbg env then gen_call2 ("dbg_fmul_" ++ (env2vec env), a, b, env) else gen_fop2 ("fmul", a, b, env)
gen_expr (FDivSig (a, b), env) = if env_dbg env then gen_call2 ("dbg_fdiv_sig_" ++ (env2vec env), a, b, env) else gen_fop2 ("fdiv", a, b, env)
gen_expr (FDivExp (a, b), env) = if env_dbg env then gen_call2 ("dbg_fdiv_exp_" ++ (env2vec env), a, b, env) else gen_fop2 ("fdiv", a, b, env)
gen_expr (ICmp (a, b), env) = gen_icmp ("icmp eq", a, b, env)
gen_expr (FCmpOEQ (a, b), env) = gen_fcmp ("fcmp oeq", a, b, env)
gen_expr (FCmpOLT (a, b), env) = gen_fcmp ("fcmp olt", a, b, env)
gen_expr (FCmpULT (a, b), env) = gen_fcmp ("fcmp ult", a, b, env)
gen_expr (FCmpOGT (a, b), env) = gen_fcmp ("fcmp ogt", a, b, env)
gen_expr (FCmpUNE (a, b), env) = gen_fcmp ("fcmp une", a, b, env)
gen_expr (CopySign (a, b), env) = gen_call2 ("llvm.copysign." ++ (env2vec env), a, b, env)
gen_expr (Call1 (fn, a),  env) = llvm_call1 (fn, a, env)
gen_expr (Call (fn, a, b),  env) = llvm_call2 (fn, a, b, env)
gen_expr (Seq (a, b), env) = llvm_seq a b env

-- llvm code for let expressions
llvm_let :: String -> Expr -> Env -> IO (String, Env)
llvm_let id val env =
    do (x, env) <- llvm_expr (val, env)
       let env' = env_bind env (id, x) in
         return (x, env')

-- llvm code for variables
llvm_var :: String -> Env -> IO (String, Env)
llvm_var id env =
  return (env_lookup env id, env)

-- llvm code for sequences instructions
llvm_seq :: Expr -> Expr -> Env -> IO (String, Env)
llvm_seq a b env =
  do (x, env) <- llvm_expr (a, env)
     (y, env) <- llvm_expr (b, env)
     return (y, env)

-- llvm code for a 1-argument call
llvm_call1 :: (Expr, Expr, Env) -> IO (String, Env)
llvm_call1 (fn, a, env) =
  do (ra, env) <- llvm_expr (a, env)
     let (env',r) = alloc env in
       let (env'',func) = name env' fn in
         let flt = env2flt env'' in 
           do putStr $ r++" = call "++flt++" @"++(env_func env'')++"_"++func++"("++flt++" "++ra++")\n"
              return (r, env'')

-- llvm code for a 2-argument call
llvm_call2 :: (Expr, Expr, Expr, Env) -> IO (String, Env)
llvm_call2 (fn, a, b, env) =
  do (ra, env) <- llvm_expr (a, env)
     (rb, env) <- llvm_expr (b, env)
     let (env',r) = alloc env in
       let (env'',func) = name env' fn in
         let flt = env2flt env'' in 
           do putStr $ r++" = call "++flt++" @"++(env_func env'')++"_"++func++"("++flt++" "++ra++", "++flt++" "++rb++")\n"
              return (r, env'')

-- generate an integer constant
gen_int :: (String, Env) -> IO (String, Env)
gen_int (int, env) =
  let (env',r) = alloc env in
    do putStr $ r++" = bitcast "++(env2int env')++" "++int++" to "++(env2flt env')++"\n"
       return (r, env')

-- generate a bitwise not
gen_not :: (Expr, Env) -> IO (String, Env)
gen_not (a, env) =
  do (ra, env) <- llvm_expr (a, env)
     let (env',[ra',rt,ro]) = allocs env 3 in
       do putStr $ ra'++" = bitcast "++(env2flt env')++" "++ra++" to "++(env2int env')++"\n"
          putStr $ rt++" = xor "++(env2int env')++" "++ra'++", "++(ones env')++"\n"
          putStr $ ro++" = bitcast "++(env2int env')++" "++rt++" to "++(env2flt env')++"\n"
          return (ro, env')

-- generate code for a two-operand integer operation
gen_iop2 :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_iop2 (op, a, b, env) =
  do (ra, env) <- llvm_expr (a, env)
     (rb, env) <- llvm_expr (b, env)
     let (env',[ra',rb',rt,ro]) = allocs env 4 in
       do putStr $ ra'++" = bitcast "++(env2flt env)++" "++ra++" to "++(env2int env)++"\n"
          putStr $ rb'++" = bitcast "++(env2flt env)++" "++rb++" to "++(env2int env)++"\n"
          putStr $ rt++" = "++op++" "++(env2int env)++" "++ra'++", "++rb'++"\n"
          putStr $ ro++" = bitcast "++(env2int env)++" "++rt++" to "++(env2flt env)++"\n"
          return (ro, env')

-- generate code for a two-operand floating-point operation
gen_fop2 :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_fop2 (op, a, b, env) =
  do (ra, env) <- llvm_expr (a, env)
     (rb, env) <- llvm_expr (b, env)
     let (env',ro) = alloc env in
       do putStr $ ro++" = "++op++" "++(env2flt env)++" "++ra++", "++rb++"\n"
          return (ro, env')

-- generate code for an integer comparison
gen_icmp :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_icmp (cmp, a, b, env) =
  do (ra, env) <- llvm_expr (a, env)
     (rb, env) <- llvm_expr (b, env)
     let (env', [ra',rb',rt,rs,ro]) = allocs env 5 in
       do putStr $ ra'++" = bitcast "++(env2flt env)++" "++ra++" to "++(env2int env)++"\n"
          putStr $ rb'++" = bitcast "++(env2flt env)++" "++rb++" to "++(env2int env)++"\n"
          putStr $ rt++" = "++cmp++" "++(env2int env')++" "++ra'++", "++rb'++"\n"
          putStr $ rs++" = select "++(env2bool env')++" "++rt++", "++(env2int env')++" "++(ones env')++", "++(env2int env')++" "++(zeros env')++"\n"
          putStr $ ro++" = bitcast "++(env2int env')++" "++rs++" to "++(env2flt env')++"\n"
          return (ro, env')

-- generate code for a floating-point comparison
gen_fcmp :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_fcmp (cmp, a, b, env) =
  do (ra, env) <- llvm_expr (a, env)
     (rb, env) <- llvm_expr (b, env)
     let (env', [rt,rs,ro]) = allocs env 3 in
       do putStr $ rt++" = "++cmp++" "++(env2flt env')++" "++ra++", "++rb++"\n"
          putStr $ rs++" = select "++(env2bool env')++" "++rt++", "++(env2int env')++" "++(ones env')++", "++(env2int env')++" "++(zeros env')++"\n"
          putStr $ ro++" = bitcast "++(env2int env')++" "++rs++" to "++(env2flt env')++"\n"
          return (ro, env')

-- create a function call with one argument
gen_call1 :: (String, Expr, Env) -> IO (String, Env)
gen_call1 (fn, a, env) =
  do (ra, env) <- llvm_expr (a, env)
     let (env', r) = alloc env in
       do putStr $ r++" = call "++(env2flt env')++" @"++fn++"("++(env2flt env')++" "++ra++")\n"
          return (r, env')

-- create a function call with one argument
gen_call2 :: (String, Expr, Expr, Env) -> IO (String, Env)
gen_call2 (fn, a, b, env) =
  do (ra, env) <- llvm_expr (a, env)
     (rb, env) <- llvm_expr (b, env)
     let (env', r) = alloc env in
       let ty = env2flt env' in
         do putStr $ r++" = call "++ty++" @"++fn++"("++ty++" "++ra++", "++ty++" "++rb++")\n"
            return (r, env')


-- ## TYPE HELPERS ## --

-- select a string using the type
type2sel :: Type -> (String, String) -> String
type2sel Float1 p = fst p
type2sel Float2 p = fst p
type2sel Float4 p = fst p
type2sel Float8 p = fst p
type2sel Float16 p = fst p
type2sel Double1 p = snd p
type2sel Double2 p = snd p
type2sel Double4 p = snd p
type2sel Double8 p = snd p

-- select a string using the environment
env2sel :: Env -> (String, String) -> String
env2sel env p = type2sel (env_type env) p

-- convert a type to the floating-point type string
type2flt :: Type -> String
type2flt Float1 = "float"
type2flt Float2 = "< 2 x float >"
type2flt Float4 = "< 4 x float >"
type2flt Float8 = "< 8 x float >"
type2flt Float16 = "< 16 x float >"
type2flt Double1 = "double"
type2flt Double2 = "< 2 x double >"
type2flt Double4 = "< 4 x double >"
type2flt Double8 = "< 8 x double >"

-- generate float type string from the environment
env2flt :: Env -> String
env2flt env = type2flt (env_type env)

-- convert a type to the integer type string
type2int :: Type -> String
type2int Float1 = "i32"
type2int Float2 = "< 2 x i32 >"
type2int Float4 = "< 4 x i32 >"
type2int Float8 = "< 8 x i32 >"
type2int Float16 = "< 16 x i32 >"
type2int Double1 = "i64"
type2int Double2 = "< 2 x i64 >"
type2int Double4 = "< 4 x i64 >"
type2int Double8 = "< 8 x i64 >"

-- generate integer type string from the environment
env2int :: Env -> String
env2int env = type2int (env_type env)

-- convert a type to the boolean type string
type2bool :: Type -> String
type2bool Float1 = "i1"
type2bool Float2 = "< 2 x i1 >"
type2bool Float4 = "< 4 x i1 >"
type2bool Float8 = "< 8 x i1 >"
type2bool Float16 = "< 16 x i1 >"
type2bool Double1 = "i1"
type2bool Double2 = "< 2 x i1 >"
type2bool Double4 = "< 4 x i1 >"
type2bool Double8 = "< 8 x i1 >"

-- generate boolean type string from the environment
env2bool :: Env -> String
env2bool env = type2bool (env_type env)

-- convert a type to the vectorized builtin string
type2vec :: Type -> String
type2vec Float1 = "f32"
type2vec Float2 = "v2f32"
type2vec Float4 = "v4f32"
type2vec Float8 = "v8f32"
type2vec Float16 = "v16f32"
type2vec Double1 = "f64"
type2vec Double2 = "v2f64"
type2vec Double4 = "v4f64"
type2vec Double8 = "v8f64"

-- generate vectorized name from the environment
env2vec :: Env -> String
env2vec env = type2vec (env_type env)

-- convert a type to the funcion postfix
type2post :: Type -> String
type2post Float1 = "f32v1"
type2post Float2 = "f32v2"
type2post Float4 = "f32v4"
type2post Float8 = "f32v8"
type2post Float16 = "f32v16"
type2post Double1 = "f64v1"
type2post Double2 = "f64v2"
type2post Double4 = "f64v4"
type2post Double8 = "f64v8"

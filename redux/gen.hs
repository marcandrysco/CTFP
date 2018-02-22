{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}


prelude =
  "declare < 2 x float > @llvm.fabs.v2f32(< 2 x float > %a)\n" ++
  "declare < 4 x float > @llvm.fabs.v4f32(< 4 x float > %a)\n"

main = 
  let t = Float4 in 
  let e = restrict_ctfp_add (Arg "a", Arg "b") in
  --let e = Fadd(Arg "a", Float "1.0") in
  --let e = Or (Arg "a", Arg "b") in
  --let e = ite (FcmpOLT (Arg "a", Arg "b")) (Arg "a") (Arg "b") in
  --let e = ite (FcmpOLT (Arg "a", Arg "b")) (Fadd (Arg "a", Arg "a")) (Fadd (Arg "a", Arg "a")) in
  let (r,(c,_,_)) = tostr (e, ("", 1, t)) in
  let f = env2flt ("",0,t) in
    putStr $ prelude ++ "define weak " ++ f ++ " @func(" ++ f ++ " %a, " ++ f ++ " %b) {\n" ++ c ++ "ret " ++ f ++ " " ++ r ++ "\n}\n"


data Expr
  = Arg     String
  | Int     String
  | Float   String
  | Not     (Expr)
  | Abs     (Expr)
  | Or      (Expr, Expr)
  | And     (Expr, Expr)
  | Fadd    (Expr, Expr)
  | FcmpOLT (Expr, Expr)
  deriving Eq

data Type
  = Float1
  | Float2
  | Float4
  | Double1
  | Double2

type Env = (String, Int, Type)

ite :: Expr -> Expr -> Expr -> Expr
ite b x y = 
  if x == y
    then x
    else Or (And (b, x), And (Not b, y))

ite2 :: Expr -> (Expr,Expr) -> (Expr,Expr) -> (Expr,Expr)
ite2 b (x1,x2) (y1,y2) = (ite b x1 y1, ite b x2 y2)

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

instance WithBlind (Expr, Expr) (Expr -> Expr) where
  withBlind cond blind fix op v =
    let b   = cond v
        tmp = ite2 b (blind v) v
        res = op tmp
        out = ite b (fix res) res
    in out

type FP1   = Expr
type FP2   = (FP1, FP1)
type UnOp  = FP1 -> FP1
type BinOp = FP2 -> FP2

withUnderflow :: FP1 -> (FP1 -> FP1) -> FP1 -> FP1
withUnderflow lim =
  withBlind
    (\v -> FcmpOLT(Abs(v), lim))
    (\v -> Float "0.0")
    (\_ r -> r)

-- variants of the above for underflow on FIRST input
withUnderflow1 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
withUnderflow1 lim =
  withBlind
    (\(v,_) -> FcmpOLT(Abs(v), lim))
    (\(v, w) -> (Float "0.0", w))
    (\r -> r)

-- variants of the above for underflow on SECOND input
withUnderflow2 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
withUnderflow2 lim =
  withBlind
    (\(_,v) -> FcmpOLT(v, lim))
    (\(w,v) -> (w, Float "0.0"))
    (\r -> r)


infixr 8 @@

(@@):: ((a -> b) -> (a -> b)) -> (a -> b) -> (a -> b)
tx @@ f = tx f


-- constants
addmin = "9.8607613152626476e-32"


restrict_ctfp_add :: FP2 -> FP1
restrict_ctfp_add =
  withUnderflow1 (Float addmin) @@
  withUnderflow2 (Float addmin) @@
  Fadd


-- allocate a register from the environment
alloc :: Env -> (Env, String)
alloc (c, i, t) = ((c, i+1, t), "%"++(show i))

-- allocate an array of registers from the environment
allocs :: Env -> Int -> (Env, [String])
allocs e n =
  if n == 0
    then (e, [])
    else let ((c,i,t),ns) = allocs e (n-1) in
      ((c,i+1,t),ns++["%"++(show i)])

-- add code to an environment
addcode :: Env -> String -> Env
addcode (c, i, t) s = (c ++ s, i, t)

-- retrieve code from an environment
getcode :: Env -> String
getcode (c, i, t) = c


-- create an integer values of all zeros
zeros :: Env -> String
zeros (c, i, t) =
  case t of
    Float1 -> "0"
    Float2 -> "< i32 0, i32 0 >"
    Float4 -> "< i32 0, i32 0, i32 0, i32 0 >"
    Double1 -> "0"
    Double2 -> "< i64 0, i64 0 >"

-- create an integer values of all ones
ones :: Env -> String
ones (c, i, t) =
  case t of
    Float1 -> "-1"
    Float2 -> "< i32 -1, i32 -1 >"
    Float4 -> "< i32 -1, i32 -1, i32 -1, i32 -1 >"
    Double1 -> "-1"
    Double2 -> "< i64 -1, i64 -1 >"

floats :: Env -> String -> String
floats (c, i, t) v =
  case t of
    Float1 -> v
    Float2 -> "< float " ++ v ++ ", float " ++ v ++ " >"
    Float4 -> "< float " ++ v ++ ", float " ++ v ++ ", float " ++ v ++ ", float " ++ v ++ " >"
    Double1 -> v
    Double2 -> "< double " ++ v ++ ", double " ++ v ++ " >"

ints :: Env -> String -> String
ints (c, i, t) v =
  case t of
    Float1 -> v
    Float2 -> "< i32 " ++ v ++ ", i32 " ++ v ++ " >"
    Float4 -> "< i32 " ++ v ++ ", i32 " ++ v ++ ", i32 " ++ v ++ ", i32 " ++ v ++ " >"
    Double1 -> v
    Double2 -> "< i64 " ++ v ++ ", i64 " ++ v ++ " >"


-- convert a type to the floating-point type string
type2flt :: Type -> String
type2flt Float1 = "float"
type2flt Float2 = "< 2 x float >"
type2flt Float4 = "< 4 x float >"
type2flt Double1 = "double"
type2flt Double2 = "< 2 x double >"

-- generate float type string from the environment
env2flt :: Env -> String
env2flt (_,_,t) = type2flt t

-- convert a type to the integer type string
type2int :: Type -> String
type2int Float1 = "i32"
type2int Float2 = "< 2 x i32 >"
type2int Float4 = "< 4 x i32 >"
type2int Double1 = "i64"
type2int Double2 = "< 2 x i64 >"

-- generate integer type string from the environment
env2int :: Env -> String
env2int (_,_,t) = type2int t

-- convert a type to the boolean type string
type2bool :: Type -> String
type2bool Float1 = "i1"
type2bool Float2 = "< 2 x i1 >"
type2bool Float4 = "< 4 x i1 >"
type2bool Double1 = "i1"
type2bool Double2 = "< 2 x i1 >"

-- generate boolean type string from the environment
env2bool :: Env -> String
env2bool (_,_,t) = type2bool t

-- convert a type to the vectorized builtin string
type2vec :: Type -> String
type2vec Float1 = "f32"
type2vec Float2 = "v2f32"
type2vec Float4 = "v4f32"
type2vec Double1 = "f64"
type2vec Double2 = "v2f64"

-- generate vectorized name from the environment
env2vec :: Env -> String
env2vec (_,_,t) = type2vec t


-- convert an expression into a string
tostr :: (Expr, Env) -> (String, Env)
tostr (Arg s, e) = ("%"++s, e)
tostr (Int s, e) = (ints e s, e)
tostr (Float s, e) = (floats e s, e)
tostr (Not a, e) = tostr_not(a, e);
tostr (Abs a, e) = tostr_call1("llvm.fabs." ++ (env2vec e), a, e);
tostr (Or (l, r), e) = tostr_iop2("or", l, r, e);
tostr (And (l, r), e) = tostr_iop2("and", l, r, e);
tostr (Fadd (l, r), e) = tostr_fop2("fadd", l, r, e);
tostr (FcmpOLT (a, b), e) = tostr_fcmp("fcmp olt", a, b, e);

tostr_not :: (Expr, Env) -> (String, Env)
tostr_not (a, e) =
  let (an,e2) = tostr (a, e) in
  let (e3,[vn,tn,on]) = allocs e2 3 in
  let vs = vn++" = bitcast "++(env2flt e)++" "++an++" to "++(env2int e)++"\n" in
  let ts = tn++" = xor "++(env2int e)++" "++vn++", "++(ones e)++"\n" in
  let os = on++" = bitcast "++(env2int e)++" "++tn++" to "++(env2flt e)++"\n" in
    (on, addcode e3 (concat [vs,ts,os]))

tostr_iop2 :: (String, Expr, Expr, Env) -> (String, Env)
tostr_iop2 (o, a, b, e) =
  let (at,e1) = tostr (a, e) in
  let (bt,e2) = tostr (b, e1) in
  let (e3,[an,bn,tn,on]) = allocs e2 4 in
  let ls = an++" = bitcast "++(env2flt e)++" "++at++" to "++(env2int e)++"\n" in
  let rs = bn++" = bitcast "++(env2flt e)++" "++bt++" to "++(env2int e)++"\n" in
  let ts = tn++" = "++o++" "++(env2int e)++" "++an++", "++bn++"\n" in
  let os = on++" = bitcast "++(env2int e)++" "++tn++" to "++(env2flt e)++"\n" in
    (on, addcode e3 (concat [ls, rs, ts, os]))

-- create a two-operand floating-point operation
tostr_fop2 :: (String, Expr, Expr, Env) -> (String, Env)
tostr_fop2 (o, a, b, e) =
  let (ra,e1) = tostr (a, e) in
  let (rb,e2) = tostr (b, e1) in
  let (e3,r) = alloc e2 in
  let s = r++" = "++o++" "++(env2flt e)++" "++ra++", "++rb++"\n" in
    (r, addcode e3 s)

-- create a function call with one argument
tostr_call1 :: (String, Expr, Env) -> (String, Env)
tostr_call1 (f, a, e) =
  let (ra,e') = tostr (a, e) in
  let (e'',r) = alloc e' in
  let s = r++" = call "++(env2flt e)++" @"++f++"("++(env2flt e)++" "++ra++")\n" in
    (r, addcode e'' s)

tostr_fcmp :: (String, Expr, Expr, Env) -> (String, Env)
tostr_fcmp (o, a, b, e) =
  let (ra,e1) = tostr (a, e) in
  let (rb,e2) = tostr (b, e1) in
  let (e3,[rt,ri,rf]) = allocs e2 3 in
  let st = rt++" = "++o++" "++(env2flt e)++" "++ra++", "++rb++"\n" in
  let si = ri++" = select "++(env2bool e)++" "++rt++", "++(env2int e)++" "++(ones e)++", "++(env2int e)++" "++(zeros e)++"\n" in
  let sf = rf++" = bitcast "++(env2int e)++" "++ri++" to "++(env2flt e)++"\n" in
    (rf, addcode e3 (concat [st,si,sf]))

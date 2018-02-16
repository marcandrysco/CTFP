{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}


main = 
  let e = restrict_ctfp_add (Arg "a", Arg "b") in
  --let e = ite (Arg "c") (Arg "a") (Arg "b") in
  let c = getcode $ snd $ tostr (e, ("", 1, Float1)) in
    putStr c


data Expr
  = Arg     String
  | Not     (Expr)
  | Or      (Expr, Expr)
  | And     (Expr, Expr)
  | Fadd    (Expr, Expr)
  | FcmpOLT (Expr, Expr)

data Type
  = Float1
  | Float2
  | Double1
  | Double2

type Env = (String, Int, Type)



ite :: Expr -> Expr -> Expr -> Expr
ite b x y = Or (And (b, x), And (Not b, y))

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
    (\v -> FcmpOLT(v, lim))
    (\v -> v)
    (\_ r -> r)

-- variants of the above for underflow on FIRST input
withUnderflow1 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
withUnderflow1 lim =
  withBlind
    (\(v,_) -> FcmpOLT(v, lim))
    (\(v, w) -> (v, w))
    (\r -> r)

-- variants of the above for underflow on SECOND input
withUnderflow2 :: FP1 -> (FP2 -> FP1) -> FP2 -> FP1
withUnderflow2 lim =
  withBlind
    (\(_,v) -> FcmpOLT(v, lim))
    (\(w,v) -> (w, v))
    (\r -> r)


infixr 8 @@

(@@):: ((a -> b) -> (a -> b)) -> (a -> b) -> (a -> b)
tx @@ f = tx f


restrict_ctfp_add :: FP2 -> FP1
restrict_ctfp_add =
  withUnderflow1 (Arg "A") @@
  Fadd
  -- withUnderflow1 9.86e-32
  -- @@ withUnderflow2 9.86e-32
  -- @@ Fadd


-- allocate a register from the environment
alloc :: Env -> (Env, String)
alloc (c, i, t) = ((c, i+1, t), show i)

-- allocate an array of registers from the environment
allocs :: Env -> Int -> (Env, [String])
allocs e n =
  if n == 0
    then (e, [])
    else let ((c,i,t),ns) = allocs e (n-1) in
      ((c,i+1,t),ns++[show i])

-- add code to an environment
addcode :: Env -> String -> Env
addcode (c, i, t) s = (c ++ s, i, t)

-- retrieve code from an environment
getcode :: Env -> String
getcode (c, i, t) = c

-- retrieve the floating point type name
fname :: Env -> String
fname (c, i, t) =
  case t of
    Float1 -> "float"
    Float2 -> "< 2 x float >"
    Double1 -> "double"
    Double2 -> "< 2 x double >"

-- retrieve the integer type name
iname :: Env -> String
iname (c, i, t) =
  case t of
    Float1 -> "i32"
    Float2 -> "< 2 x i32 >"
    Double1 -> "i64"
    Double2 -> "< 2 x i64 >"

-- retrieve the boolean type name
bname :: Env -> String
bname (c, i, t) =
  case t of
    Float1 -> "i1"
    Float2 -> "< 2 x i1 >"
    Double1 -> "i1"
    Double2 -> "< 2 x i1 >"

-- create an integer values of all zeros
zeros :: Env -> String
zeros (c, i, t) =
  case t of
    Float1 -> "0"
    Float2 -> "< i32 0, i32 0 >"
    Double1 -> "0"
    Double2 -> "< i64 0, i64 0 >"

-- create an integer values of all ones
ones :: Env -> String
ones (c, i, t) =
  case t of
    Float1 -> "-1"
    Float2 -> "< i32 -1, i32 -1 >"
    Double1 -> "-1"
    Double2 -> "< i64 -1, i64 -1 >"

-- convert an expression into a string
tostr :: (Expr, Env) -> (String, Env)
tostr (Arg s, e) = (s, e)
tostr (Not a, e) = tostr_not(a, e);
tostr (Or (l, r), e) = tostr_iop2("or", l, r, e);
tostr (And (l, r), e) = tostr_iop2("and", l, r, e);
tostr (Fadd (l, r), e) = tostr_fop2("fadd", l, r, e);
tostr (FcmpOLT (a, b), e) = tostr_fcmp("fcmp olt", a, b, e);

tostr_not :: (Expr, Env) -> (String, Env)
tostr_not (a, e) =
  let (an,e2) = tostr (a, e) in
  let (e3,[vn,tn,on]) = allocs e2 3 in
  let vs = "%"++vn++" = bitcast "++(fname e)++" %"++an++" to "++(iname e)++"\n" in
  let ts = "%"++tn++" = xor "++(iname e)++" %"++vn++", "++(ones e)++"\n" in
  let os = "%"++on++" = bitcast "++(iname e)++" %"++tn++" to "++(fname e)++"\n" in
    (on, addcode e3 (concat [vs,ts,os]))

tostr_iop2 :: (String, Expr, Expr, Env) -> (String, Env)
tostr_iop2 (o, a, b, e) =
  let (at,e1) = tostr (a, e) in
  let (bt,e2) = tostr (b, e1) in
  let (e3,[an,bn,tn,on]) = allocs e2 4 in
  let ls = "%"++an++" = bitcast "++(fname e)++" %"++at++" to "++(iname e)++"\n" in
  let rs = "%"++bn++" = bitcast "++(fname e)++" %"++bt++" to "++(iname e)++"\n" in
  let ts = "%"++tn++" = "++o++" "++(iname e)++" %"++an++", %"++bn++"\n" in
  let os = "%"++on++" = bitcast "++(iname e)++" %"++tn++" to "++(fname e)++"\n" in
    (on, addcode e3 (concat [ls, rs, ts, os]))

tostr_fop2 :: (String, Expr, Expr, Env) -> (String, Env)
tostr_fop2 (o, a, b, e) =
  let (ra,e1) = tostr (a, e) in
  let (rb,e2) = tostr (b, e1) in
  let (e3,r) = alloc e2 in
  let s = "%"++r++" = "++o++" "++(fname e)++" %"++ra++", %"++rb++"\n" in
    (r, addcode e3 s)

tostr_fcmp :: (String, Expr, Expr, Env) -> (String, Env)
tostr_fcmp (o, a, b, e) =
  let (ra,e1) = tostr (a, e) in
  let (rb,e2) = tostr (b, e1) in
  let (e3,[rt,ri,rf]) = allocs e2 3 in
  let st = "%"++rt++" = "++o++" "++(fname e)++" %"++ra++", %"++rb++"\n" in
  let si = "%"++ri++" = select "++(bname e)++" %"++rt++", "++(iname e)++" "++(ones e)++", "++(iname e)++" "++(zeros e)++"\n" in
  let sf = "%"++rf++" = bitcast "++(iname e)++" %"++ri++" to "++(fname e)++"\n" in
    (rf, addcode e3 (concat [st,si,sf]))

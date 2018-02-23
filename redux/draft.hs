module Ctfp where

import Prelude hiding (div)
-- | example of decoration

--------------------------------------------------------------------------------
-- | SUBSECTION: PRIMITIVES
--------------------------------------------------------------------------------

withBump n f x = f (x + n)

incr x = x + 1

blob = withBump 200
    @@ withBump 100
    @@ incr


infixr 8 @@

(@@):: ((a -> b) -> (a -> b)) -> (a -> b) -> (a -> b)
tx @@ f = tx f

ite :: Bool -> a -> a -> a
ite = undefined -- (b & x) | (!b & y)

copySign   = undefined
isPow4     = undefined
divByParts = undefined
getSigExp = undefined

add :: FP2 -> FP1
add (x, y) = x + y

div :: FP2 -> FP1
div (x, y) = undefined

_INF, _NAN, _FLT_MIN :: FP1
_INF = undefined
_NAN = undefined
_FLT_MIN = undefined

raw :: String -> a
raw = undefined

type FP1   = Double
type FP2   = (FP1, FP1)
type UnOp  = FP1 -> FP1
type BinOp = FP2 -> FP2

--------------------------------------------------------------------------------
-- | SUBSECTION: STRATEGIES
--------------------------------------------------------------------------------
-- | STRATEGY #1
-- | 'withBlind' is the CORE strategy (1)
--------------------------------------------------------------------------------
withBlind :: (a -> Bool)    -- ^ test
          -> (a -> a)       -- ^ blinder
          -> (a -> b -> b)  -- ^ fixer
          -> (a -> b)       -- ^ operation
          -> (a -> b)       -- ^ blinded-operation
withBlind cond blind fix op v =
  let b   = cond v
      tmp = ite b (blind v) v
      res = op tmp
      out = ite b (fix v res) res
  in
      out

--------------------------------------------------------------------------------
-- | STRATEGY #2
-- | 'withDummy' is the DERIVED strategy (2)
--------------------------------------------------------------------------------
withDummy :: (a -> Bool)    -- ^ cond bad inputs
          -> b              -- ^ output in case of bad input
          -> a
          -> (a -> b)
          -> (a -> b)
withDummy badIn badOut safeIn op inp =
  withBlind
    badIn
    (\_ -> safeIn)
    (\_ _ -> copySign inp badOut)
    op
    inp

-- | variant of 'withDummy' that uses safeDummy for FIRST input
withDummy1 :: (a1 -> Bool)
           -> a1
           -> ((a1, a2) -> b -> b)
           -> ((a1, a2) -> b)
           -> ((a1, a2) -> b)
withDummy1 badIn1 safeIn1 badOut =
  withBlind
    (\(x1,_)  -> badIn1 x1)
    (\(_ ,x2) -> (safeIn1, x2))
    badOut

-- | variant of 'withDummy' that uses safeDummy for SECOND input
withDummy2 :: (a2 -> Bool)
           -> a2
           -> ((a1, a2) -> b -> b)
           -> ((a1, a2) -> b)
           -> ((a1, a2) -> b)
withDummy2 badIn1 safeIn2 badOut =
  withBlind
    (\(_,x2) -> badIn1 x2)
    (\(x1,_) -> (x1, safeIn2))
    badOut

--------------------------------------------------------------------------------
-- | STRATEGY #3
-- | 'withUnderflow' is the DERIVED strategy (3)
--------------------------------------------------------------------------------
withUnderflow :: FP1 -> (FP1 -> FP1) -> FP1 -> FP1
withUnderflow lim =
  withBlind
    (\v -> abs v < lim)
    (\v -> copySign v 0.0)
    (\_ r -> r)

-- variants of the above for underflow on FIRST input
withUnderflow1 :: FP1 -> (FP2 -> a) -> FP2 -> a
withUnderflow1 lim =
  withBlind
    (\(v,_) -> abs v < lim)
    (\(v, w) -> (copySign v 0.0, w))
    (\_ r -> r)

-- variants of the above for underflow on SECOND input
withUnderflow2 :: FP1 -> (FP2 -> a) -> FP2 -> a
withUnderflow2 lim =
  withBlind
    (\(_,v) -> abs v < lim)
    (\(w,v) -> (w, copySign v 0.0))
    (\_ r -> r)

--------------------------------------------------------------------------------
-- | STRATEGY #4
--  'withTxForm tx f' returns a function that
--  transforms its input using 'tx' BEFORE invoking 'f'
--------------------------------------------------------------------------------
withTxForm :: (a -> c) -> (c -> b) -> a -> b
withTxForm tx f = \a -> f (tx a)

--------------------------------------------------------------------------------
-- | SUBSECTION: CTFP
--------------------------------------------------------------------------------
-- | Now the actual CTFP lib that uses the strategies
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- called 'square' in paper
safeSquare :: FP1 -> FP1
--------------------------------------------------------------------------------
safeSquare
  =  withDummy (== 1.46) 2.13 1.5
  @@ withDummy (==  _INF) _INF  1.5
  @@ square

-- | just machine multiply
square:: FP1 -> FP1
square x = x * x


--------------------------------------------------------------------------------
blindSqrt :: FP1 -> FP1
--------------------------------------------------------------------------------
blindSqrt
  =  withBlind isPow4 (\a -> raw "a | 1") (\t2 -> raw "t2 & ~1")
  @@ sqrt

--------------------------------------------------------------------------------
-- called 'sqrtdummy' in paper
safeSqrt :: FP1 -> FP1
--------------------------------------------------------------------------------
safeSqrt
  =  withDummy (<  0.0)  _NAN 1.5
  @@ withDummy (== _INF) _INF 1.5
  @@ withDummy (== 0.0) 0.0 1.5
  @@ blindSqrt

--------------------------------------------------------------------------------
-- called 'restrict_ctfp_add' in paper
restrict_ctfp_add :: FP2 -> FP1
--------------------------------------------------------------------------------
restrict_ctfp_add
  =  withUnderflow1 9.86e-32
  @@ withUnderflow2 9.86e-32
  @@ add

--------------------------------------------------------------------------------
full_ctfp_add :: FP2 -> FP1
--------------------------------------------------------------------------------
full_ctfp_add
  =  withDummy trialAdd 0.0 (0.0, 0.0)
  @@ withUnderflow1 _FLT_MIN
  @@ withUnderflow2 _FLT_MIN
  @@ add

trialAdd (a, b) =
  let c = 16777216.0
      t = abs ((a * c) + (b * c))
  in
      (t == 0.0) || (t >= (c * _FLT_MIN))

--------------------------------------------------------------------------------
divdummy :: FP2 -> FP1
--------------------------------------------------------------------------------
divdummy
  =  withDummy isDivNan  _NAN (1.5, 1.5)
  @@ withDummy isDivInf  _INF (1.5, 1.5)
  @@ withDummy isDivZero 0.0 (1.5, 1.5)
  @@ divByParts

isDivNan (a, b)
  =  (a == _NAN)
  || (b == _NAN)
  || ((a == _INF) && (b == _INF))
  || ((a == 0.0) && (b == 0.0))

isDivInf (a, b)
  = (a == _INF) || (b == 0.0)

isDivZero (a, b)
  = (a == 0.0) || (b == _INF)

--------------------------------------------------------------------------------
divbyparts :: FP2 -> FP1
--------------------------------------------------------------------------------
divbyparts
  =  withDummy2 (== 1.0)  1.5 (\(n,_) _ -> n)
  @@ withDummy1 (== 0.0)  1.5 (\_ _     -> 0.0)
  @@ withDummy1 (== _INF) 1.5 (\_ _     -> _INF)
  @@ withTxForm splitDiv
  @@ div

splitDiv (n, d) =
  let (s, e) = getSigExp d
  in (div (n, e), s)

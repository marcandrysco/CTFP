{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.LLVC.Smt where 

import           Text.Printf (printf) 
import           Data.Monoid
import qualified Language.LLVC.UX    as UX
import           Language.LLVC.Types 

-------------------------------------------------------------------------------
-- | Serializing API
-------------------------------------------------------------------------------

class ToSmt a where 
  toSmt :: a -> Smt 

instance ToSmt (Pred a) where 
  toSmt = undefined 

instance ToSmt Type where 
  toSmt Float  = "Float32" 
  toSmt (I 1)  = "Bool" 
  toSmt (I 32) = "Int32" 
  toSmt (I n)  = UX.panic ("toSmt: Unhandled Int-" ++ show n) UX.junkSpan 

instance ToSmt Var where 
  toSmt = sanitizeVar

sanitizeVar :: Var -> Smt 
sanitizeVar cs = tx <$> cs 
  where 
    tx '%' = '_'
    tx c   = c 

-------------------------------------------------------------------------------
-- | Command API
-------------------------------------------------------------------------------

type    Smt = UX.Text
newtype Cmd = Cmd UX.Text
newtype VC  = VC [Cmd] 

instance Monoid VC where 
  mempty                  = VC [] 
  mappend (VC q1) (VC q2) = VC (q1 <> q2) 

-------------------------------------------------------------------------------
-- | Basic Commands 
-------------------------------------------------------------------------------

declare :: (Var, Type) -> VC 
declare (x, t) = cmd $ printf "(declare-const %s %s)" (toSmt x) (toSmt t)

assert :: Pred a -> VC 
assert p = cmd $ printf "(assert %s)" (toSmt p)

check :: Pred a -> VC 
check p = withBracket (assert (PNot p) <> checkSat) 

withBracket :: VC -> VC 
withBracket vc = push <> vc <> pop 

push, pop, checkSat :: VC 
push     = cmd "(push 1)"
pop      = cmd "(pop 1)"
checkSat = cmd "(check-sat)" 

preamble :: VC 
preamble = mconcat $ cmd <$> 
  [ "(set-logic QF_FPBV)"
  -- , "(define-sort Int1    () Bool)"
  , "(define-sort Int32   () (_ BitVec 32))"
  , "(define-sort Float32 () (_ FloatingPoint  8 24))"
  ]

cmd :: UX.Text -> VC
cmd s = VC [ Cmd s ]

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.LLVC.Smt 
  ( -- * Opaque SMT Query type 
    VC

    -- * Constructing Queries
  , declare
  , check
  , assert

    -- * Issuing Query
  , writeQuery 
  ) 
  where 

import           Text.Printf (printf) 
import           Data.Monoid
import           Language.LLVC.Types 
import qualified Language.LLVC.Utils as Utils
import qualified Language.LLVC.UX    as UX
import qualified Data.HashMap.Strict as M 

writeQuery :: FilePath -> VC -> IO () 
writeQuery f vc = writeFile f (toSmt (preamble <> vc))

-------------------------------------------------------------------------------
-- | Serializing API
-------------------------------------------------------------------------------

class ToSmt a where 
  toSmt :: a -> Smt 

instance ToSmt VC where 
  toSmt (VC cmds) = unlines [ c | Cmd c <- cmds] 

instance ToSmt Op where 
  toSmt BvXor  = "bvxor"
  toSmt BvAnd  = "bvand"
  toSmt BvOr   = "bvor"
  toSmt FpAdd  = "fp_add" 
  toSmt FpEq   = "fp.eq" 
  toSmt FpAbs  = "fp.abs" 
  toSmt FpLt   = "fp.lt" 
  toSmt ToFp32 = "to_fp_32" 
  toSmt Ite    = "ite" 
  toSmt Eq     = "=" 

instance ToSmt (Arg a) where 
  toSmt (ETLit n (I 32) _) = sigIntHex n (I 32) 
  toSmt (ETLit n Float _)  = printf "((_ to_fp 8 24) RNE %s)" (sigIntHex n Float)
  toSmt (ETLit n _ _)      = show n 
  toSmt (ELit n    _)      = show n 
  toSmt (EVar x    _)      = toSmt x 

convTable :: M.HashMap (Integer, Type) String
convTable = M.fromList 
  [ ((0x3980000000000000, Float), "addmin") ]
 
sigIntHex :: Integer -> Type -> Smt 
sigIntHex n t     = M.lookupDefault res (n, t) convTable 
  where 
    res 
      | 0 <= n    = s 
      | otherwise = printf "(- 0 %s)" s
    s             = "#x" ++ Utils.integerHex (abs n)
  
  

instance ToSmt Pred where 
  toSmt (PArg a)     = toSmt a 
  toSmt (PAtom o ps) = printf "(%s %s)"  (toSmt o) (toSmts ps) 
  toSmt (PNot p)     = printf "(not %s)" (toSmt p)
  toSmt (PAnd ps)    = printf "(and %s)" (toSmts ps)
  toSmt (POr  ps)    = printf "(or %s)"  (toSmts ps)
  toSmt PTrue        =        "true"     

toSmts :: (ToSmt a) => [a] -> Smt
toSmts = unwords . fmap toSmt

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

assert :: Pred -> VC 
assert p = cmd $ printf "(assert %s)" (toSmt p)

check :: Pred -> VC 
check PTrue = mempty 
check p     = withBracket (assert (PNot p) <> checkSat) 

withBracket :: VC -> VC 
withBracket vc = push <> vc <> pop 

push, pop, checkSat :: VC 
push     = cmd "(push 1)"
pop      = cmd "(pop 1)"
checkSat = cmd "(check-sat)" 

preamble :: VC 
preamble = mconcat $ cmd <$> 
  [ "(set-logic QF_FPBV)"
  , "(define-sort Int1    () Bool)"
  , "(define-sort Int32   () (_ BitVec 32))"
  -- , "(define-sort Float32 () (_ FloatingPoint  8 24))"
  , "(define-fun to_fp_32 ((a Int32)) Float32  ((_ to_fp 8 24) RNE a))"
  , "(define-fun fp_add ((a Float32) (b Float32)) Float32 (fp.add RNE a b))"
  ]

cmd :: UX.Text -> VC
cmd s = VC [ Cmd s ]

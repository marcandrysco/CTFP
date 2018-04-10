{-# LANGUAGE RecordWildCards #-}

module Language.LLVC.Verify where 

import           Data.Monoid
import qualified Language.LLVC.UX    as UX
import           Language.LLVC.Types 

verify :: FilePath -> IO ()
verify f = do 
  putStrLn ("LLVC: checking " ++ show f) 
  return ()

newtype Smt = Smt UX.Text
newtype Cmd = Cmd UX.Text
newtype VC  = VC [Cmd] 

instance Monoid VC where 
  mempty                  = VC [] 
  mappend (VC q1) (VC q2) = VC (q1 <> q2) 

vcFun :: Program a -> FnDef a -> VC 
vcFun env fd@(FnDef { fnBody = Just fb })
  =  mconcatMap declare      (fnArgs fd) 
  <> mconcatMap (vcAsgn env) (fnAsgns fb)
  <> checkValid (subst (fnPost fd) retVar (snd (fnRet fb))) 
vcFun _ _ 
  =  mempty 

mconcatMap :: (Monoid b) => (a -> b) -> [a] -> b 
mconcatMap f = mconcat . fmap f

vcAsgn :: Program a -> ((Var, a), Expr a) -> VC 
vcAsgn = undefined 

subst :: Pred a -> Var -> Expr a -> Pred a 
subst = undefined 

retVar :: Var 
retVar = "%ret"

declare :: (Var, Type) -> VC 
declare (_x, _t) = undefined

checkValid :: Pred a -> VC 
checkValid p = withBracket (assert (PNot p) <> checkSat) 

toSmt :: Pred a -> Smt 
toSmt = undefined 

assert :: Pred a -> VC 
assert _p = undefined 

checkSat :: VC 
checkSat = undefined 

withBracket :: VC -> VC 
withBracket vc = push <> vc <> pop 
  where 
    push       = VC [Cmd "(push 1)"]
    pop        = VC [Cmd "(pop 1)"]

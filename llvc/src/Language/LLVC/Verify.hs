{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.LLVC.Verify where 

-- import           Text.Printf (printf) 
-- import qualified Language.LLVC.UX    as UX
import           Data.Monoid
import           Language.LLVC.Smt   
import           Language.LLVC.Types 

verify :: FilePath -> IO ()
verify f = do 
  putStrLn ("LLVC: checking " ++ show f) 
  return ()

vcFun :: Program a -> FnDef a -> VC 
vcFun env fd@(FnDef { fnBody = Just fb })
  =  mconcatMap declare      (fnArgs fd) 
  <> mconcatMap (vcAsgn env) (fnAsgns fb)
  <> check      (subst (fnPost fd) retVar (snd (fnRet fb))) 
vcFun _ _ 
  =  mempty 

mconcatMap :: (Monoid b) => (a -> b) -> [a] -> b 
mconcatMap f = mconcat . fmap f

-------------------------------------------------------------------------------
contractAt :: Program a -> Fn -> Var -> [TypedArg a] -> (Pred a, Pred a)
contractAt = undefined

varType :: Program a -> Fn -> [TypedArg a] -> Type -> Type 
varType = undefined
-------------------------------------------------------------------------------

vcAsgn :: Program a -> ((Var, a), Expr a) -> VC 
vcAsgn env ((x, _), ECall fn tys t _) 
                = declare (x, tx) 
               <> check  pre 
               <> assert post 
  where 
    (pre, post) = contractAt env fn x tys 
    tx          = varType    env fn   tys t  

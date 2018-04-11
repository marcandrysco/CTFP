{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.LLVC.Verify where 

-- import           Text.Printf (printf) 
-- import qualified Language.LLVC.UX    as UX
import           Data.Monoid
import           Language.LLVC.Utils 
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
  <> check      (subst (fnPost fd) [(retVar, snd (fnRet fb))]  ) 
vcFun _ _ 
  =  mempty 

vcAsgn :: Program a -> ((Var, a), Expr a) -> VC 
vcAsgn env ((x, _), ECall fn tys tx l) 
                = declare (x, tx) 
               <> check  pre 
               <> assert post 
  where 
    (pre, post) = contractAt env fn x tys l 
    -- tx          = resultType env fn   tys t  

contractAt :: Program a -> Fn -> Var -> [TypedArg a] -> a -> (Pred a, Pred a)
contractAt env fn rv tys l = (pre, post) 
  where 
    pre                    = subst (ctPre  ct) su 
    post                   = subst (ctPost ct) su 
    su                     = zip formals actuals 
    actuals                = EVar rv l : (snd <$> tys) 
    formals                = retVar    : ctParams ct
    ct                     = contract env fn 

-- resultType :: Program a -> Fn -> [TypedArg a] -> Type -> Type 
-- resultType _ _ _ t           = t 
-- resultType _ (FnFunc _) _ t  = t 
-- resultType _ (FnBin _) _  t  = t 
-- resultType _ (FnFcmp _) _ t  = t 
-- resultType _ FnSelect _ t    = t 
-- resultType _ FnBitcast _ t   = t 

-------------------------------------------------------------------------------


contract :: Program a -> Fn -> Contract a 
contract env fn = undefined 

data Contract a = Contract 
  { ctParams :: ![Var] 
  , ctResult :: !Var 
  , ctPre    :: !(Pred a)
  , ctPost   :: !(Pred a)
  } deriving (Eq, Ord, Show)
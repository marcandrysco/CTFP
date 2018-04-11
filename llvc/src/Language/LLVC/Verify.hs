{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.LLVC.Verify where 

-- import           Text.Printf (printf) 
-- import qualified Language.LLVC.UX    as UX
import qualified Data.Maybe          as Mb 
import qualified Data.HashMap.Strict as M 
import           Data.Monoid
import           Language.LLVC.UX 
import           Language.LLVC.Utils 
import           Language.LLVC.Smt   
import           Language.LLVC.Types 

verify :: FilePath -> IO ()
verify f = do 
  putStrLn ("LLVC: checking " ++ show f) 
  return ()

vc :: (Located a) => Program a -> VC 
vc p    = mconcatMap (vcFun env) (M.elems p) 
  where 
    env = mkEnv p 

vcFun :: (Located a) => Env -> FnDef a -> VC 
vcFun env fd@(FnDef { fnBody = Just fb })
  =  mconcatMap declare      (fnArgs fd) 
  <> mconcatMap (vcAsgn env) (fnAsgns fb)
  <> check      (subst su    (fnPost fd)) 
  where 
    su = [(retVar, snd (fnRet fb))]
vcFun _ _ 
  =  mempty 

vcAsgn :: (Located a) => Env  -> ((Var, a), Expr a) -> VC 
vcAsgn env ((x, _), ECall fn tys tx l) 
                = declare (x, tx) 
               <> check  pre 
               <> assert post 
  where 
    (pre, post) = contractAt env fn x tys l 
    -- tx          = resultType env fn   tys t  

contractAt :: (Located a) => Env -> Fn -> Var -> [TypedArg a] -> a -> (Pred, Pred)
contractAt env fn rv tys l = (pre, post) 
  where 
    pre                    = subst su (ctPre  ct)
    post                   = subst su (ctPost ct)
    su                     = zip formals actuals 
    actuals                = EVar rv l : (snd <$> tys) 
    formals                = retVar    : ctParams ct
    ct                     = contract env fn (sourceSpan l) 

-- resultType :: Program a -> Fn -> [TypedArg a] -> Type -> Type 
-- resultType _ _ _ t           = t 
-- resultType _ (FnFunc _) _ t  = t 
-- resultType _ (FnBin _) _  t  = t 
-- resultType _ (FnFcmp _) _ t  = t 
-- resultType _ FnSelect _ t    = t 
-- resultType _ FnBitcast _ t   = t 

-------------------------------------------------------------------------------
-- | Contracts for all the `Fn` stuff.
-------------------------------------------------------------------------------
data Contract = Ct
  { ctParams :: ![Var] 
  , ctPre    :: !Pred
  , ctPost   :: !Pred
  } deriving (Eq, Show)

type Env = M.HashMap Fn Contract 

contract :: Env -> Fn -> SourceSpan -> Contract
contract env fn l = Mb.fromMaybe err (M.lookup fn env)
  where 
    err           = panic msg l 
    msg           = "Cannot find contract for: " ++ show fn

mkEnv :: Program a -> Env 
mkEnv p   = M.fromList (prims ++ defs) 
  where 
    prims = primitiveContracts 
    defs  = [ (FnFunc v, defContract d)  | (v, d) <- M.toList p ]  

defContract :: FnDef a -> Contract 
defContract = undefined

-- | We could parse these in too, in due course.
primitiveContracts :: [(Fn, Contract)]
primitiveContracts =  
  [ (FnFcmp Olt , undefined
    )
  , (FnBin BvXor, undefined 
    )
  , (FnBin BvAnd, undefined 
    )
  , (FnBin FAdd , undefined 
    )
  , (FnSelect   , undefined
    )
  , (FnBitcast  , undefined)

  , (FnFunc "@llvm.fabs.f32", onlyPost 1 undefined)

  ] 

onlyPost :: Int -> Pred -> Contract 
onlyPost n = Ct (paramVar <$> [0..(n-1)]) pTrue 

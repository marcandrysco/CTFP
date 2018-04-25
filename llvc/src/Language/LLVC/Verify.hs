{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.LLVC.Verify (vcs) where 

import           Prelude hiding (pred)
import qualified Data.List           as L 
import qualified Data.Maybe          as Mb 
import qualified Data.HashMap.Strict as M 
import           Data.Monoid
import qualified Language.LLVC.Parse as Parse 
import           Language.LLVC.UX 
import           Language.LLVC.Utils 
import           Language.LLVC.Smt   
import           Language.LLVC.Types hiding (contract) 
import qualified Text.Printf as Printf 

-------------------------------------------------------------------------------
vcs :: (Located a) => Program a -> [(Var, VC)] 
-------------------------------------------------------------------------------
vcs p   = [ (f, vcFun env fd fb (Just (pre, post)))
          | (f, fd)     <- M.toList p 
          , fb          <- Mb.maybeToList (fnBody fd)
          , (pre, post) <- Mb.maybeToList (ctProps $ fnCon fd) 
          ] 
  where 
    env = mkEnv p 

vcFun :: (Located a) => Env a -> FnDef a -> FnBody a -> Maybe (Pred, Pred) -> VC 
vcFun env fd fb prop 
                =  comment    ("VC for: " ++  fnName fd)
                <> mconcatMap declare      [(inV env x, t) | (x,t) <- argTys] 
                <> assert                  (inP env pre)
                <> mconcatMap (vcStmt env) (fnStmts  fb)
                <> declare    (inV env retVar, rT)
                <> equate     env [rv] env [rE] l 
                <> check      err          (inP env post) 
  where 
    -- su          = [(retVar, retExp)]
    rv          = EVar retVar l
    (rT, rE)    = fnRet fb
    err         = mkError "Failed ensures check!" (sourceSpan l) 
    l           = getLabel rE 
    (argTys, pre, post) = case prop of 
                            Nothing     -> ([], PTrue, PTrue)
                            Just (p, q) -> (fnArgTys fd, p, q) 

vcStmt :: (Located a) => Env a -> Stmt a -> VC 
vcStmt env (SAssert p l) 
  = check err (inP env p) 
  where 
    err = mkError "Failed assert" (sourceSpan l)
vcStmt env asgn@(SAsgn x (ECall fn tys tx l) _)
  =  comment (pprint asgn)
  <> declare (inV env x, tx) 
  <> vcSig env fn x tys (sig env fn l) l 

vcSig :: (Located a) => Env a -> Fn -> Var -> [TypedArg a] -> Sig -> a -> VC 
vcSig env _ x tys (SigC ct) l 
                = check err (inP env pre)
               <> assert    (inP env post) 
  where 
    (pre, post) = contractAt ct x tys l 
    err         = mkError "Failed requires check" (sourceSpan l)

vcSig env (FnFunc f) rv tys (SigI i) l 
  | Just fb <- fnBody fd
                = mconcatMap declare      [(inV env' x, t) | (x,t) <- fnArgTys fd ] 
               <> equate env actuals env' (evl <$> formals) l 
               <> vcFun env' fd fb Nothing
               <> equate env [evl rv] env' [evl retVar] l 
  where 
    fd          = fnDef env f l  
    env'        = pushEnv i env 
    formals     = fst <$> fnArgTys fd
    actuals     = snd <$> tys        
    evl v       = EVar v l

vcSig _ _ fn _ _ l 
                = panic ("VCSig for Fn: " ++ show fn) (sourceSpan l)

equate :: (Located a) => Env a -> [Arg a] -> Env a -> [Arg a] -> a -> VC
equate env1 x1s env2 x2s l = assert $ smtPred $ PAnd $ zipWith eq x1s' x2s'
  where 
    x1s'                   = inA env1 <$> x1s 
    x2s'                   = inA env2 <$> x2s 
    eq x1 x2               = PAtom Eq (PArg <$> [bare x1, bare x2])
    sp                     = sourceSpan l
    bare                   = fmap (const sp)

contractAt :: (Located a) => Contract -> Var -> [TypedArg a] -> a -> (Pred, Pred)
contractAt ct rv tys l = (pre, post) 
  where 
    (pre, post)        = (subst su pre0, subst su post0)
    Just (pre0, post0) = ctProps ct 
    su                 = zip formals actuals 
    actuals            = EVar rv l : (snd <$> tys) 
    formals            = retVar    : ctParams ct

-------------------------------------------------------------------------------
-- | Renaming locals in a Context
-------------------------------------------------------------------------------
inP :: Env a -> Pred -> SmtPred
inP env p = smtPred (substf f p) 
  where 
    f x l = Just (EVar (inV env x) l)

inA :: Env a -> Arg a -> Arg a 
inA env (EVar v l) = EVar (inV env v) l  
inA _   a          = a 

inV :: Env a -> Var -> Var 
inV env x@('%':_) = stackPrefix (eStack env) ++ x 
inV _   x         = x 

-- inV env x = stackPrefix (eStack env) ++ x 

stackPrefix :: [Int] -> String 
stackPrefix [] = "" 
stackPrefix is = L.intercalate "_" ("tmp" : (show <$> is))




-------------------------------------------------------------------------------
-- | Contracts for all the `Fn` stuff.
-------------------------------------------------------------------------------
data Sig = SigC !Contract             -- ^ function with specification
         | SigI !Int                  -- ^ function to be inlined
         
data Env a = Env 
  { eSig   :: M.HashMap Fn  Contract  -- ^ map from functions to code 
  , eId    :: M.HashMap Var Int       -- ^ unique id per function 
  , eDef   :: M.HashMap Var (FnDef a) -- ^ definitions of functions
  , eStack :: [Int]                   -- ^ non-empty stack of function names
  }

pushEnv :: Int -> Env a -> Env a 
pushEnv i env = env { eStack = i : eStack env } 

sig :: (Located l) => Env a -> Fn -> l -> Sig 
sig env fn l = case M.lookup fn (eSig env) of 
  Just ct -> SigC ct 
  Nothing -> case fn of 
               FnFunc f -> SigI (fnId env f l) 
               _        -> errMissing "definition" fn l 

fnDef :: (Located l) => Env a -> Var -> l -> FnDef a 
fnDef env v l = Mb.fromMaybe err (M.lookup v (eDef env))
  where 
    err       = errMissing "(inline) definition" v l

fnId :: (Located l) => Env a -> Var -> l -> Int 
fnId env v l = Mb.fromMaybe err (M.lookup v (eId env)) 
  where 
    err      = errMissing "id" v l 

errMissing :: (Located l, Show x) => String -> x -> l -> a 
errMissing thing x l = panic msg (sourceSpan l)
  where 
    msg              = Printf.printf "Cannot find %s for %s" thing (show x) 

mkEnv :: Program a -> Env a 
mkEnv p   = Env (M.fromList sigs) (M.fromList fIds) (M.fromList fDefs) [] 
  where 
    fIds   = zip (fst <$> fDefs) [0..]
    fDefs  = [ (f, d)  | (f, d)    <- M.toList p ] 
    sigs   = [ (fn, ct) | (fn, ct) <- fPrims ++ fCons, Mb.isJust (ctProps ct) ]  
    fPrims = primitiveContracts 
    fCons  = [ (FnFunc v, fnCon d) | (v, d) <- M.toList p]  
     

-- | We could parse these in too, in due course.
primitiveContracts :: [(Fn, Contract)]
primitiveContracts =  
  [ ( FnCmp Float Olt 
    , postCond 2 "(= %ret (fp.lt %arg0 %arg1))" 
    )
  , ( FnCmp (I 32) Slt 
    , postCond 2 "(= %ret (lt32 %arg0 %arg1))" 
    )
  , ( FnBin BvXor
    , postCond 2 "(= %ret (bvxor %arg0 %arg1))" 
    )
  , ( FnBin BvOr
    , postCond 2 "(= %ret (bvor  %arg0 %arg1))" 
    )
  , ( FnBin BvAnd
    , postCond 2 "(= %ret (bvand %arg0 %arg1))" 
    )
  , (FnBin FpAdd 
    , mkContract 2 
        "(and (fp_rng addmin %arg0) (fp_rng addmin %arg1))"
        "(= %ret (fp_add %arg0 %arg1))" 
    )
  , (FnBin FpSub
    , mkContract 2 
        "(and (fp_rng submin %arg0) (fp_rng submin %arg1))"
        "(= %ret (fp_sub %arg0 %arg1))" 
    )
  , (FnBin FpMul 
    , mkContract 2 
        "(and (fp_rng mulmin %arg0) (fp_rng mulmin %arg1))"
        "(= %ret (fp_mul %arg0 %arg1))" 
    )
  , ( FnSelect   
    , postCond 3 "(= %ret (ite %arg0 %arg1 %arg2))" 
    )
  , ( FnBitcast (I 32) Float
    , postCond 1 "(= (to_ieee_bv %ret) %arg0)"
    )

  , ( FnBitcast Float (I 32)
    , postCond 1 "(= %ret (to_ieee_bv  %arg0))" )
  ] 

postCond :: Int -> Text -> Contract 
postCond n = mkContract n "true" 

mkContract :: Int -> Text -> Text -> Contract 
mkContract n tPre tPost = Ct 
  { ctParams = paramVar <$> [0..(n-1)]
  , ctProps  = Just (pred tPre, pred tPost) 
  } 

pred :: Text -> Pred 
pred = Parse.parseWith Parse.predP "primitive-contracts" 

-- putStrLn $ printf "The value of %d in hex is: 0x%08x" i i
-- putStrLn $ printf "The value of %d in binary is: %b"  i i

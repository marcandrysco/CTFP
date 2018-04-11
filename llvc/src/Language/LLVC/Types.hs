{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.LLVC.Types where 

-- import qualified Data.Maybe          as Mb
import Data.Hashable
import GHC.Generics
import qualified Data.List           as L 
import qualified Data.HashMap.Strict as M 
import qualified Language.LLVC.UX    as UX 
import Text.Printf (printf)

data Type 
  = Float 
  | I Int                      -- ^ Int of a given size 1, 16, 32 etc.
  deriving (Eq, Ord, Show)

instance UX.PPrint Type where 
  pprint Float = "float"
  pprint (I n) = "i" ++ show n

type Var   = UX.Text 

-------------------------------------------------------------------------------
-- | 'Fn' correspond to the different kinds of "operations"
-------------------------------------------------------------------------------
data Fn 
  = FnFcmp    Rel               -- ^ 'fcmp' olt 
  | FnBin     Op                -- ^ binary operation 
  | FnSelect                    -- ^ ternary 'select' 
  | FnBitcast                   -- ^ 'bitcast' 
  | FnFunc    Var               -- ^ something that is 'call'ed 
  deriving (Eq, Ord, Show, Generic)

data Rel 
  = Olt 
  deriving (Eq, Ord, Show, Generic) 

instance Hashable Fn 

instance UX.PPrint Rel where 
  pprint Olt = "olt"

instance UX.PPrint Fn where 
  pprint (FnFcmp r) = printf "fcmp %s" (UX.pprint r)
  pprint (FnBin  o) = UX.pprint o
  pprint FnSelect   = "select" 
  pprint FnBitcast  = "bitcast" 
  pprint (FnFunc f) = f

-------------------------------------------------------------------------------
-- | 'Expr' correspond to the RHS of LLVM assignments 
-------------------------------------------------------------------------------
data Arg a 
  = ELit Integer a 
  | EVar Var     a 
  deriving (Eq, Ord, Show, Functor)

data Expr a 
  = ECall Fn [TypedArg a] Type a -- ^ Function name, args, result type 
  deriving (Eq, Ord, Show, Functor)

type TypedArg  a = (Type, Arg  a)
type TypedExpr a = (Type, Expr a)

instance UX.PPrint (Arg a) where 
  pprint (ELit n _) = show n 
  pprint (EVar x _) = x 

instance UX.PPrint (Expr a) where 
  pprint (ECall fn tes t _) = ppCall fn tes t 

ppCall :: Fn -> [TypedArg a] -> Type -> UX.Text 
ppCall (FnFunc f) tes t   
  = printf "call %s %s (%s)" (UX.pprint t) f (pprints tes) 
ppCall (FnBin o) [te1, (_, e2)] _ 
  = printf "%s %s, %s" (UX.pprint o) (UX.pprint te1) (UX.pprint e2) 
ppCall (FnFcmp r) [te1, (_, e2)] _ 
  = printf "fcmp %s %s, %s" (UX.pprint r) (UX.pprint te1) (UX.pprint e2) 
ppCall FnSelect tes _ 
  = printf "select %s" (pprints tes)
ppCall FnBitcast [te] t 
  = printf "bitcast %s to %s" (UX.pprint te) (UX.pprint t) 
ppCall f tes _ 
  = UX.panic ("ppCall: TBD" ++ UX.pprint f ++ pprints tes) UX.junkSpan

instance UX.PPrint a => UX.PPrint (Type, a) where 
  pprint (t, e) = printf "%s %s" (UX.pprint t) (UX.pprint e)

-- instance UX.PPrint a => UX.PPrint [a] where 
pprints :: (UX.PPrint a) => [a] -> UX.Text
pprints = L.intercalate ", " . fmap UX.pprint 

-------------------------------------------------------------------------------
-- | A 'Program' is a list of Function Definitions  
-------------------------------------------------------------------------------

type Program a = M.HashMap Var (FnDef a)  -- ^ A list of function declarations

data FnBody a = FnBody 
  { fnAsgns :: [((Var, a), Expr a)]  -- ^ Assignments for each variable
  , fnRet   :: !(TypedArg a)         -- ^ Return value
  }
  deriving (Eq, Ord, Show, Functor)

data FnDef a = FnDef 
  { fnName :: !Var                   -- ^ Name
  , fnArgs :: ![(Var, Type)]         -- ^ Parameters and their types 
  , fnOut  :: !Type                  -- ^ Output type 
  , fnBody :: Maybe (FnBody a)       -- ^ 'Nothing' for 'declare', 'Just fb' for 'define' 
  , fnPre  :: !(Pred a)              -- ^ Precondition / "requires" clause               
  , fnPost :: !(Pred a)              -- ^ Postcondition / "ensures" clause               
  , fnLab  :: a                      
  }
  deriving (Eq, Ord, Show, Functor)

instance UX.PPrint (FnDef a) where 
  pprint fd        = printf "%s %s %s(%s) %s" dS oS (fnName fd) aS bS
    where
      oS           = UX.pprint (fnOut fd)
      (dS, bS, aS) = case fnBody fd of 
                       Nothing -> ("declare", "\n"       , pprints (snd <$> fnArgs fd))
                       Just b  -> ("define" , UX.pprint b, pprints (fnArgs fd) )
         
instance UX.PPrint (Var, Type) where 
  pprint (x, t) = printf "%s %s" (UX.pprint t) x 

instance UX.PPrint (FnBody a) where 
  pprint (FnBody xes te)  = unlines ("{" : fmap ppAsgn xes ++ [ppRet te, "}"]) 
    where 
      ppRet               = printf "  ret %s"     . UX.pprint  
      ppAsgn ((x,_), e)   = printf "  %s = %s"  x (UX.pprint e)

instance UX.PPrint (Program a) where 
  pprint p = L.intercalate "\n\n" (UX.pprint <$> M.elems p)

-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

class Labeled thing where 
  getLabel :: thing a -> a 

instance Labeled Arg where 
  getLabel (ELit _ z)      = z 
  getLabel (EVar _ z)      = z 

instance Labeled Expr where 
  getLabel (ECall _ _ _ z) = z 
  
-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

mkFcmp :: Rel -> Type -> Arg a -> Arg a -> a -> Expr a 
mkFcmp r t e1 e2 = ECall (FnFcmp r) [(t, e1), (t, e2)] (I 1)

mkSelect :: (Show a) => TypedArg a -> TypedArg a -> TypedArg a -> a -> Expr a 
mkSelect x@(t1, _) y@(t2, _) z@(t3, _) l 
  | t1 == I 1 && t2 == t3 = ECall FnSelect [x, y, z] t2 l 
  | otherwise             = error $ "Malformed Select: " ++ show [x, y, z]

mkBitcast :: TypedArg a -> Type -> a -> Expr a 
mkBitcast te = ECall FnBitcast [te]

mkOp :: Op -> TypedArg a -> Arg a -> a -> Expr a 
mkOp o (t, e1) e2 = ECall (FnBin o) [(t, e1), (t, e2)] t 

mkCall :: Var -> [(Var, Type)] -> Type -> a -> Expr a 
mkCall f xts t sp = ECall (FnFunc f) tes t sp
  where 
    tes           = [ (tx, EVar x sp) | (x, tx) <- xts]

decl :: Var -> [Type] -> Type -> a -> FnDef a 
decl f ts t l = FnDef 
  { fnName = f 
  , fnArgs = zip primArgs ts 
  , fnOut  = t 
  , fnBody = Nothing 
  , fnPre  = pTrue
  , fnPost = pTrue
  , fnLab  = l 
  }

defn :: Var -> [(Var, Type)] -> FnBody a -> Type -> a -> FnDef a 
defn f xts b t l = FnDef 
  { fnName = f 
  , fnArgs = xts 
  , fnOut  = t 
  , fnBody = Just b 
  , fnPre  = pTrue 
  , fnPost = pTrue 
  , fnLab  = l 
  }

primArgs :: [Var]
primArgs = ["%arg" ++ show i | i <- [0..] :: [Integer]] 

retVar :: Var 
retVar = "%ret"


-------------------------------------------------------------------------------
-- | Predicates 
-------------------------------------------------------------------------------

-- | 'Op' are the builtin operations we will use with SMT (and which can)
--   appear in the contracts.
data Op 
  = FpEq 
  | FpAbs 
  | FpLt 
  | Ite 
  | ToFp32    -- ((_ to_fp 8 24) RNE r3)  
  | BvXor
  | BvAnd 
  | FAdd 
  deriving (Eq, Ord, Show)

instance UX.PPrint Op where 
  pprint BvXor  = "xor"
  pprint BvAnd  = "and"
  pprint FAdd   = "fadd" 
  pprint FpEq   = "fp.eq" 
  pprint FpAbs  = "fp.abs" 
  pprint FpLt   = "fp.lt" 
  pprint Ite    = "Ite" 
  pprint ToFp32 = "to_fp_32" 

-- | 'Pred' are boolean combinations of 'Expr' used to define contracts 
data Pred a 
  = PAtom  Op [Arg a]  
  | PNot   (Pred a)
  | PAnd   [Pred a]
  | POr    [Pred a]
  deriving (Eq, Ord, Show, Functor)

pTrue, pFalse :: Pred a 
pTrue  = POr []
pFalse = PAnd []

subst :: Pred a -> [(Var, Arg b)] -> Pred a 
subst = undefined 


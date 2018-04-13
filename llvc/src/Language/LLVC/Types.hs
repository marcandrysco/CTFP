{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.LLVC.Types where 

-- import qualified Data.Maybe          as Mb
import           Data.Hashable
import           GHC.Generics
import qualified Data.List           as L 
import qualified Data.HashMap.Strict as M 
import qualified Language.LLVC.UX    as UX 
import           Text.Printf (printf)

data Type 
  = Float 
  | I Int                      -- ^ Int of a given size 1, 16, 32 etc.
  deriving (Eq, Ord, Show, Generic)

instance UX.PPrint Type where 
  pprint Float = "float"
  pprint (I n) = "i" ++ show n

type Var   = UX.Text 

-------------------------------------------------------------------------------
-- | 'Fn' correspond to the different kinds of "operations"
-------------------------------------------------------------------------------
data Fn 
  = FnCmp     Type Rel     -- ^ 'fcmp' olt 
  | FnBin     Op           -- ^ binary operation 
  | FnSelect               -- ^ ternary 'select' 
  | FnBitcast Type Type    -- ^ 'bitcast' 
  | FnFunc    Var          -- ^ something that is 'call'ed 
  deriving (Eq, Ord, Show, Generic)

data Rel 
  = Olt 
  | Slt  
  deriving (Eq, Ord, Show, Generic) 

instance Hashable Type 
instance Hashable Op 
instance Hashable Rel 
instance Hashable Fn 

instance UX.PPrint Rel where 
  pprint Olt = "olt"
  pprint Slt = "slt"

instance UX.PPrint Fn where 
  pprint (FnCmp Float r) = printf "fcmp %s" (UX.pprint r)
  pprint (FnCmp (I _) r) = printf "icmp %s" (UX.pprint r)
  pprint (FnBin  o)      = UX.pprint o
  pprint FnSelect       = "select" 
  pprint (FnBitcast {}) = "bitcast" 
  pprint (FnFunc f)     = f

-------------------------------------------------------------------------------
-- | 'Expr' correspond to the RHS of LLVM assignments 
-------------------------------------------------------------------------------
data Arg a 
  = ELit  !Integer       a    -- ^ integer 
  | ETLit !Integer !Type a    -- ^ integer interpreted at a type
  | EVar  !Var           a    -- ^ variable 
  | ECon  !UX.Text       a    -- ^ smt-string-literal e.g. #x00000005
  deriving (Eq, Ord, Show, Functor)

data Expr a 
  = ECall Fn [TypedArg a] Type a -- ^ Function name, args, result type 
  deriving (Eq, Ord, Show, Functor)

type TypedArg  a = (Type, Arg  a)
type TypedExpr a = (Type, Expr a)

instance UX.PPrint (Arg a) where 
  pprint (ELit  n _  ) = show n 
  pprint (ETLit n _ _) = show n 
  pprint (EVar  x _  ) = x 
  pprint (ECon  s _  ) = s 

instance UX.PPrint (Expr a) where 
  pprint (ECall fn tes t _) = ppCall fn tes t 

ppCmp :: Type -> Rel -> UX.Text 
ppCmp Float Olt = "fcmp olt"
ppCmp (I _) Slt = "icmp slt"
ppCmp t     r   = error $ "ppCmp: " ++ show (t, r)

ppCall :: Fn -> [TypedArg a] -> Type -> UX.Text 
ppCall (FnFunc f) tes t   
  = printf "call %s %s (%s)" (UX.pprint t) f (pprints tes) 
ppCall (FnBin o) [te1, (_, e2)] _ 
  = printf "%s %s, %s" (UX.pprint o) (UX.pprint te1) (UX.pprint e2) 
ppCall (FnCmp t r) [te1, (_, e2)] _ 
  = printf "%s %s, %s" (ppCmp t r) (UX.pprint te1) (UX.pprint e2) 
ppCall FnSelect tes _ 
  = printf "select %s" (pprints tes)
ppCall (FnBitcast _ _) [te] t 
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
  deriving (Eq, Show, Functor)

data FnDef a = FnDef 
  { fnName :: !Var                   -- ^ Name
  , fnArgs :: ![Type]                -- ^ Parameters and their types 
  , fnOut  :: !Type                  -- ^ Output type 
  , fnCon  :: !Contract              -- ^ Specification 
  , fnBody :: Maybe (FnBody a)       -- ^ 'Nothing' for 'declare', 'Just fb' for 'define' 
  , fnLab  :: a                     
  }
  deriving (Eq, Show, Functor)

data Contract = Ct
  { ctParams :: ![Var]               -- ^ Parameter names 
  , ctPre    :: !Pred                -- ^ Precondition / "requires" clause               
  , ctPost   :: !Pred                -- ^ Postcondition / "ensures" clause               
  } deriving (Eq, Show)

instance UX.PPrint (FnDef a) where 
  pprint fd        = printf "%s %s %s(%s) %s" dS oS (fnName fd) aS bS
    where
      oS           = UX.pprint (fnOut fd)
      (dS, bS, aS) = case fnBody fd of 
                       Nothing -> ("declare", "\n"       , pprints (fnArgs fd))
                       Just b  -> ("define" , UX.pprint b, pprints (fnArgTys fd) )
                      
fnArgTys    :: FnDef a -> [(Var, Type)]
fnArgTys fd = zip (ctParams (fnCon fd)) (fnArgs fd)

instance UX.PPrint (Var, Type) where 
  pprint (x, t) = printf "%s %s" (UX.pprint t) x 

instance UX.PPrint (FnBody a) where 
  pprint (FnBody xes te)  = unlines ("{" : fmap ppAsgn xes ++ [ppRet te, "}"]) 
    where 
      ppRet               = printf "  ret %s"     . UX.pprint  

ppAsgn :: ((Var, a), Expr b) -> UX.Text
ppAsgn ((x,_), e)   = printf "  %s = %s"  x (UX.pprint e)

instance UX.PPrint (Program a) where 
  pprint p = L.intercalate "\n\n" (UX.pprint <$> M.elems p)

-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

class Labeled thing where 
  getLabel :: thing a -> a 

instance Labeled Arg where 
  getLabel (ELit  _ z)   = z 
  getLabel (ETLit _ _ z) = z 
  getLabel (EVar _ z)    = z 
  getLabel (ECon _ z)    = z 

instance Labeled Expr where 
  getLabel (ECall _ _ _ z) = z 
  
-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

mkCmp :: Rel -> Type -> Arg a -> Arg a -> a -> Expr a 
mkCmp r t e1 e2 = ECall (FnCmp t r) [tLit (t, e1), tLit (t, e2)] (I 1)

mkSelect :: (Show a) => TypedArg a -> TypedArg a -> TypedArg a -> a -> Expr a 
mkSelect x@(t1, _) y@(t2, _) z@(t3, _) l 
  | t1 == I 1 && t2 == t3 = ECall FnSelect [x, tLit y, tLit z] t2 l 
  | otherwise             = error $ "Malformed Select: " ++ show [x, y, z]

tLit :: TypedArg a -> TypedArg a 
tLit (t, ELit n l) = (t, ETLit n t l) 
tLit z            = z 

mkBitcast :: TypedArg a -> Type -> a -> Expr a 
mkBitcast (t, e) t' = ECall (FnBitcast t t') [(t, e)] t'

mkOp :: Op -> TypedArg a -> Arg a -> a -> Expr a 
mkOp o (t, e1) e2 = ECall (FnBin o) [tLit (t, e1), tLit (t, e2)] t 

mkCall :: Var -> [(Var, Type)] -> Type -> a -> Expr a 
mkCall f xts t sp = ECall (FnFunc f) tes t sp
  where 
    tes           = [ (tx, EVar x sp) | (x, tx) <- xts]

decl :: Var -> [Type] -> Type -> Pred -> Pred -> a -> FnDef a 
decl f ts t pre post l = FnDef 
  { fnName = f 
  , fnArgs = ts 
  , fnOut  = t 
  , fnBody = Nothing 
  , fnCon  = contract (take n paramVars) pre post 
  , fnLab  = l 
  }
  where n  = length ts 

contract :: [Var] -> Pred -> Pred -> Contract 
contract xs pre post = Ct 
  { ctParams = xs 
  , ctPre    = pre  
  , ctPost   = post 
  }


defn :: Var -> [(Var, Type)] -> FnBody a -> Type -> Pred -> Pred -> a -> FnDef a 
defn f xts b t pre post l = FnDef 
  { fnName = f 
  , fnArgs = ts 
  , fnOut  = t 
  , fnBody = Just b 
  , fnCon  = contract xs pre post 
  , fnLab  = l 
  }
  where 
   (xs,ts) = unzip xts 

paramVars :: [Var]
paramVars = paramVar <$> [0..] 

paramVar :: Int -> Var 
paramVar i = "%arg" ++ show i 

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
  | FpAdd 
  | ToFp32    -- ((_ to_fp 8 24) RNE r3)  
  | BvOr
  | BvXor
  | BvAnd 
  | Ite 
  | Eq
  | SmtOp !Var
  deriving (Eq, Ord, Show, Generic)


instance UX.PPrint Op where 
  pprint BvOr      = "or"
  pprint BvXor     = "xor"
  pprint BvAnd     = "and"
  pprint FpAdd     = "fadd" 
  pprint FpEq      = "fp.eq" 
  pprint FpAbs     = "fp.abs" 
  pprint FpLt      = "fp.lt" 
  pprint ToFp32    = "to_fp_32" 
  pprint Ite       = "ite" 
  pprint Eq        = "=" 
  pprint (SmtOp x) = x

-- | 'Pred' are boolean combinations of 'Expr' used to define contracts 
data Pred 
  = PArg   !BareArg
  | PAtom  !Op ![Pred] 
  | PNot   !Pred 
  | PAnd   [Pred]
  | POr    [Pred]
  | PTrue 
  deriving (Eq, Show, Generic) 

subst :: (UX.Located a) => [(Var, Arg a)] -> Pred -> Pred
subst su             = go 
  where 
    m                = M.fromList [ (x, UX.sourceSpan <$> a) | (x, a) <- su ] 
    goa a@(EVar x _) = M.lookupDefault a x m 
    goa a            = a 
    go (PArg a)      = PArg (goa a)
    go (PAtom o ps)  = PAtom o (go <$> ps)
    go (PNot p)      = PNot (go p) 
    go (PAnd ps)     = PAnd (go <$> ps)
    go (POr  ps)     = POr  (go <$> ps)
    go (PTrue)       = PTrue 


-------------------------------------------------------------------------------
-- | 'Bare' aliases 
-------------------------------------------------------------------------------

type BareTypedArg  = TypedArg  UX.SourceSpan 
type BareProgram   = Program   UX.SourceSpan 
type BareArg       = Arg       UX.SourceSpan 
type BareDef       = FnDef     UX.SourceSpan 
type BareExpr      = Expr      UX.SourceSpan 
type BareBody      = FnBody    UX.SourceSpan 
type BareVar       = (Var,     UX.SourceSpan)


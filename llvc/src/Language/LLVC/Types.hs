{-# LANGUAGE DeriveFunctor #-}

module Language.LLVC.Types where 

import qualified Data.HashMap.Strict as M 
import qualified Language.LLVC.UX    as UX 

data Type 
  = Float 
  | I Int                      -- ^ Int of a given size 1, 16, 32 etc.
  deriving (Eq, Ord, Show)

type Var   = UX.Text 

-------------------------------------------------------------------------------
-- | 'Fn' correspond to the different kinds of "operations"
-------------------------------------------------------------------------------
data Fn 
  = FnFcmp    Rel               -- ^ fcmp olt 
  | FnBv      BvOp              -- ^ bitwise operation 
  | FnSelect    
  | FnBitcast 
  | FnFunc    Var 
  deriving (Eq, Ord, Show)

data BvOp
  = BvXor 
  | BvAnd 
  deriving (Eq, Ord, Show)

data Rel 
  = Olt 
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- | 'Expr' correspond to the RHS of LLVM assignments 
-------------------------------------------------------------------------------
data Expr a 
  = ELit  Integer               a
  | EVar  Var                   a -- ^ Bare variable e.g. '%a'
  | ECall Fn [TypedExpr a] Type a -- ^ Function name, args, result type 
  deriving (Eq, Ord, Show, Functor)

type TypedExpr a = (Type, Expr a)

-- | 'Pred' are boolean combinations of 'Expr' used to define contracts 
data Pred a 
  = PExpr  (Expr a) a 
  | PNot   (Expr a) a
  | PAnd   [Expr a] a
  | POr    [Expr a] a
  deriving (Eq, Ord, Show, Functor)

pTrue, pFalse :: a -> Pred a 
pTrue  = POr []
pFalse = PAnd []

-------------------------------------------------------------------------------
-- | A 'Program' is a list of Function Definitions  
-------------------------------------------------------------------------------
type Program a = M.HashMap Var (FnDef a)  -- ^ A list of function declarations

data FnBody a = FnBody 
  { fnDefs :: [(Var, Expr a)]        -- ^ Assignments for each variable
  , fnRet  :: !(TypedExpr a)         -- ^ Return value
  }
  deriving (Eq, Ord, Show, Functor)

data FnDef a = FnDef 
  { fnName :: !Var                   -- ^ Name
  , fnArgs :: ![(Var, Type)]         -- ^ Parameters and their types 
  , fnBody :: Maybe (FnBody a)       -- ^ 'Nothing' for 'declare', 'Just fb' for 'define' 
  , fnReq  :: !(Pred a)              -- ^ Precondition / "requires" clause               
  , fnEns  :: !(Pred a)              -- ^ Postcondition / "ensures" clause               
  , fnLab  :: a                      
  }
  deriving (Eq, Ord, Show, Functor)

-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

class Labeled thing where 
  getLabel :: thing a -> a 

instance Labeled Expr where 
  getLabel (ELit _ z)      = z 
  getLabel (EVar _ z)      = z 
  getLabel (ECall _ _ _ z) = z 
  
-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

mkFcmp :: Rel -> Type -> Expr a -> Expr a -> a -> Expr a 
mkFcmp r t e1 e2 = ECall (FnFcmp r) [(t, e1), (t, e2)] (I 1)

mkSelect :: (Show a) => TypedExpr a -> TypedExpr a -> TypedExpr a -> a -> Expr a 
mkSelect x@(t1, e1) y@(t2, e2) z@(t3, e3) l 
  | t1 == I 1 && t2 == t3 = ECall FnSelect [x, y, z] t2 l 
  | otherwise             = error $ "Malformed Select: " ++ show [x, y, z]

mkBitcast :: Type -> Expr a -> Type -> a -> Expr a 
mkBitcast t e = ECall FnBitcast [(t, e)]

mkBvOp :: BvOp -> Type -> Expr a -> Expr a -> a -> Expr a 
mkBvOp o t e1 e2 = ECall (FnBv o) [(t, e1), (t, e2)] t 

decl :: Var -> [Type] -> Type -> a -> FnDef a 
decl f ts t l = FnDef 
  { fnName = f 
  , fnArgs = zip args ts 
  , fnBody = Nothing 
  , fnReq  = pTrue l 
  , fnEns  = pTrue l 
  , fnLab  = l 
  }

args :: [Var]
args = ["%arg" ++ show i | i <- [0..]] 
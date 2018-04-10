module Language.LLVC.Types where 

import qualified Data.HashMap.Strict as M 

type Text = String

data Type 
  = Float 
  | I Int                      -- ^ Int of a given size 1, 16, 32 etc.
  deriving (Eq, Ord, Show)

type Var   = Text 

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
data Expr 
  = ELit  Integer
  | EVar  Var                     -- ^ Bare variable e.g. '%a'
  | ECall Fn [TypedExpr] Type     -- ^ Function name, args, result type 
--  | EType Expr Type               -- ^ Expression with type decoration e.g. 'float %a'
  deriving (Eq, Ord, Show)

type TypedExpr = (Type, Expr)

-- | 'Pred' are boolean combinations of 'Expr' used to define contracts 
data Pred 
  = PExpr  Expr  
  | PNot   Expr
  | PAnd  [Expr]
  | POr   [Expr]
  deriving (Eq, Ord, Show)


-------------------------------------------------------------------------------
-- | A 'Program' is a list of Function Definitions  
-------------------------------------------------------------------------------
type Program = M.HashMap Var FnDef  -- ^ A list of function declarations

data FnBody = FnBody 
  { fnDefs :: [(Var, Expr)]         -- ^ Assignments for each variable
  , fnRet  :: TypedExpr             -- ^ Return value
  }
  deriving (Eq, Ord, Show)

data FnDef = FnDef 
  { fnName :: Var                   -- ^ Name
  , fnArgs :: [(Var, Type)]         -- ^ Parameters and their types 
  , fnBody :: Maybe FnBody          -- ^ 'Nothing' for 'declare', 'Just fb' for 'define' 
  , fnReq  :: Pred                  -- ^ Precondition / "requires" clause               
  , fnEns  :: Pred                  -- ^ Postcondition / "ensures" clause               
  }
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- | Constructors 
-------------------------------------------------------------------------------

mkFcmp :: Rel -> Type -> Expr -> Expr -> Expr 
mkFcmp r t e1 e2 = ECall (FnFcmp r) [(t, e1), (t, e2)] (I 1)

mkSelect :: TypedExpr -> TypedExpr -> TypedExpr -> Expr 
mkSelect x@(t1, e1) y@(t2, e2) z@(t3, e3) 
  | t1 == I 1 && t2 == t3 = ECall FnSelect [x, y, z] t2 
  | otherwise             = error $ "Malformed Select: " ++ show [x, y, z]

mkBitcast :: Type -> Expr -> Type -> Expr 
mkBitcast t e = ECall FnBitcast [(t, e)]

mkBvOp :: BvOp -> Type -> Expr -> Expr -> Expr 
mkBvOp o t e1 e2 = ECall (FnBv o) [(t, e1), (t, e2)] t 


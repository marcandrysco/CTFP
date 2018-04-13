{-# LANGUAGE TupleSections   #-}

module Language.LLVC.Parse where -- ( parse, parseFile ) where

import           Control.Monad (void)
import qualified Data.HashMap.Strict        as M 
import           Text.Megaparsec hiding (parse)
import           Data.List.NonEmpty         as NE
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Char
-- import           Text.Megaparsec.Expr
import           Language.LLVC.Types
import           Language.LLVC.UX 

type Parser = Parsec SourcePos Text

--------------------------------------------------------------------------------
parseFile :: FilePath -> IO BareProgram 
--------------------------------------------------------------------------------
parseFile f = parse f <$> readFile f

--------------------------------------------------------------------------------
parse :: FilePath -> Text -> BareProgram 
----------------------------------------------------------------------------------
parse = parseWith programP

parseWith  :: Parser a -> FilePath -> Text -> a
parseWith p f s = case runParser (whole p) f s of
                    Left err -> panic (show err) (posSpan . NE.head . errorPos $ err)
                    Right e  -> e

--------------------------------------------------------------------------------
-- | Top-Level Program Parser
--------------------------------------------------------------------------------

programP :: Parser BareProgram 
programP = do 
  ds    <- many fnDefnP 
  return $ M.fromList [(fnName d, d) | Just d <- ds] 

fnDefnP :: Parser (Maybe BareDef) 
fnDefnP 
  =  (rWord "declare"   >> (Just <$> declareP)) 
 <|> (rWord "define"    >> (Just <$> defineP))
 <|> (rWord "attributes" >> attribDef >> return Nothing) 
 <?> "declaration" 

attribDef :: Parser ()
attribDef = attrP >> symbol "=" >> braces (many attributeP) >> return ()
  where 
    attributeP 
        =  rWord "nounwind"
       <|> rWord "readnone"
       <|> rWord "alwaysinline"
       <?> "attribute-keyword"

attrP :: Parser () 
attrP = symbol "#" >> integer >> return ()


declareP :: Parser BareDef 
declareP = do 
  outTy      <- typeP 
  (name, sp) <- identifier "@" 
  inTys      <- parens (sepBy typeP comma) <* many attrP
  pre        <- requiresP 
  post       <- ensuresP 
  return      $ decl name inTys outTy pre post sp

defineP :: Parser BareDef 
defineP = do 
  _               <- many (rWord "weak")
  outTy           <- typeP
  (name, sp)      <- identifier "@" 
  dArgs           <- argTypesP <* many attrP
  (pre,post,body) <- braces ((,,) <$> requiresP <*> ensuresP <*> bodyP) 
  return           $ defn name dArgs body outTy pre post sp

requiresP, ensuresP :: Parser Pred
requiresP = annotationP "requires"
ensuresP  = annotationP "ensures"

annotationP :: String -> Parser Pred
annotationP kw = symbol ";@" >> rWord kw >> predP

argTypeP :: Parser (Var, Type)
argTypeP = do 
  t <- typeP 
  x <- varP "%" 
  return (x, t)

bodyP :: Parser BareBody
bodyP = FnBody <$> many stmtP <*> retP 

stmtP :: Parser BareStmt 
stmtP 
  =  flip SAssert <$> (symbol ";@" *> rWord "assert") <*> predP
 <|> mkAsgn       <$> (identifier "%" <* symbol "=")  <*> exprP
  where 
    mkAsgn (x,l) e = SAsgn x e l 

-- assignP :: Parser (BareVar, BareExpr) 
-- assignP = (,) <$> identifier "%" <* symbol "=" <*> exprP

argTypesP :: Parser [(Var, Type)] 
argTypesP = parens (sepBy argTypeP comma) 

retP :: Parser (Type, BareArg)
retP = do 
  _       <- rWord "ret" 
  t       <- typeP 
  e       <- argP 
  return (t, e) 

argP :: Parser BareArg 
argP 
  =  uncurry ECon <$> identifier "#"
 <|> uncurry ELit <$> integer 
 <|> uncurry EVar <$> identifier "%" 
 <|> uncurry EVar <$> smtId 
 <?> "smt-argument"


exprP :: Parser BareExpr 
exprP 
  =  eCallP 
 <|> cmpP 
 <|> selectP 
 <|> bitcastP 
 <|> binExprP 
 <?> "expression"

binExprP :: Parser BareExpr
binExprP = do 
  (o, sp) <- llOpP 
  te1     <- typedArgP <* comma 
  e2      <- argP 
  return   $ mkOp o te1 e2 sp 

llOpP :: Parser (Op, SourceSpan) 
llOpP =   (BvAnd, ) <$> rWord "and" 
      <|> (BvXor, ) <$> rWord "xor" 
      <|> (BvOr, )  <$> rWord  "or" 
      <|> (FpAdd, ) <$> rWord "fadd" 
      <?>  "binary-op"

bitcastP :: Parser BareExpr 
bitcastP = do 
  sp    <- rWord "bitcast"
  te    <- typedArgP 
  _     <- rWord "to"
  t     <- typeP 
  return $ mkBitcast te t sp 

selectP :: Parser BareExpr 
selectP = do 
  sp    <- rWord "select"
  te1   <- typedArgP <* comma 
  te2   <- typedArgP <* comma 
  te3   <- typedArgP 
  return $ mkSelect te1 te2 te3 sp 

typedArgP :: Parser BareTypedArg  
typedArgP = (,) <$> typeP <*> argP

cmpP :: Parser BareExpr 
cmpP = do 
  sp    <- rWord "fcmp" <|> rWord "icmp"
  r     <- relP 
  t     <- typeP 
  e1    <- argP <* comma 
  e2    <- argP 
  return $ mkCmp r t e1 e2 sp
 
relP :: Parser Rel 
relP =  (rWord "olt" >> return Olt)
    <|> (rWord "slt" >> return Slt) 
    <?> "relation"

eCallP :: Parser BareExpr 
eCallP = do 
  t       <- rWord "call" *> typeP 
  (f, sp) <- identifier "@"
  xts     <- argTypesP 
  return   $ mkCall f xts t sp 

typeP :: Parser Type 
typeP =  (rWord "float" >> return Float)  
     <|> (rWord "i32"   >> return (I 32)) 
     <|> (rWord "i1"    >> return (I  1)) 
     <?> "type"

--------------------------------------------------------------------------------
-- | Contract Parser 
--------------------------------------------------------------------------------
predP :: Parser Pred 
predP =  parens pred0P 
     <|> const PTrue        <$> rWord "true" 
     <|> const (PNot PTrue) <$> rWord "false" 
     <?> "pred"

pred0P :: Parser Pred 
pred0P =  PAnd        <$> (rWord "and" *> many predP)
      <|> POr         <$> (rWord "or"  *> many predP) 
      <|> PNot        <$> (rWord "not" *>      predP) 
      <|> pAtomP 

pAtomP :: Parser Pred 
pAtomP 
  =  atom1 "fp.abs"   FpAbs
 <|> atom1 "to_fp_32" ToFp32 
 <|> atom2 "="        Eq 
 <|> atom2 "fp.eq"    FpEq 
 <|> atom2 "fp.lt"    FpLt 
 <|> atom2 "fp_add"   FpAdd 
 <|> atom2 "bvor"     BvOr 
 <|> atom2 "bvxor"    BvXor
 <|> atom2 "bvand"    BvAnd 
 <|> atom3 "ite"      Ite
 <|> atomOp 
 
atomOp :: Parser Pred 
atomOp = PAtom <$> (SmtOp . fst <$> smtId) <*> many pArgP 

atom1 :: Text -> Op -> Parser Pred 
atom1 kw o = (\x1 -> PAtom o [x1]) 
          <$> (rWord kw *> pArgP)

atom2 :: Text -> Op -> Parser Pred 
atom2 kw o = (\x1 x2 -> PAtom o [x1, x2]) 
          <$> (rWord kw *> pArgP) 
          <*> pArgP 

atom3 :: Text -> Op -> Parser Pred 
atom3 kw o = (\x1 x2 x3 -> PAtom o [x1, x2, x3]) 
          <$> (rWord kw *> pArgP) 
          <*> pArgP 
          <*> pArgP

pArgP :: Parser Pred 
pArgP =  PArg <$> argP 
     <|> parens pred0P 


--------------------------------------------------------------------------------
-- | Tokenisers and Whitespace
--------------------------------------------------------------------------------

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

-- RJ: rename me "space consumer"
sc :: Parser ()
sc = L.space (void spaceChar) lineCmnt blockCmnt
  where 
    lineCmnt  = L.skipLineComment  "; "
    blockCmnt = L.skipBlockComment "/*" "*/"

-- | `symbol s` parses just the string s (and trailing whitespace)
symbol :: String -> Parser String
symbol = L.symbol sc

comma :: Parser String
comma = symbol ","

colon :: Parser String
colon = symbol ":"

-- | 'parens' parses something between parenthesis.
parens :: Parser a -> Parser a
parens = betweenS "(" ")"

-- | 'brackets' parses something between [...] 
brackets :: Parser a -> Parser a
brackets = betweenS "[" "]"

-- | 'braces' parses something between {...}
braces :: Parser a -> Parser a
braces = betweenS "{" "}"

betweenS :: String -> String -> Parser a -> Parser a
betweenS l r = between (symbol l) (symbol r)

-- | `lexeme p` consume whitespace after running p
lexeme :: Parser a -> Parser (a, SourceSpan)
lexeme p = L.lexeme sc (withSpan p)

-- | 'integer' parses an integer.
integer :: Parser (Integer, SourceSpan)
-- integer = lexeme L.decimal
integer = lexeme (   (symbol "0x" *> L.hexadecimal) 
                  <|> L.signed sc L.decimal
                 ) 

-- | `rWord`
rWord   :: String -> Parser SourceSpan
rWord w = snd <$> (withSpan (string w) <* notFollowedBy alphaNumChar <* sc)

-- | list of reserved words
keywords :: [Text]
keywords =
  [ "define", "declare", "weak"
  , "float", "i32", "i1"
  , "call"
  , "fcmp", "olt", "select"
  , "bitcast", "to"
  , "and", "or"
  , "ret"
  , "true", "false"
  ]

withSpan' :: Parser (SourceSpan -> a) -> Parser a
withSpan' p = do
  p1 <- getPosition
  f  <- p
  p2 <- getPosition
  return (f (SS p1 p2))

withSpan :: Parser a -> Parser (a, SourceSpan)
withSpan p = do
  p1 <- getPosition
  x  <- p
  p2 <- getPosition
  return (x, SS p1 p2)

varP :: Text -> Parser Var
varP s = fst <$> identifier s 

identifier :: Text -> Parser (String, SourceSpan)
identifier s = lexeme (p >>= checkId)
  where
    p       = (++) <$> symbol s <*> many identChar 

smtId :: Parser (String, SourceSpan)
smtId = lexeme (p >>= checkId)
  where 
    p = (:) <$> lowerChar <*> many identChar 

checkId :: Text -> Parser Text
checkId x 
  | x `elem` keywords = fail $ "keyword " ++ show x ++ " cannot be an identifier"
  | otherwise         = return x

identChar :: Parser Char
identChar = oneOf ok <?> "identifier-char"
  where 
    ok    = "._" ++ ['0'.. '9'] ++ ['a' .. 'z'] ++ ['A' .. 'Z']

stretch :: (Monoid a) => [Expr a] -> a
stretch = mconcat . fmap getLabel


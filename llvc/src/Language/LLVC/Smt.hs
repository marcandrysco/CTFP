{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE BangPatterns         #-}

module Language.LLVC.Smt 
  ( -- * Opaque SMT Query type 
    VC

  -- * Initializing 
  , comment
  -- , preamble 

    -- * Constructing Queries
  , declare
  , check
  , assert

    -- * Issuing Query
  , writeQuery 
  
    -- * Executing Query 
  , runQuery 
  ) 
  where 

import qualified Data.Text                as T
import qualified Data.Text.Lazy.Builder   as LT
-- import           Text.PrettyPrint.HughesPJ
    
import           System.IO                (Handle)
import           System.Process

import           Text.Printf (printf) 
import           Data.Monoid
import           Language.LLVC.Types 
import qualified Language.LLVC.Utils as Utils
import qualified Language.LLVC.UX    as UX
import qualified Data.HashMap.Strict as M 
import qualified Paths_llvc 

writeQuery :: FilePath -> VC -> IO () 
writeQuery f vc = do 
  prelude  <- readPrelude 
  writeFile f $ prelude ++ toSmt vc 

readPrelude :: IO UX.Text 
readPrelude = readFile =<< Paths_llvc.getDataFileName "include/prelude.smt2"

-------------------------------------------------------------------------------
-- | Serializing API
-------------------------------------------------------------------------------

class ToSmt a where 
  toSmt :: a -> Smt 

instance ToSmt VC where 
  toSmt (VC cmds) = unlines (toSmt <$> cmds) 

instance ToSmt Cmd where 
  toSmt (Say s)    = s 
  toSmt (Hear s _) = s 

instance ToSmt Op where 
  toSmt BvAnd     = "bvand"
  toSmt BvOr      = "bvor"
  toSmt BvXor     = "bvxor"
  toSmt FpAdd     = "fp_add" 
  toSmt FpEq      = "fp.eq" 
  toSmt FpAbs     = "fp.abs" 
  toSmt FpLt      = "fp.lt" 
  toSmt ToFp32    = "(_ to_fp 8 24) RNE"
  toSmt Ite       = "ite" 
  toSmt Eq        = "=" 
  toSmt (SmtOp x) = x 

instance ToSmt (Arg a) where 
  toSmt (ETLit n (I 32) _) = sigIntHex n (I 32) 
  toSmt (ETLit n Float _)  = printf "((_ to_fp 8 24) RNE %s)" (sigIntHex n Float)
  toSmt (ETLit n _ _)      = show n 
  toSmt (ELit n    _)      = show n 
  toSmt (EVar x    _)      = toSmt x 
  toSmt (ECon x    _)      = x 

convTable :: M.HashMap (Integer, Type) String
convTable = M.fromList 
  [ ((0x3980000000000000, Float), "addmin") 
  , ((-1                , I 32) , "#xffffffff")
  ]
 
sigIntHex :: Integer -> Type -> Smt 
sigIntHex n t     = M.lookupDefault res (n, t) convTable 
  where 
    res 
      | 0 <= n    = "#x" ++ pad ++ nStr 
      | otherwise = UX.panic ("sigIntHex: negative" ++ show n) UX.junkSpan 
    nStr          = Utils.integerHex (abs n)
    pad           = replicate (8 - length nStr) '0' 
  
  

instance ToSmt Pred where 
  toSmt (PArg a)     = toSmt a 
  toSmt (PAtom o ps) = printf "(%s %s)"  (toSmt o) (toSmts ps) 
  toSmt (PNot p)     = printf "(not %s)" (toSmt p)
  toSmt (PAnd ps)    = printf "(and %s)" (toSmts ps)
  toSmt (POr  ps)    = printf "(or %s)"  (toSmts ps)
  toSmt PTrue        =        "true"     

toSmts :: (ToSmt a) => [a] -> Smt
toSmts = unwords . fmap toSmt

instance ToSmt Type where 
  toSmt Float  = "Float32" 
  toSmt (I 1)  = "Bool" 
  toSmt (I 32) = "Int32" 
  toSmt (I n)  = UX.panic ("toSmt: Unhandled Int-" ++ show n) UX.junkSpan 

instance ToSmt Var where 
  toSmt = sanitizeVar

sanitizeVar :: Var -> Smt 
sanitizeVar ('%':cs) = 'r' : (sanitizeChar <$> cs) 
sanitizeVar cs       = sanitizeChar <$> cs 

sanitizeChar :: Char -> Char 
sanitizeChar '%' = '_'
sanitizeChar c   = c 

-------------------------------------------------------------------------------
-- | Command API
-------------------------------------------------------------------------------

type    Smt = UX.Text
newtype VC  = VC [Cmd] 
data Cmd    = Say  !Smt 
            | Hear !Smt !UX.SourceSpan

instance Monoid VC where 
  mempty                  = VC [] 
  mappend (VC q1) (VC q2) = VC (q1 <> q2) 

-------------------------------------------------------------------------------
-- | VC Construction API 
-------------------------------------------------------------------------------

comment :: UX.Text -> VC 
comment s = say $ printf "; %s" s

declare :: (UX.Located l) => l -> (Var, Type) -> VC 
declare _ (x, t) = say $ printf "(declare-const %s %s)" (toSmt x) (toSmt t)

assert :: (UX.Located l) => l -> Pred -> VC 
assert _ PTrue = mempty 
assert _ p     = say $ printf "(assert %s)" (toSmt p)

check :: (UX.Located l) => l -> Pred -> VC 
check _ PTrue = mempty 
check l p     = withBracket (assert l (PNot p) <> checkSat sp)
  where 
    sp        = UX.sourceSpan l

withBracket :: VC -> VC 
withBracket vc = push <> vc <> pop 

push, pop :: VC 
push     = say  "(push 1)"
pop      = say  "(pop 1)"

checkSat :: UX.SourceSpan -> VC
checkSat l = VC [ Hear "(check-sat)" l ]

say :: UX.Text -> VC
say s = VC [ Say s ]

-------------------------------------------------------------------------------
-- | VC "Execution" API 
-------------------------------------------------------------------------------

runQuery :: VC -> IO [UX.SourceSpan]
runQuery = error "TODO:runQuery"

makeContext   :: Config -> FilePath -> IO Context
makeContext cfg f
  = do me       <- makeProcess cfg
       prelude  <- readPrelude 
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog     <- openFile smtFile WriteMode
       let me'   = me { ctxLog = Just hLog }
       mapM_ (smtWrite me') prelude
       return me'
    where
       smtFile = f <.> "smt2" 

smtWrite :: Context -> Raw -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-} do
  when (ctxVerbose me) $ LTIO.putStrLn "SMT READ"
  ln  <- smtReadRaw me
  res <- A.parseWith (smtReadRaw me) responseP ln
  case A.eitherResult res of
    Left e  -> Misc.errorstar $ "SMTREAD:" ++ e
    Right r -> do
      maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (ctxLog me)
      when (ctxVerbose me) $ LTIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
      return r

smtWriteRaw      :: Context -> Raw -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  hPutStrLnNow (ctxCout me) s
  maybe (return ()) (`hPutStrLnNow` s) (ctxLog me)

smtReadRaw       :: Context -> IO T.Text
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (ctxCin me)

hPutStrLnNow     :: Handle -> LT.Text -> IO ()
hPutStrLnNow h !s = LTIO.hPutStrLn h s >> hFlush h

type SmtParser a = Parser T.Text a

responseP :: SmtParser Response
responseP = {-# SCC "responseP" #-} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown

--------------------------------------------------------------------------------
command              :: Context -> Cmd -> IO Response
--------------------------------------------------------------------------------
command me !cmd       = say cmd >> hear cmd
  where
    env               = ctxSymEnv me
    say               = smtWrite me . Builder.toLazyText . runSmt2 env
    hear CheckSat     = smtRead me
    hear (GetValue _) = smtRead me
    hear _            = return Ok

makeProcess :: IO Context
makeProcess = do 
  (hOut, hIn, _ ,pid) <- runInteractiveCommand "z3" 
  loud <- isLoud
  return Ctx { ctxPid     = pid
             , ctxCin     = hIn
             , ctxCout    = hOut
             , ctxLog     = Nothing
             , ctxVerbose = loud
             }

data Response 
  = Ok 
  | Fail !UX.SourceSpan 

data Context = Ctx
  { ctxPid     :: !ProcessHandle
  , ctxCin     :: !Handle
  , ctxCout    :: !Handle
  , ctxLog     :: !(Maybe Handle)
  , ctxVerbose :: !Bool
  }
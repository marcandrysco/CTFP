module Language.LLVC.Utils where


import           Numeric   (showHex, showIntAtBase)
import qualified Data.Map  as M
import qualified Data.List as L
import           Data.Monoid
import           Data.Maybe (fromMaybe)
import           Data.Char (isSpace, intToDigit)
import           Control.Exception
import           Control.Monad
import           Text.Printf
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import           System.Timeout
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           System.Console.ANSI
import           Debug.Trace (trace)

--------------------------------------------------------------------------------
(>->) :: (a -> Either e b) -> (b -> c) -> a -> Either e c
--------------------------------------------------------------------------------
f >-> g = f >=> safe g
  where
    safe :: (a -> b) -> a -> Either c b
    safe h x = Right (h x)

--------------------------------------------------------------------------------
mconcatMap :: (Monoid b) => (a -> b) -> [a] -> b 
--------------------------------------------------------------------------------
mconcatMap f = mconcat . fmap f

groupBy :: (Ord k) => (a -> k) -> [a] -> [(k, [a])]
groupBy f = M.toList . L.foldl' (\m x -> inserts (f x) x m) M.empty

inserts :: (Ord k) => k -> v -> M.Map k [v] -> M.Map k [v]
inserts k v m = M.insert k (v : M.findWithDefault [] k m) m

dupBy :: (Ord k) => (a -> k) -> [a] -> [[a]]
dupBy f xs = [ xs' | (_, xs') <- groupBy f xs, 2 <= length xs' ]

trim :: String -> String
trim = f . f  where f = reverse . dropWhile isSpace

trimEnd :: String -> String
trimEnd = reverse . dropWhile isSpace . reverse  

executeShellCommand :: Maybe FilePath -> String -> Int -> IO ExitCode
executeShellCommand logMb cmd n = fromMaybe (ExitFailure 100) <$> body
  where
    body = timeout n . {- withFile logF AppendMode -} withH $ \h -> do
             let p       = (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
             (_,_,_,ph) <- createProcess p
             waitForProcess ph
    withH = case logMb of 
              Just logF -> withFile logF AppendMode
              Nothing   -> \act -> act stdout


data Phase = Start | Stop deriving (Show)

phase :: Phase -> String -> IO ()
phase p msg = putStrLn $ printf "**** %s : %s **************************************" (show p) msg

writeLoud :: String -> IO ()
writeLoud s = whenLoud $ putStrLn s >> hFlush stdout

ensurePath :: FilePath -> IO ()
ensurePath = createDirectoryIfMissing True . takeDirectory

safeReadFile :: FilePath -> IO (Either String String)
safeReadFile f = (Right <$> readFile f) `catch` handleIO f

handleIO :: FilePath -> IOException -> IO (Either String a)
handleIO f e = return . Left $ "Warning: Couldn't open " <> f <> ": " <> show e

traceShow :: (Show a) => String -> a -> a
traceShow msg x = trace (printf "TRACE: %s = %s" msg (show x)) x

safeHead :: a -> [a] -> a
safeHead def []    = def
safeHead _   (x:_) = x

getRange :: Int -> Int -> [a] -> [a]
getRange i1 i2
  = take (i2 - i1 + 1)
  . drop (i1 - 1)

integerHex :: Integer -> String 
integerHex i = showHex i "" 

integerBinary :: Integer -> String 
integerBinary i = showIntAtBase 2 intToDigit i "" 

-- putStrLn $ showHex 12 "" -- prints "c"
-- putStrLn $ showIntAtBase 2 intToDigit 12 "" -- prints "1100"

withColor :: Color -> IO () -> IO ()
withColor c act = do 
  setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
  act
  setSGR [ Reset]

data ExitStatus 
  = Safe 
  | Unsafe 
  | Crash 

exitStatus :: ExitStatus -> IO () 
exitStatus Safe   = withColor Green  $ putStrLn "Yay! Safe!"
exitStatus Unsafe = withColor Red    $ putStrLn "Yikes, errors found!"
exitStatus Crash  = withColor Yellow $ putStrLn "Oops, crash!"
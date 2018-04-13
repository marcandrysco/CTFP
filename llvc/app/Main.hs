module Main where

import Control.Monad (forM_) 
import Control.Exception
-- import System.Process (runCommand) 
import System.Environment 
import System.FilePath 
import System.Exit
import System.IO                        
import Language.LLVC.Parse 
import Language.LLVC.UX 
import qualified Language.LLVC.Utils as Utils 
import Language.LLVC.Verify 
import Language.LLVC.Smt 

main :: IO ()
main = exec `catch` esHandle stderr exitFailure

exec :: IO ()
exec = getGoal >>= llvc 

llvc :: FileGoal -> IO () 
llvc (f, g) = do 
  p     <- parseFile f 
  let gs = filterGoals g (vcs p)  
  forM_ gs (checkVC f)

filterGoals :: Goal -> [(Text, VC)] -> [(Text, VC)]
filterGoals None      _   = [] 
filterGoals All       xs = xs 
filterGoals (Some fs) xs = filter ((`elem` fs) . fst) xs 

checkVC :: FilePath -> (Text, VC) -> IO () 
checkVC f (fn, vc) = do 
  let smtF = f <.> tail fn <.> "smt2"
  -- let logF = f <.> "log"
  let cmd  = "z3 " ++ smtF 
  -- putStrLn $ "** Generate VC for " ++ fn
  writeQuery smtF vc 
  -- putStrLn $ "** Check VC for " ++ fn
  _ <- Utils.executeShellCommand Nothing cmd 100  
  hFlush stdout
  return ()

esHandle :: Handle -> IO a -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF

verify :: FilePath -> IO ()
verify f = do 
  putStrLn ("LLVC: checking " ++ show f) 
  return ()

----

type FileGoal = (FilePath, Goal) 

getGoal :: IO FileGoal 
getGoal = argsGoal <$> getArgs

argsGoal :: [String] -> FileGoal 
argsGoal (f:rest) = (f, goal rest) 
argsGoal _        = error "usage: 'llvc FILE {*, function-name}'" 

goal :: [String] -> Goal 
goal []      = None 
goal ("*":_) = All 
goal fs      = Some fs 

data Goal 
  = Some [Text]   -- ^ Check a single function's VC
  | All           -- ^ Check all  functions' VC
  | None          -- ^ Don't check, just generate VCs 
  deriving (Eq, Show)
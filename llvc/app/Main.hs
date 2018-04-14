module Main where

import qualified Data.List as L
import           Control.Exception
import           System.Environment 
import           System.FilePath 
import           System.Exit
import           Language.LLVC.UX 
import           Language.LLVC.Parse 
import           Language.LLVC.Verify 
import           Language.LLVC.Smt 
import qualified Language.LLVC.Utils as Utils 

-- import System.Process (runCommand) 
-- import Control.Monad (forM_) 
-- import System.IO 

main :: IO ()
main = (getGoal >>= llvc)
          `catch` 
             esHandle Utils.Crash exitFailure

 

llvc :: FileGoal -> IO () 
llvc (f, g) = do 
  putStrLn $ "\nllvc: checking " ++ show f 
  p       <- parseFile f 
  let gs   = filterGoals g (vcs p)  
  putStrLn $ "\nGoals: " ++ L.intercalate ", " (fst <$> gs) ++ "\n" 
  errs    <- concat <$> mapM (checkVC f) gs 
  case errs of 
    [] -> esHandle Utils.Safe   exitSuccess [] 
    _  -> esHandle Utils.Unsafe exitFailure errs

filterGoals :: Goal -> [(Text, VC)] -> [(Text, VC)]
filterGoals None      _   = [] 
filterGoals All       xs = xs 
filterGoals (Some fs) xs = filter ((`elem` fs) . fst) xs 

checkVC :: FilePath -> (Text, VC) -> IO [UserError] 
checkVC f (fn, vc) = do 
  let smtF = f <.> tail fn <.> "smt2"
  runQuery smtF vc

esHandle :: Utils.ExitStatus -> IO a -> [UserError] -> IO a
esHandle status exitF es = Utils.exitStatus status >> renderErrors es >>= putStrLn >> exitF

----

type FileGoal = (FilePath, Goal) 

getGoal :: IO FileGoal 
getGoal = argsGoal <$> getArgs

argsGoal :: [String] -> FileGoal 
argsGoal (f:rest) = (f, goal rest) 
argsGoal _        = error "usage: 'llvc FILE [function-name]'" 

goal :: [String] -> Goal 
goal []      = All 
goal fs      = Some fs 

data Goal 
  = Some [Text]   -- ^ Check a single function's VC
  | All           -- ^ Check all  functions' VC
  | None          -- ^ Don't check, just generate VCs 
  deriving (Eq, Show)
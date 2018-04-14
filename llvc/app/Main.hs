module Main where

-- import qualified Data.List as L
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
  putStrLn "" 
  p       <- parseFile f 
  let gs   = filterGoals g (vcs p)  
  errs    <- concat <$> mapM (checkVC f) gs 
  case errs of 
    [] -> esHandle Utils.Safe   exitSuccess [] 
    _  -> esHandle Utils.Unsafe exitFailure errs

checkVC :: FilePath -> (Text, VC) -> IO [UserError] 
checkVC f (fn, vc) = do 
  putStrLn $ "llvc checking: " ++ fn
  let smtF = f <.> tail fn <.> "smt2"
  runQuery smtF vc

esHandle :: Utils.ExitStatus -> IO a -> [UserError] -> IO a
esHandle status exitF es = Utils.exitStatus status >> renderErrors es >>= putStrLn >> exitF

----

type FileGoal = (FilePath, Goal) 

filterGoals :: Goal -> [(Text, VC)] -> [(Text, VC)]
filterGoals All       xs = xs
filterGoals (Some fs) xs = filter ((`elem` fs) . fst) xs 

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
  deriving (Eq, Show)
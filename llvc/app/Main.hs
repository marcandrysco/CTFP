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
exec = getArgs >>= mapM_ llvc 

llvc :: FilePath -> IO () 
llvc f = do 
  p  <- parseFile f 
  forM_ (vcs p) (checkVC f)

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


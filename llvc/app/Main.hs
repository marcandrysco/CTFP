module Main where

import Control.Exception
import System.Environment 
import System.FilePath 
import System.Exit
import System.IO                        
import Language.LLVC.Parse 
import Language.LLVC.UX 
import Language.LLVC.Verify 
import Language.LLVC.Smt 

main :: IO ()
main = exec `catch` esHandle stderr exitFailure

exec :: IO ()
exec = getArgs >>= mapM_ llvc 

llvc :: FilePath -> IO () 
llvc f = do 
  p <- parseFile f 
  writeQuery (f </> ".smt2") (vc p) 

esHandle :: Handle -> IO a -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF

verify :: FilePath -> IO ()
verify f = do 
  putStrLn ("LLVC: checking " ++ show f) 
  return ()


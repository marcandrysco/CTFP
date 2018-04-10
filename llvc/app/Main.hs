module Main where

import Control.Exception
import System.Environment 
import System.Exit
import System.IO                        
import Language.LLVC.Parse 
import Language.LLVC.UX 
-- import Language.LLVC.Verify 

main :: IO ()
main = exec `catch` esHandle stderr exitFailure

exec :: IO ()
exec = getArgs >>= mapM_ llvc 

llvc :: FilePath -> IO () 
llvc f = parseFile f >>= putStrLn . pprint 

esHandle :: Handle -> IO a -> [UserError] -> IO a
esHandle h exitF es = renderErrors es >>= hPutStrLn h >> exitF

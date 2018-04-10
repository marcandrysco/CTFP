module Main where

import Language.LLVC.Parse 
import Language.LLVC.Verify 
import System.Environment 

main :: IO ()
main = getArgs >>= mapM_ llvc 

llvc :: FilePath -> IO () 
llvc f = parseFile f >>= print 
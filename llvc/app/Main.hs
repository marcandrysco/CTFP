module Main where

import Language.LLVC.Verify 
import System.Environment 

main :: IO ()
main = do 
  args <- getArgs
  mapM_ verify args
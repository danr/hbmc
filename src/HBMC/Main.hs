module Main where

import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Parser

import Tip.HaskellFrontend

import Tip.Core

import HBMC.Surgery
import HBMC.Merge
import HBMC.Identifiers

import System.Environment

main :: IO ()
main = do
    f:es <- getArgs
    s <- readFile f
    thy <- case parse s of
      Left s     -> do putStrLn s
                       renameTheory <$> readHaskellFile (defaultParams f)
      Right thy0 -> return (renameTheory thy0)

    -- putStrLn $ ppRender thy

    -- putStrLn "matchPoints:"

    putStrLn $ unlines
      [ ppRender (func_body fn) ++ ":\n" ++
        ppRender (view (mapInit (fmap (\(g,es) -> (Gbl g :@: es)))
                                (findPoints (func_body fn)))) ++ "\n"
      | fn <- thy_funcs thy
      ]


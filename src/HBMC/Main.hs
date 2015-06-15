module Main where

import Tip.Pretty
import Tip.Pretty.SMT ()

import Tip.HaskellFrontend

import Tip.Core

import HBMC.Surgery
import HBMC.Merge
import HBMC.Identifiers

import System.Environment

main :: IO ()
main = do
    f:es <- getArgs
    thy <- either error renameTheory <$> readHaskellOrTipFile f defaultParams

    -- putStrLn $ ppRender thy

    -- putStrLn "matchPoints:"

    putStrLn $ unlines
      [ ppRender (func_body fn) ++ ":\n" ++
        ppRender (viewAOT (mapInit (\(g,es) -> (Gbl g :@: es))
                                   (findPoints (func_body fn)))) ++ "\n"
      | fn <- thy_funcs thy
      ]


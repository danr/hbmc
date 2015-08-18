module Main where

import Tip.Pretty
import Tip.Pretty.SMT ()

import Tip.HaskellFrontend

import Tip.Core

import Tip.Fresh

import Tip.Utils.Rename

import Tip.Scope

import HBMC.Merge
import HBMC.Identifiers

import System.Environment

import Data.List

main :: IO ()
main = do
    f:es <- getArgs
    thy <- either error renameTheory <$> readHaskellOrTipFile f defaultParams

    -- putStrLn $ ppRender thy

    -- putStrLn "matchPoints:"

    let ren = renameWith (disambig varStr)

    putStrLn $ unlines
      [ ppRender (ren e) ++ ":\n" ++
        intercalate ",\n"
          (map (ppRender . ren)
            (freshPass (hoistAllTrace (scope thy)) e))
      | fn <- thy_funcs thy
      , let e = func_body fn
      ]


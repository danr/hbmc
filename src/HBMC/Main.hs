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

import HBMC.Data
import HBMC.Projections
import HBMC.Bool

import HBMC.ToSimple

import Tip.Passes

import System.Environment

import Data.List

main :: IO ()
main = do
    f:es <- getArgs
    thy0 <- either error renameTheory <$> readHaskellOrTipFile f defaultParams

    let [thy1] =
          map (addMaybeToTheory . addBoolToTheory) $
            freshPass
              (runPasses
                [ SimplifyAggressively
                , RemoveNewtype
                , UncurryTheory
                , SimplifyGently
                , BoolOpToIf
                , CommuteMatch
                , SimplifyGently
                , RemoveAliases, CollapseEqual
                , SimplifyGently
                , CSEMatch
                -- , EliminateDeadCode
                ]) thy0

    let (dis,_) = unzip (map dataInfo (thy_datatypes thy1))
        di      = concat dis

    let thy = freshPass (projectPatterns di) thy1

    -- putStrLn $ ppRender thy

    let ren = renameWith (disambig varStr)

    putStrLn $ unlines
      [ ppRender (ren e) ++ ":\n" ++
        intercalate ",\n" (map (ppRender . ren) es) ++ "\n" ++
        ppRender (ren s)
      | fn <- thy_funcs thy
      , let e = func_body fn
      , let es = freshPass (mergeTrace (scope thy)) e
      , let s = freshPass toExpr (last es)
      ]


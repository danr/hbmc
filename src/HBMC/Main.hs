module Main where

import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Pretty.Haskell

import Tip.HaskellFrontend
import Tip.Haskell.Rename
import Tip.Haskell.Repr as H

import Tip.Core

import Tip.Fresh

import Tip.Utils.Rename

import Tip.Scope

import HBMC.Merge
import HBMC.Identifiers

import HBMC.Data
import HBMC.Projections
import HBMC.Bool

import HBMC.Monadic

import HBMC.ToSimple

import Tip.Passes

import System.Environment

import Data.List

import Control.Monad

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
      [ "\n================\n" ++ ppRender (ren e)
        ++ ":\n=>\n"
        ++ intercalate ",\n=>\n" (map (ppRender . ren) es)
        ++ "\n=>\n" ++ ppRender (ren s)
        ++ "\n=>\n" ++ ppRender (fst $ renameDecls (H.Decls [H.TH (fmap toHsId m)]))
      | fn <- thy_funcs thy
      , let e = func_body fn
      , let es = freshPass (mergeTrace (scope thy) <=< toExpr) e
      , let s = freshPass toExpr (last es)
      , let m = freshPass (\ e' -> do r <- freshNamed "r"; trExpr e' r) s
      ]


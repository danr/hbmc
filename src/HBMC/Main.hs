module Main where

import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Pretty.Haskell

import Tip.HaskellFrontend
import Tip.Haskell.Rename
import Tip.Haskell.Translate (addImports,HsId)
import Tip.Haskell.Repr as H

import Tip.Core

import Tip.Fresh

import Tip.Utils.Rename

import Tip.Scope

import HBMC.Merge
import HBMC.Identifiers
import HBMC.Haskell

import HBMC.Data
import HBMC.Projections
import HBMC.Bool

import HBMC.Monadic hiding (Var)

import HBMC.ToSimple

import HBMC.Live

import Tip.Passes

import System.Environment

import Data.List
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.Writer

import System.FilePath
import System.Directory
import System.IO.Temp
import System.Process

import Text.Show.Pretty (ppShow)

type Translated = ([Datatype Var],[Func Var],[Prop Var])

translate :: Theory Var -> WriterT [String] Fresh Translated
translate thy0 =
  do [thy1] <-
        map addBoolToTheory <$> lift
            (runPasses
              [ SimplifyAggressively
              , RemoveNewtype
              , UncurryTheory
              , SimplifyGently
              , IfToBoolOp
              , AddMatch
              , SimplifyGently
              , RemoveAliases, CollapseEqual
              , BoolOpToIf
              , CommuteMatch
              , SimplifyGently
              , BoolOpToIf
              , CommuteMatch
              , CSEMatch
              , TypeSkolemConjecture
              , EliminateDeadCode
              ] thy0)

     thy2 <- lift (monomorphise False thy1)

     thy <- lift $ do let (dis,_) = unzip (map dataInfo (thy_datatypes thy2))
                      projectPatterns (concat dis) thy2

     fn_decls <- sequence
         [ do let e = func_body fn
              -- es <- lift $ sequence [ toExpr e ]
              es <- lift $ mergeTrace (scope thy) e
              tell (ppRender fn:map (ppRender . ren) (e:es))
              lift (trFunction fn{ func_body = last es })
         | fn <- thy_funcs thy
         ]

     props <- lift $ sequence [ trFormula prop | prop <- thy_asserts thy ]

     let thy' = addMaybesToTheory
                  (concatMap F.toList fn_decls ++ concatMap F.toList props)
                  thy

     tell [ppShow (thy_datatypes thy')]
     tell (map ppShow fn_decls)
     tell [ppShow props]

     return (thy_datatypes thy', fn_decls, props)

runLive :: Translated -> IO ()
runLive (ds,fs,p:_) = liveProp Verbose static (fmap pp_var p)
  where
  pp_var = PPVar

  lkup_data = dataDescs (map (fmap pp_var) ds)
  static    = liveFuncs lkup_data (map (fmap pp_var) fs)

compile :: Translated -> Fresh String
compile (ds,fs,props) =
 do let main_decls =
           [ H.funDecl (Var "main") [] (trProp Verbose p) | p <- props ]

    let fn_decls = [ trFunc f | f <- fs ]

    let rec_dts = recursiveDatatypes ds

    dt_decls <- mapM (trDatatype rec_dts False) ds

    let decls = concat dt_decls ++ fn_decls ++ take 1 main_decls

    let Decls ds = addImports $ fst $ renameDecls $ fmap toHsId (Decls decls)

    let langs = map LANGUAGE ["ScopedTypeVariables", "TypeFamilies", "FlexibleInstances",
                              "MultiParamTypeClasses", "GeneralizedNewtypeDeriving"]

    return (ppRender (Decls (langs ++ Module "Main" : ds)))

ren = renameWith (disambig varStr)

data Target = Live | Compile

main :: IO ()
main = do
    f:es <- getArgs
    thy0 <- either error renameTheory <$> readHaskellOrTipFile f defaultParams

    let target = Compile

    let h :: Translated -> Fresh (IO ())
        h tr = case target of
                 Live    -> return (runLive tr)
                 Compile -> do c <- compile tr
                               return $
                                 do writeFile "Tmp.hs" c
                                    rawSystem "ghc" ["Tmp.hs"]
                                    rawSystem "./Tmp" []
                                    return ()

    let (m,dbg) = freshPass (runWriterT . (lift . h <=< translate)) thy0

    putStrLn (unlines dbg)

    m


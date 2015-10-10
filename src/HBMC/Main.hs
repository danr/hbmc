{-# LANGUAGE RecordWildCards #-}
module Main where

import qualified HBMC.Params as Params
import HBMC.Params (Params,getParams)

import Tip.Pretty
import Tip.Pretty.SMT ()

import qualified Tip.HaskellFrontend as Tip
import Tip.HaskellFrontend hiding (Params)
import Tip.Haskell.Rename
import Tip.Haskell.Translate (addImports,HsId)

import Tip.Core
import Tip.Utils

import Tip.Fresh

import Tip.Utils.Rename

import Tip.Scope

import HBMC.Merge
import HBMC.Identifiers

import HBMC.Data
import HBMC.Projections

import HBMC.Monadic hiding (Var)

import HBMC.ToSimple

import HBMC.Live

import Tip.Passes
import Tip.Pass.Booleans

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

translate :: Params -> Theory Var -> WriterT [String] Fresh Translated
translate params thy0 =
  do [thy1] <-
        map (skolemTypesToNat . removeBuiltinBoolWith boolNames) <$> lift
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

     let fn_comps = map (fmap func_name) (components defines uses (thy_funcs thy))

     let ci | Params.insist_isnt params = flip lookup
              [ (c,all_cons \\ [c])
              | Datatype tc [] cons <- thy_datatypes thy
              , not (isMaybeTC tc)
              , let all_cons = map con_name cons
              , c <- map con_name cons
              ]
            | otherwise = const Nothing

     fn_decls <- sequence
         [ do let e = func_body fn
              es <- lift $
                if Params.merge params
                    then mergeTrace (scope thy) e
                    else sequence [toExpr e]
              tell (ppRender fn:map (ppRender . ren) (e:es))
              lift (trFunction params ci fn_comps fn{ func_body = last es })
         | fn <- thy_funcs thy
         ]

     props <- lift $ sequence [ trFormula ci prop | prop <- thy_asserts thy ]

     let thy' = addMaybesToTheory
                  (concatMap F.toList fn_decls ++ concatMap F.toList props)
                  thy

     tell [ppShow (thy_datatypes thy')]
     tell (map ppShow fn_decls)
     tell [ppShow props]

     return (thy_datatypes thy', fn_decls, props)

runLive :: Params -> Translated -> IO ()
runLive p (_,_,[])       = error "Needs at least one property!"
runLive p (ds,fs,prop:_) = liveProp p static (fmap pp_var prop)
  where
  pp_var = PPVar

  lkup_data = dataDescs (Params.delay_all_datatypes p) (map (fmap pp_var) ds)
  static    = liveFuncs p lkup_data (map (fmap pp_var) fs)

ren = renameWith (disambig varStr)

main :: IO ()
main = do
    params <- getParams
    thy0 <- either error renameTheory <$>
      readHaskellOrTipFile
        (Params.file params)
        Tip.defaultParams{ Tip.prop_names = Params.prop_names params }

    let (m,dbg) = freshPass (runWriterT . (lift . return . runLive params <=< translate params)) thy0

    when (Params.debug params) (putStrLn (unlines dbg))

    m


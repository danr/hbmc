{-# LANGUAGE RecordWildCards #-}
module Main where

import qualified HBMC.Params as Params
import HBMC.Params (Params,getParams)

import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Pretty.Haskell

import qualified Tip.HaskellFrontend as Tip
import Tip.HaskellFrontend hiding (Params)
import Tip.Haskell.Rename
import Tip.Haskell.Translate (addImports,HsId)
import Tip.Haskell.Repr as H

import Tip.Core
import Tip.Utils

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

translate :: Params -> Theory Var -> WriterT [String] Fresh Translated
translate params thy0 =
  do [thy1] <-
        map (skolemTypesToNat . addBoolToTheory) <$> lift
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

     fn_decls <- sequence
         [ do let e = func_body fn
              es <- lift $
                if Params.merge params
                    then mergeTrace (scope thy) e
                    else sequence [toExpr e]
              tell (ppRender fn:map (ppRender . ren) (e:es))
              lift (trFunction params fn_comps fn{ func_body = last es })
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

runLive :: Params -> Translated -> IO ()
runLive p (_,_,[])       = error "Needs at least one property!"
runLive p (ds,fs,prop:_) = liveProp p static (fmap pp_var prop)
  where
  pp_var = PPVar

  lkup_data = dataDescs (Params.delay_all_datatypes p) (map (fmap pp_var) ds)
  static    = liveFuncs lkup_data (map (fmap pp_var) fs)

compile :: Params -> Translated -> Fresh String
compile p (ds,fs,props) =
 do let main_decls =
           [ H.funDecl (Var "main") [] (trProp p prop) | prop <- props ]

    let fn_decls = [ trFunc f | f <- fs ]

    let rec_dts = recursiveDatatypes ds

    dt_decls <- mapM (trDatatype rec_dts (Params.delay_all_datatypes p)) ds

    let decls = concat dt_decls ++ fn_decls ++ take 1 main_decls

    let Decls ds = addImports $ fst $ renameDecls $ fmap toHsId (Decls decls)

    let langs = map LANGUAGE ["ScopedTypeVariables", "TypeFamilies", "FlexibleInstances",
                              "MultiParamTypeClasses", "GeneralizedNewtypeDeriving"]

    return (ppRender (Decls (langs ++ Module "Main" : ds)))

ren = renameWith (disambig varStr)

data Target = Live | Compile

main :: IO ()
main = do
    params <- getParams
    thy0 <- either error renameTheory <$>
      readHaskellOrTipFile
        (Params.file params)
        Tip.defaultParams{ Tip.prop_names = Params.prop_names params }

    let h :: Translated -> Fresh (IO ())
        h tr = case Params.compile params of
                 False -> return (runLive params tr)
                 True  -> do c <- compile params tr
                             return $
                               do writeFile "Tmp.hs" c
                                  rawSystem "ghc" ["Tmp.hs"]
                                  rawSystem "./Tmp" []
                                  return ()

    let (m,dbg) = freshPass (runWriterT . (lift . h <=< translate params)) thy0

    when (Params.debug params) (putStrLn (unlines dbg))

    m


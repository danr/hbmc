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

import Language.Haskell.Interpreter
import System.FilePath
import System.Directory
import System.IO.Temp

import Text.Show.Pretty (ppShow)

--translate :: Theory Var -> WriterT [String] Fresh (Decls (HsId String))
translate :: Theory Var -> WriterT [String] Fresh (IO ())
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
              {- trFunc <$> -}
              lift (trFunction fn{ func_body = last es })
         | fn <- thy_funcs thy
         ]

     main_decls@(main_prop:_) <- lift $ sequence
         [ {- H.funDecl (Var "main") [] . trProp Verbose <$> -} trFormula prop
         | prop <- thy_asserts thy
         ]

     let thy' = addMaybesToTheory
                  (concatMap F.toList fn_decls ++ concatMap F.toList main_decls)
                  thy

     tell [ppShow (thy_datatypes thy')]
     tell (map ppShow fn_decls)
     tell [ppShow main_decls]

     let pp_var = PPVar

     let lkup_data = dataDescs (map (fmap pp_var) (thy_datatypes thy'))
         static    = liveFuncs lkup_data (map (fmap pp_var) fn_decls)

     return (liveProp Verbose static (fmap pp_var main_prop))

{-
    let rec_dts = recursiveDatatypes (thy_datatypes thy)

    tell ("rec_dts:":map varStr rec_dts)

    dt_decls <- lift $ mapM (trDatatype rec_dts False) (thy_datatypes thy)

    let decls = concat dt_decls ++ fn_decls ++ main_decls

    let Decls ds = addImports $ fst $ renameDecls $ fmap toHsId (Decls decls)

    let langs = map LANGUAGE ["ScopedTypeVariables", "TypeFamilies", "FlexibleInstances",
                              "MultiParamTypeClasses", "GeneralizedNewtypeDeriving"]

    return (Decls (langs ++ Module "Main" : ds))
    -}

ren = renameWith (disambig varStr)

main :: IO ()
main = do
    f:es <- getArgs
    thy0 <- either error renameTheory <$> readHaskellOrTipFile f defaultParams
    let (m,dbg) = freshPass (runWriterT . translate) thy0
    -- let mod_str = unlines (["{-"] ++ dbg ++ ["-}"] ++ [ppRender ds])
    -- putStrLn mod
    -- m <- runMod mod_str
    -- m
    putStrLn (unlines dbg)
    m

{-
runMod :: String -> IO (IO ())
runMod mod_str =
  fmap (either (error . showError) id) $
    do dir <- getCurrentDirectory -- createTempDirectory "." "tmp"
       putStrLn dir
       let a_file = dir </> "A" <.> "hs"
       writeFile a_file mod_str
       setCurrentDirectory dir
       runInterpreter $
         do set [searchPath := ["../lib"]]
            loadModules ["A"]
            setImports ["Main","LibHBMC","Prelude"]
            interpret "main" (undefined :: IO ())

showError :: InterpreterError -> String
showError (WontCompile ghcerrs) = unlines (map errMsg ghcerrs)
showError (GhcException e) = e
showError e = show e
-}

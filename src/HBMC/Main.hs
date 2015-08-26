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

import Tip.Passes

import System.Environment

import Data.List

import Control.Monad
import Control.Monad.Writer

import Language.Haskell.Interpreter
import System.FilePath
import System.Directory
import System.IO.Temp

translate :: Theory Var -> WriterT [String] Fresh (Decls (HsId String))
translate thy0 = do
    [thy1] <-
        map (addMaybeToTheory . addBoolToTheory) <$> lift
            (runPasses
              [ SimplifyAggressively
              , RemoveNewtype
              , UncurryTheory
              , SimplifyGently
              , AddMatch
              , BoolOpToIf
              , CommuteMatch
              , SimplifyGently
              , RemoveAliases, CollapseEqual
              , SimplifyGently
              , CSEMatch
              -- , EliminateDeadCode
              ] thy0)

    let (dis,_) = unzip (map dataInfo (thy_datatypes thy1))
        di      = concat dis

    thy <- lift (projectPatterns di thy1)

    fn_decls <- sequence
        [ do let e = func_body fn
             es <- lift $ mergeTrace (scope thy) e
             tell ("":map (ppRender . ren) es)
             trFunc <$> lift (trFunction fn{ func_body = last es })
        | fn <- thy_funcs thy
        ]

    main_decls <- lift $ sequence
        [ H.funDecl (Var "main") [] . trProp Verbose <$> trFormula prop
        | prop <- thy_asserts thy
        ]

    dt_decls <- lift $ mapM (trDatatype False) (thy_datatypes thy)

    let decls = concat dt_decls ++ fn_decls ++ main_decls

    let Decls ds = addImports $ fst $ renameDecls $ fmap toHsId (Decls decls)

    let langs = map LANGUAGE ["ScopedTypeVariables", "TypeFamilies", "FlexibleInstances",
                              "MultiParamTypeClasses", "GeneralizedNewtypeDeriving"]

    return (Decls (langs ++ Module "Main" : ds))

ren = renameWith (disambig varStr)

main :: IO ()
main = do
    f:es <- getArgs
    thy0 <- either error renameTheory <$> readHaskellOrTipFile f defaultParams
    let (ds,dbg) = freshPass (runWriterT . translate) thy0
    let mod_str = unlines (["{-"] ++ dbg ++ ["-}"] ++ [ppRender ds])
    -- putStrLn mod
    m <- runMod mod_str
    m

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

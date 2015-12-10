{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

import HBMC.Object
import HBMC.Program
import HBMC.MakeProgram

import HBMC.ToSimple

import qualified Data.Map as M

-- import HBMC.Monadic hiding (Var)
-- import HBMC.Live

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

deriving instance Names a => Names (PPVar a)

data Translated a = Translated [PreFunction a] [Prop a]
  deriving (Show, Functor)

translate :: Params -> Theory Var -> WriterT [String] Fresh (Translated Var)
translate params thy0 =
  do [thy1] <-
        map (removeBuiltinBoolWith boolNames) <$> lift
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
              , SortsToNat
              , EliminateDeadCode
              ] thy0)

     thy2 <- lift (monomorphise False thy1)

     (di,thy) <- lift $ do let di = dataInfo (thy_datatypes thy2)
                           (,) di <$> projectPatterns di thy2

     let fn_comps = map (fmap func_name) (components defines uses (thy_funcs thy))

     fn_decls <- sequence
         [ do let e = func_body fn
              es <- lift $
                if Params.merge params
                    then mergeTrace (scope thy) e
                    else sequence [toExpr e]
              tell (ppRender fn:map (ppRender . ren) (e:es))
              lift (trFunction params di fn_comps fn{ func_body = last es })
         | fn <- thy_funcs thy
         ]

     props <- lift $ sequence [ trFormula di prop | prop <- thy_asserts thy ]

{-
     let thy' = addMaybesToTheory
                  (concatMap F.toList fn_decls ++ concatMap F.toList props)
                  thy
                  -}

     -- This maybe-hack won't me needed with LetApp or dynamic function
     -- call horizon merging

     tell [ppShow (thy_datatypes thy)]
     tell (map ppShow fn_decls)
     tell [ppShow props]

     return (Translated fn_decls props)

runLive :: Params -> Translated (PPVar Var) -> IO ()
runLive p (Translated _    [])       = error "Needs at least one property!"
runLive p (Translated prog (prop:_)) = run (evalProp (M.fromList prog) prop)

ren = renameWith (disambig varStr)

main :: IO ()
main = do
    params <- getParams
    thy0 <- either error renameTheory <$>
      readHaskellOrTipFile
        (Params.file params)
        Tip.defaultParams{ Tip.prop_names = Params.prop_names params }

    let (m,dbg) = freshPass (runWriterT . (lift . return . runLive params <=< fmap (fmap PPVar) . translate params)) thy0

    when (Params.debug params) (putStrLn (unlines dbg))

    m


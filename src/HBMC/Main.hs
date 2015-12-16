{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main where

import qualified HBMC.Params as Params
import HBMC.Params (Params,theParams)

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


import Tip.Passes
import Tip.Pass.Booleans

import System.Environment

import Data.List
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.Writer
import Control.Applicative( (<$>) )

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
            (flip runPasses thy0 $
              [ SimplifyAggressively
              , RemoveNewtype
              , UncurryTheory
              , SimplifyGently
              , IfToBoolOp
              , AddMatch
              , SimplifyGently ]
              ++ (if Params.top_level_bool_ops params then
                   [ RemoveAliases
                   , SimplifyGently
                   , BoolOpLift
                   , CollapseEqual
                   , BoolOpToIf
                   ]
                 else
                   [ RemoveAliases, CollapseEqual
                   , SimplifyGently
                   , BoolOpToIf
                   , CommuteMatch
                   , SimplifyGently
                   , BoolOpToIf
                   ])
              ++
              [ CommuteMatch
              , CSEMatch
              , TypeSkolemConjecture
              , SortsToNat
              , EliminateDeadCode
              ])

     thy2 <- lift (monomorphise False thy1)

     (di,thy) <- lift $ do let di = dataInfo (thy_datatypes thy2)
                           (,) di <$> projectPatterns di thy2

     merged_fns <-
       sequence
         [ do let e = func_body fn
              e' <- if Params.merge params
                      then lift $ merge (scope thy) e
                      else return e
              tell (ppRender fn:map (ppRender . ren) [e,e'])
              return fn{func_body=e'}
         | fn <- thy_funcs thy
         ]

     let fn_comps = components defines uses merged_fns

     let fns_with_laters =
           concat
             [ case c of
                 Rec fs   -> insertLaters params fs
                 NonRec f -> [f]
             | c <- fn_comps
             ]


     fn_decls <-
       lift $ sequence
         [ trFunction params di (map (fmap func_name) fn_comps) fn
         | fn <- fns_with_laters
         ]

     props <- lift $ sequence [ trFormula di prop | prop <- thy_asserts thy ]

     tell (map ppShow fn_decls)
     tell [ppShow props]

     return (Translated fn_decls props)

runLive :: Params -> Translated (PPVar Var) -> IO ()
runLive p (Translated _    [])       = error "Needs at least one property!"
runLive p (Translated prog (prop:_)) = run p (evalProp (M.fromList prog) prop)

ren = renameWith (disambig varStr)

main :: IO ()
main = do
    params <- theParams
    thy0 <- either error renameTheory <$>
      readHaskellOrTipFile
        (Params.file params)
        Tip.defaultParams{ Tip.prop_names = Params.prop_names params }

    let (m,dbg) = freshPass (runWriterT . (lift . return . runLive params <=< fmap (fmap PPVar) . translate params)) thy0

    when (Params.debug params) (putStrLn (unlines dbg))

    m


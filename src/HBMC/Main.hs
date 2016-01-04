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

import Tip.Core as Tip
import Tip.Utils

import Tip.Fresh

import Tip.Utils.Rename

import Tip.Scope

import HBMC.Merge
import HBMC.Identifiers

import HBMC.Data
import HBMC.Projections

import HBMC.Object  as O
import HBMC.Program
import HBMC.Eval    as E
import HBMC.MakeProgram

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

deriving instance (PrettyVar a,Names a) => Names (PPVar a)

data Translated a = Translated
  { tr_thy     :: Theory a
    -- ^ the final theory is returned so the result can be
    --   (non-symbolically) evaluated and checked wrt to it
  , tr_pre_fns :: [PreFunction a]
    -- ^ functions for symbolic evaluation
  , tr_props   :: [(Tip.Expr a,Prop a)]
    -- ^ symbolic properties matched with their original Tip formula (for evaluation)
  }
  deriving (Show, Functor)

translate :: Params -> Theory Var -> WriterT [String] Fresh (Translated Var)
translate params thy0 =
  do [thy1] <- lift (flip runPasses thy0 $
              [ SimplifyGently
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
              , Monomorphise False
              ])

     tell [show (pp thy1)]

     let thy2 = removeBuiltinBoolWith boolNames thy1

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

     props <- lift $ sequence
                       [ (,) (fm_body prop_orig) <$> trFormula di prop
                       | (prop_orig,prop) <- thy_asserts thy1 `zip` thy_asserts thy
                       ]

     tell (map ppShow fn_decls)
     tell [ppShow (map snd props)]

     return (Translated thy1 fn_decls props)

runLive :: Params -> Translated (PPVar Var) -> IO ()
runLive p (Translated thy _    [])           = error "Needs at least one property!"
runLive p (Translated thy prog ((e,prop):_)) =
  do m <- run p (evalProp (M.fromList prog) prop)
     case m of
       Just v  ->
         case E.evalExpr thy (M.map trVal v) (dig e) of
           Right (E.Lit (Bool True))  -> error "Incorrect!"
           Right E.Unk                -> error "Incorrect (unk)!"
           Right (E.Lit (Bool False)) -> return ()
           Left s  -> error $ "Evaluator errored: " ++ s
           Right b -> error $ "Evaluator returned: " ++ show b
       Nothing -> return ()

  where
  trVal :: O.Val (PPVar Var) -> E.Val (PPVar Var)
  trVal (O.Cn (O.Cons n _ _) vs)
    | n == unkName     = E.Unk
    | n == O.trueName  = E.Lit (Bool True)
    | n == O.falseName = E.Lit (Bool False)
    | otherwise        = E.Con n (map trVal vs)

  dig (Quant _ Forall _ e) = dig e
  dig e = e

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


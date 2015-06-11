{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
module TipLift where

import Tip.Core
import Tip.Pretty
import Tip.Pretty.SMT hiding (apply)
import Tip.Fresh
import Tip.Simplify

import Data.List

import Data.Generics.Geniplate

import Control.Applicative

-- Lifting

class Name a => Call a where
  labelName  :: a
  skipName   :: a
  callName   :: a
  cancelName :: a

type Label = Expr

labels :: Call a => Expr a -> [Label a]
labels e = nub [ lbl | Gbl (Global f _ _) :@: [lbl,_] <- universeBi e, f == labelName ]

labelled :: Call a => Expr a -> Label a -> [Expr a]
e `labelled` l = [ el | Gbl (Global f _ _) :@: [lbl,el] <- universeBi e, f == labelName, l == lbl ]

antiMatch :: Call a => [Expr a] -> Fresh ((Local a,Expr a),Expr a)
antiMatch xs =
  do let (Local f ft:_fs,argss) =
           unzip
             [ (Local fx (exprType x),args)
             | x <- xs, let Gbl (Global fx _ _) :@: args = x
             ]

     g <- refresh f
     let lg = Local g ft

     (args,vars) <-
        unzip <$>
        sequence
          [ case column of
              e:es | all (e==) es -> do y <- fresh; return (e,Left (Local y (exprType e)))
              es                  -> do x <- fresh
                                        let lx = Local x (exprType (head es))
                                        return (Lcl lx,Right lx)
          | column <- transpose argss
          ]

     let rights = [ x | Right x <- vars ]

     return
       ( (lg, Lam rights (Gbl (fun f) :@: args))
       , Lam (map (either id id) vars)
             (Gbl (Global callName (PolyType [] [] ft) [])
               :@: (Lcl lg:map Lcl rights))
       )

liftCall :: Call a => Label a -> Expr a -> Fresh (Local a,Expr a,Expr a)
liftCall l e =
  do ((g,g_def),f_repl) <- antiMatch (e `labelled` l)
     e' <- flip transformBiM e $
             \ e0 -> case e0 of
                       Gbl (Global f _ _) :@: [lbl,_ :@: args]
                         | f == labelName
                         , l == lbl
                         -> do f_repl' <- freshen f_repl
                               return (f_repl' `apply` args)
                       Gbl (Global f _ _) :@: [lbl,rest]
                         | f == skipName
                         , l == lbl
                         -> return (Gbl (fun cancelName) :@: [Lcl g,rest])
                       _ -> return e0
     return (g,g_def,e')

insertSkips :: Call a => Label a -> Expr a -> Expr a
insertSkips l e0 =
  case e0 of
    Let x b e -> Let x b (insertSkips l e)
    Match e alts -> Match e [ Case pat (insertSkips l rhs) | Case pat rhs <- alts ]
    _ | l `elem` labels e0 -> e0
      | otherwise          -> Gbl (fun skipName) :@: [l,e0]

-- Assumes a top level cascade of lets and case only, and that
-- nothing bound by a let needs to be lifted
--
-- 1) locates the lift point
-- 2) insert missing skipes
-- 3) lifts it
removeLabel :: Call a => Label a -> Expr a -> Fresh (Expr a)
removeLabel l e0 =
  case e0 of
    _ | l `notElem` labels e0 -> return e0
    Let x b e -> Let x b <$> removeLabel l e
    Match e alts
      | sum [ 1 :: Int | Case _ rhs <- alts, l `elem` labels rhs ] > 1
        -> do (g,g_def,Match e' alts') <- liftCall l (insertSkips l e0)
              return (Match (Let g g_def e') alts')
      | otherwise
        -> Match e <$> sequence [ Case pat <$> removeLabel l rhs | Case pat rhs <- alts ]
    _ -> error $ "removeLabel " ++ ppRender l ++ " on non-let, not-case: " ++ ppRender e0

removeLabels :: Call a => Expr a -> Fresh (Expr a)
removeLabels e =
  case labels e of
    l:_ -> removeLabels
              =<< simplifyExpr aggressively{touch_lets=False,remove_variable_scrutinee_in_branches=False}
                  -- the only simplification we really want to do here is beta reduction,
                  -- while not destroying the weird invariants we have.
                  -- The simplifier could instead be parameterised
                  -- on things to simplify, i.e. Let,Match,Lambda+At,Builtins, and so on...
              =<< removeLabel l e
    []  -> return e

removeLabelsFromTheory :: Call a => Theory a -> Fresh (Theory a)
removeLabelsFromTheory
  Theory{..} =
  do fns <- sequence [ do b <- removeLabels func_body
                          return Function{func_body=b,..}
                     | Function{..} <- thy_funcs
                     ]
     return Theory{thy_funcs=fns,..}

fun a = Global a noPolyType []
noPolyType = PolyType [] [] boolType


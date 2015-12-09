{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module HBMC.MakeProgram where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Tip.Core
import Tip.Fresh
import Tip.Utils

import HBMC.Identifiers hiding (Con,Proj,Var)
import HBMC.Identifiers (Var())

import HBMC.Params
import Tip.Passes
import Tip.Pass.Booleans

import Data.Generics.Geniplate

import HBMC.ToSimple
import qualified HBMC.Program as P
import HBMC.Program (Expr')

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

import qualified Data.Map as M
import Data.Map( Map )

-- the other constructors
type ConInfo a = a -> Maybe [a]

-- Simple termination check: there is some argument that always decreases
-- Not working for mutually recursive groups!
terminates :: Var          -- function name
           -> [Var]        -- arguments
           -> Expr Var -- body as a simple expression
           -> Bool
terminates _ [] _ = True
terminates f as e =
  or [ and [ chase a (es !! i)
           | Gbl (Global f' _ _) :@: es <- universeBi e
           , f == f' ]
     | (a,i) <- as `zip` [0..] ]
  where
  chase needle (Gbl (Global g _ _) :@: [Lcl (Local x _)])
    | Just{} <- unproj g
    = needle == x
  chase _ _ = False

trFunction :: Params -> ConInfo Var -> [Component Var] -> Function Var -> Fresh (Var,([Var],Expr' Var))
trFunction p ci fn_comps Function{..} =
  do r <- fresh
     let (rec,mut_rec) = case lookupComponent func_name fn_comps of
                           Just (Rec xs) -> (True,length xs > 1)
                           _             -> (False,False)
     let args = map lcl_name func_args
     let chk = strict_data_lazy_fun p || ((not (terminates func_name args func_body) || mut_rec) && postpone p)
     let mem = memo p && rec
     body <- trExpr ci func_body (Just r)

     return (func_name,(args,(if chk then Later else id) body))
                             -- TODO: memo?

trFormula :: ConInfo Var -> Formula Var -> Fresh (Prop Var)
trFormula ci fm =
  case fm of
    Formula r      _ (_:_) e -> error "trFormula, TODO: translate type variables"
    Formula Prove  i []    e -> trFormula ci (Formula Assert i [] (neg e))
    Formula Assert _ []    e ->
      do let (vs,e') = fmap neg (forallView (neg e))
         let cs      = conjuncts (ifToBoolOp e')
         let news    = [ x :<-: New True (tyConOf t) | Local x t <- vs ]
         asserts <- mapM (trToTrue ci) cs
         return (Prop (map lcl_name vs) (simpMon (news ++ concat asserts)))

trToTrue :: ConInfo Var -> Expr Var -> Fresh (Mon Var)
trToTrue ci e0 =
  case e0 of
    Builtin Equal    :@: ~[e1,e2] -> tr True  e1 e2
    Builtin Distinct :@: ~[e1,e2] -> tr False e1 e2
    _                             -> tr True  e0 (boolExpr boolNames True)
  where
  tr pol e1 e2 =
    do (lets1,s1) <- collectLets <$> toExprSimpleEnd (removeBuiltinBoolFrom boolNames (boolOpToIf e1))
       (lets2,s2) <- collectLets <$> toExprSimpleEnd (removeBuiltinBoolFrom boolNames (boolOpToIf e2))
       let equal_fn = blankGlobal
                        (api (if pol then "equalHere" else "notEqualHere"))
                        (error "trToTrue global type")
       trExpr ci (makeLets (lets1 ++ lets2) (Gbl equal_fn :@: [s1,s2])) Nothing

conjuncts :: Expr a -> [Expr a]
conjuncts e0 =
  case e0 of
    Builtin And :@: es                            -> concatMap conjuncts es
    Builtin Not :@: [Builtin Or :@: es]           -> concatMap conjuncts es
    Builtin Not :@: [Builtin Implies :@: [e1,e2]] -> concatMap conjuncts [e1,neg e2]
    _                                             -> [e0]

trExpr :: ConInfo Var -> Expr Var -> Fresh (Expr' Var)
trExpr ci e00 =
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  ([x :<-: New False (tyConOf t) | (Local x t,_) <- matches ] ++)
         <$> go (makeLets (fn_calls ++ matches) rest)
  where
  go e0 =
    case e0 of
      Let x e b -> P.Let x <$> go e <*>  go b

      {-o
      Let x (Match s brs) e ->
        (++) <$> trMatch ci s brs (Just (lcl_name x)) <*> go e

      Let x (Gbl (Global f _ _) :@: ss) e ->
        (lcl_name x :<-: Call f (map trSimple ss) :) <$> go e
      -}

      Match s brs ->
        P.Case
          <$> go s
          <*> sequence
           [ do rhs' <- go rhs
                return (k,[??],rhs')
           | Case (ConPat (Global k _ _) _ as) rhs <- brs
           ]

      Gbl (Global (SystemCon "noop" _) _ _) :@: _ -> return P.Noop

      Gbl (Global (Api "equalHere") _ _) :@: [s1,s2]    -> P.EqPrim P.EqualHere    <$> go s1 <*> go s2
      Gbl (Global (Api "notEqualHere") _ _) :@: [s1,s2] -> P.EqPrim P.NotEqualHere <$> go s1 <*> go s2

      Lcl (Local x _) -> P.Var x

      Gbl (Global k _ _) :@: [s] | Just i <- unproj k -> P.Proj i <$> go s
      Gbl (Global k (PolyType _ _ (TyCon tc _)) _) :@: ss -> P.Con tc k (map trSimple ss)
                                                             -- continue
                                                             -- here with
                                                             -- cons

      _ -> error $ "trExpr " ++ ppRender e0

trSimple :: Expr Var -> Simp Var
trSimple s =
  case s of
    _ -> error $ "trSimple, not simple: " ++ ppRender s

trCase :: ConInfo Var -> Var -> Maybe Var -> [Var] -> Case Var -> Fresh (Mon Var)
trCase ci c mr cons (Case pat rhs) =
  do body <- trExpr ci rhs mr
     return $
       case body of
         [] -> []
         _  ->
           return $
             case pat of
               Default                 -> Guard Unless [c :=? k | k <- cons] body
               ConPat (Global k _ _) _ -> Guard When   [c :=? k] body

isMatch :: Expr a -> Bool
isMatch Match{} = True
isMatch _       = False

tyConOf :: Type a -> a
tyConOf (TyCon x _) = x

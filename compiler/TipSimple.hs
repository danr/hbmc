{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module TipSimple where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Generics.Geniplate

data Let a = Apply a [Simple a]
           | Proj a Int (Simple a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Expr a
  = Simple (Simple a)
  | Let  a (Let a) (Expr a)
  | Match a (Simple a) a [Call a] [Alt a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Simple a
  = Var a
  | Con a [Simple a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Call a = Call a [a] (Expr a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Alt a = Pat a :=> Expr a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Pat a = ConPat a | Default
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

instanceTransformBi [t| forall a . (Simple a,Expr a) |]
instanceTransformBi [t| forall a . (Simple a,Simple a) |]
instanceTransformBi [t| forall a . (Simple a,Let a) |]

instanceTransformBi [t| forall a . (Let a,Expr a) |]
instanceTransformBi [t| forall a . (Let a,Let a) |]

substSimple :: TransformBi (Simple a) (f a) => (a -> Simple a) -> f a -> f a
substSimple su =
  transformBi $ \ s0 ->
    case s0 of
      Var x -> su x
      _     -> s0

substProj :: TransformBi (Let a) (f a) => (a -> Simple a) -> f a -> f a
substProj su =
  transformBi $ \ l0 ->
    case l0 of
      Proj a i (Var x) -> Proj a i (su x)
      Apply{}          -> l0

bindLets :: [(a,Let a)] -> Expr a -> Expr a
bindLets = flip (foldr (\ (x,lt) e -> Let x lt e))

instance PrettyVar a => Pretty (Expr a) where
  pp (Simple s) = pp s
  pp (Let x lt e) = sep ["let" $\ ppVar x <+> "=" $\ pp lt <> ";",pp e]
  pp (Match tc s s' calls alts) =
    ("case" <+> "{-" <+> ppVar tc <+> "-}" $\ pp s <+> "of")
      $\ (if null calls then empty else braces (vcat (punctuate ";" (map pp calls))))
      $$ vcat [ppVar s' <> "@" <> pp alt | alt <- alts]

instance PrettyVar a => Pretty (Let a) where
  pp (Apply f args) = ppVar f <+> fsep (map pp args)
  pp (Proj t i x)   = "proj" <> ppVar t <> "_" <> int i <+> pp x

instance PrettyVar a => Pretty (Simple a) where
  pp (Var a)        = ppVar a
  pp (Con k [])     = ppVar k
  pp (Con k ss)     = parens (ppVar k $\ fsep (map pp ss))

instance PrettyVar a => Pretty (Call a) where
  pp (Call f xs e) = (ppVar f $\ fsep (map ppVar xs)) $\ "=" <+> pp e

instance PrettyVar a => Pretty (Alt a) where
  pp (p :=> e) = pp p <+> "->" $\ pp e

instance PrettyVar a => Pretty (Pat a) where
  pp Default    = "_"
  pp (ConPat k) = ppVar k


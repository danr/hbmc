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
  | Match a (Simple a) [Call a] [Alt a]
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

instanceTransformBi [t| forall a . (Let a,Call a) |]
instanceTransformBi [t| forall a . (Let a,Alt a) |]

substSimple :: TransformBi (Simple a) (f a) => (a -> Simple a) -> f a -> f a
substSimple su =
  transformBi $ \ s0 ->
    case s0 of
      Var x -> su x
      _     -> s0

modLet :: TransformBi (Let a) (f a) => (Let a -> Let a) -> f a -> f a
modLet = transformBi

instance Pretty a => Pretty (Expr a) where
  pp (Simple s) = pp s
  pp (Let x lt e) = sep ["let" $\ pp x <+> "=" $\ pp lt <> ";",pp e]
  pp (Match tc s calls alts) =
    ("case" <+> "{-" <+> pp tc <+> "-}" $\ pp s <+> "of")
      $\ (if null calls then empty else braces (vcat (punctuate ";" (map pp calls))))
      $$ vcat (map pp alts)

instance Pretty a => Pretty (Let a) where
  pp (Apply f args) = pp f <+> fsep (map pp args)
  pp (Proj t i x)   = "proj" <> pp t <> "_" <> pp i <+> pp x

instance Pretty a => Pretty (Simple a) where
  pp (Var a)        = pp a
  pp (Con k [])     = pp k
  pp (Con k ss)     = parens (pp k $\ fsep (map pp ss))

instance Pretty a => Pretty (Call a) where
  pp (Call f xs e) = (pp f $\ fsep (map pp xs)) $\ "=" <+> pp e

instance Pretty a => Pretty (Alt a) where
  pp (p :=> e) = pp p <+> "->" $\ pp e

instance Pretty a => Pretty (Pat a) where
  pp Default    = "_"
  pp (ConPat k) = pp k


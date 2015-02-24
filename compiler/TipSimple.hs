{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module TipSimple where

import Text.PrettyPrint
import Tip.Pretty
import qualified Data.Foldable as F
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

tryHalf :: Expr a -> Maybe (HalfExpr a)
tryHalf e0 = case e0 of
  Match{}   -> Nothing
  Let x l e -> do HalfExpr ls e' <- tryHalf e
                  return (HalfExpr ((x,l):ls) e')
  Simple s  -> return (HalfExpr [] (half s))
 where
  half :: Simple a -> Half a
  half (Var x) = HVar x
  half (Con dc tc ss) = HCon dc tc (map half ss)

-- inlines
optHalf :: Eq a => HalfExpr a -> HalfExpr a
optHalf (HalfExpr ((x,Apply f ss):ls) h)
  | sum (map (count x . snd) ls) == 0, count x h == 1
  = optHalf (HalfExpr ls (substHalf x f ss h))
optHalf (HalfExpr (l0:ls) h)
  = let HalfExpr ls' h' = optHalf (HalfExpr ls h)
    in  HalfExpr (l0:ls') h'
optHalf he = he

substHalf :: Eq a => a -> a -> [Simple a] -> Half a -> Half a
substHalf x f args (HVar y) | x == y = HFun f args
substHalf x f args (HCon dc tc hs) = HCon dc tc (map (substHalf x f args) hs)
substHalf _ _ _    h = h

count :: (Eq a,Foldable f) => a -> f a -> Int
count x t = length [ y | y <- F.toList t, x == y ]

data HalfExpr a = HalfExpr [(a,Let a)] (Half a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Half a
  = HFun a [Simple a]
  | HCon a a [Half a]
  | HVar a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Simple a
  = Var a
  | Con a {-^ dc -} a {-^ ty con -} [Simple a]
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

instance Pretty a => Pretty (Expr a) where
  pp (Simple s) = pp s
  pp (Let x lt e) = sep ["let" $\ pp x <+> "=" $\ pp lt <> ";",pp e]
  pp (Match tc s s' calls alts) =
    ("case" <+> "{-" <+> pp tc <+> "-}" $\ pp s <+> "of")
      $\ (if null calls then empty else braces (vcat (punctuate ";" (map pp calls))))
      $$ vcat [pp s' <> "@" <> pp alt | alt <- alts]

instance Pretty a => Pretty (Let a) where
  pp (Apply f args) = pp f <+> fsep (map pp args)
  pp (Proj t i x)   = "proj" <> pp t <> "_" <> pp i <+> pp x

instance Pretty a => Pretty (Simple a) where
  pp (Var a)        = pp a
  pp (Con k _ [])     = pp k
  pp (Con k _ ss)     = parens (pp k $\ fsep (map pp ss))

instance Pretty a => Pretty (Call a) where
  pp (Call f xs e) = (pp f $\ fsep (map pp xs)) $\ "=" <+> pp e

instance Pretty a => Pretty (Alt a) where
  pp (p :=> e) = pp p <+> "->" $\ pp e

instance Pretty a => Pretty (Pat a) where
  pp Default    = "_"
  pp (ConPat k) = pp k


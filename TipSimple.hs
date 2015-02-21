{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module TipSimple where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

data Expr a
  = Simple (Simple a)
  | Let  a   a [Simple a] (Expr a)
  -- let x = f x1 .... xn in e
  | Match (Simple a) [Call a] [Alt a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Simple a
  = Var a
  | Con a [Simple a]
  | Proj a Int [Simple a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Call a = Call a [a] (Expr a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Alt a = Pat a :=> Expr a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Pat a = ConPat a | Default
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

substSimple :: (a -> Simple a) -> Simple a -> Simple a
substSimple su e =
  case e of
    Var x       -> su x
    Con x ss    -> Con x (map (substSimple su) ss)
    Proj x i ss -> Proj x i (map (substSimple su) ss)

substExpr :: (a -> Simple a) -> Expr a -> Expr a
substExpr su e0 =
  case e0 of
    Simple s     -> Simple (substSimple su s)
    Let x f ss e -> Let x f (map (substSimple su) ss) (substExpr su e)
    Match e calls alts ->
      Match (substSimple su e)
        [ Call f x (substExpr su e) | Call f x e <- calls ]
        [ pat :=> substExpr su rhs | pat :=> rhs <- alts ]

instance Pretty a => Pretty (Expr a) where
  pp (Simple s) = pp s
  pp (Let x f args e) = sep ["let" $\ pp x <+> "=" $\ pp f <+> fsep (map pp args) <> ";",pp e]
  pp (Match s calls alts) =
    ("case" $\ pp s <+> "of")
      $\ (if null calls then empty else braces (vcat (punctuate ";" (map pp calls))))
      $$ vcat (map pp alts)

instance Pretty a => Pretty (Simple a) where
  pp (Var a)        = pp a
  pp (Con k [])     = pp k
  pp (Con k ss)     = parens (pp k $\ fsep (map pp ss))
  pp (Proj tc i ss) = parens ("proj" <> pp tc <> "_" <> pp i $\ fsep (map pp ss))

instance Pretty a => Pretty (Call a) where
  pp (Call f xs e) = (pp f $\ fsep (map pp xs)) $\ "=" <+> pp e

instance Pretty a => Pretty (Alt a) where
  pp (p :=> e) = pp p <+> "->" $\ pp e

instance Pretty a => Pretty (Pat a) where
  pp Default    = "_"
  pp (ConPat k) = pp k


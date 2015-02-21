{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module TipTarget where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

data Expr a
  = Apply a [Expr a]
  | Do [Stmt a] (Expr a)
  | Lam (Pat a) (Expr a)
  | List [Expr a] -- a literal list
  | Noop
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

mkDo []      x = x
mkDo ss Noop = case (init ss,last ss) of
  (i,Stmt e)   -> mkDo i e
  (i,Bind x e) -> mkDo i e
mkDo ss e = Do ss e

var :: a -> Expr a
var x = Apply x []

data Pat a = VarPat a | ConPat a [Pat a] | TupPat [Pat a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Stmt a = Bind a (Expr a) | Stmt (Expr a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

instance Pretty a => Pretty (Expr a) where
  pp e =
    case e of
      Apply x es -> pp x $\ fsep (map pp_par es)
      Do ss e    -> "do" $\ (vcat (punctuate ";" (map pp (ss ++ [Stmt e]))))
      Lam p e    -> "\\" <+> pp p <+> "->" $\ pp e
      List es    -> brackets (fsep (punctuate "," (map pp es)))
      Noop       -> "return ()"
   where
    pp_par e0 =
      case e0 of
        Apply x [] -> pp e0
        _          -> parens (pp e0)

instance Pretty a => Pretty (Stmt a) where
  pp (Bind x e) = pp x <+> "<-" $\ pp e
  pp (Stmt e)   = pp e

instance Pretty a => Pretty (Pat a) where
  pp p = case p of
    VarPat x    -> pp x
    ConPat k ps -> parens (pp k $\ fsep (map pp ps))
    TupPat ps   -> parens (fsep (punctuate "," (map pp ps)))


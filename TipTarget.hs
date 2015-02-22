{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module TipTarget where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Tip (Type(..))

-- Equal
-- EqualData equalData
-- ConstructiveData constrs
-- Thunk
-- Data
-- Maybe Nothing Just
-- Value
-- Type
-- dflt
-- get
-- getData

class Interface a where
  prelude :: String -> a
  api     :: String -> a

data Decl a
  = FunDecl a [a] (Expr a)
  | DataDecl a [a] [(a,[Type a])] [String]
  | InstDecl [Type a] {-^ context -}
             (Type a) {-^ head -}
             [Decl a] {-^ declarations (associated types and fun decls) -}
  | AssociatedType (Type a) (Type a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Expr a
  = Apply a [Expr a]
  | Do [Stmt a] (Expr a)
  | Lam [Pat a] (Expr a)
  | List [Expr a] -- a literal list
  | Tup [Expr a]  -- a literal tuple
  | Noop
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

mkDo []      x = x
mkDo ss1 (Do ss2 e) = mkDo (ss1 ++ ss2) e
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
      Apply x [] -> pp x
      Apply x es | Lam ps b <- last es -> ((pp x $\ fsep (map pp_par (init es))) $\ "(\\" <+> fsep (map pp ps) <+> "->") $\ pp b <> ")"
      Apply x es -> pp x $\ fsep (map pp_par es)
      Do ss e    -> "do" <+> (vcat (map pp (ss ++ [Stmt e])))
      Lam ps e   -> "\\" <+> fsep (map pp ps) <+> "->" $\ pp e
      List es    -> brackets (fsep (punctuate "," (map pp es)))
      Tup es     -> tuple (map pp es)
      Noop       -> "return ()"
   where
    pp_par e0 =
      case e0 of
        Apply x [] -> pp e0
        List{}     -> pp e0
        Tup{}      -> pp e0
        _          -> parens (pp e0)

instance Pretty a => Pretty (Stmt a) where
  pp (Bind x e) = pp x <+> "<-" $\ pp e
  pp (Stmt e)   = pp e

instance Pretty a => Pretty (Pat a) where
  pp p =
    case p of
      VarPat x    -> pp x
      ConPat k ps -> parens (pp k $\ fsep (map pp ps))
      TupPat ps   -> tuple (map pp ps)

tuple :: [Doc] -> Doc
tuple []     = "()"
tuple (d:ds) = parens (sep [d <> ",",tuple ds])

instance Pretty a => Pretty (Decl a) where
  pp d =
    case d of
      FunDecl f xs e -> (pp f $\ fsep (map pp xs) <+> "=") $\ pp e
      DataDecl tc tvs cons derivs ->
        (((if length cons == 1 then "newtype" else "data") $\ pp tc) $\ fsep (map pp tvs) <+> "=") $\
          fsep (punctuate "|" [ pp c $\ fsep (map pp ts) | (c,ts) <- cons ]) $\
          "deriving" <+> fsep (punctuate "," (map text derivs))
      InstDecl ctx head ds ->
        (("instance" $\
          ((if null ctx then empty else
             parens (fsep (punctuate "," (map pp ctx))) <+> "=>") $\ pp head)) $\
             "where") $\ vcat (map pp ds)
      AssociatedType lhs rhs -> "type" <+> pp lhs <+> "=" $\ pp rhs


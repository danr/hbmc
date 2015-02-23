{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module TipTarget where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import TipLift (Call)

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

class TipLift.Call a => Interface a where
  prelude   :: String -> a
  api       :: String -> a

  proj      :: a -> Int -> a
  unproj    :: a -> Maybe (a,Int)
  mproj     :: a -> Int -> a

  mainFun   :: a

  conLabel  :: a -> a -- the translation of constructors
  conRepr   :: a -> a -- concrete datatype representation
  thunkRepr :: a -> a
  wrapData  :: a -> a
  caseData  :: a -> a -- caseNat
  mkCon     :: a -> a -- the pure constructors

data Decls a = Decls [Decl a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Decl a
  = TySig a [Type a] (Type a)
  | FunDecl a [([Pat a],Expr a)]
  | DataDecl a [a] [(a,[Type a])] [a]
  | InstDecl [Type a] {-^ context -}
             (Type a) {-^ head -}
             [Decl a] {-^ declarations (associated types and fun decls) -}
  | AssociatedType (Type a) (Type a)
  | Decl a `Where` [Decl a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

funDecl :: a -> [a] -> Expr a -> Decl a
funDecl f xs b = FunDecl f [(map VarPat xs,b)]

data Type a
  = TyCon a [Type a]
  | TyVar a
  | TyTup [Type a]
  | TyArr (Type a) (Type a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

modTyCon :: (a -> a) -> Type a -> Type a
modTyCon f t0 =
  case t0 of
    TyCon t ts  -> TyCon (f t) (map (modTyCon f) ts)
    TyVar x     -> TyVar x
    TyTup ts    -> TyTup (map (modTyCon f) ts)
    TyArr t1 t2 -> TyArr (modTyCon f t1) (modTyCon f t2)

data Expr a
  = Apply a [Expr a]
  | Do [Stmt a] (Expr a)
  | Lam [Pat a] (Expr a)
  | List [Expr a] -- a literal list
  | Tup [Expr a]  -- a literal tuple
  | LinearTup [Expr a]
  | String a      -- string from a name...
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

data Pat a = VarPat a | ConPat a [Pat a] | TupPat [Pat a] | WildPat
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Stmt a = Bind a (Expr a) | BindTyped a (Type a) (Expr a) | Stmt (Expr a)
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
      LinearTup es -> parens (fsep (punctuate "," (map pp es)))
      String s   -> "\"" <> pp s <> "\""
      Noop       -> "Prelude.return ()"
   where
    pp_par e0 =
      case e0 of
        Apply x []  -> pp e0
        List{}      -> pp e0
        Tup{}       -> pp e0
        LinearTup{} -> pp e0
        String{}    -> pp e0
        _           -> parens (pp e0)

instance Pretty a => Pretty (Stmt a) where
  pp (Bind x e)        = pp x <+> "<-" $\ pp e
  pp (BindTyped x t e) = (pp x <+> "::" $\ pp t <+> "<-") $\ pp e
  pp (Stmt e)          = pp e

instance Pretty a => Pretty (Pat a) where
  pp p =
    case p of
      VarPat x    -> pp x
      ConPat k ps -> parens (pp k $\ fsep (map pp ps))
      TupPat ps   -> tuple (map pp ps)
      WildPat     -> "_"

tuple :: [Doc] -> Doc
tuple []     = "()"
tuple (d:ds) = parens (sep [d <> ",",tuple ds])

instance Pretty a => Pretty (Decl a) where
  pp d =
    case d of
      TySig f ctx t -> (pp f <+> "::" $\ parens (fsep (punctuate "," (map pp ctx))) <+> "=>") $\ pp t
      FunDecl f xs ->
        vcat
          [ (pp f $\ fsep (map pp ps) <+> "=") $\ pp b
          | (ps,b) <- xs
          ]
      DataDecl tc tvs cons derivs ->
        (((case cons of
             [(_,[_])] -> "newtype"
             _         -> "data") $\ pp tc) $\ fsep (map pp tvs) <+> "=") $\
          (fsep (punctuate " |" [ pp c $\ fsep (map (parens . pp) ts) | (c,ts) <- cons ]) $$
          (if null derivs then empty
           else "deriving" <+> parens (fsep (punctuate "," (map pp derivs)))))
      InstDecl ctx head ds ->
        (("instance" $\
          ((if null ctx then empty else
             parens (fsep (punctuate "," (map pp ctx))) <+> "=>") $\ pp head)) $\
             "where") $\ vcat (map pp ds)
      AssociatedType lhs rhs -> "type" <+> pp lhs <+> "=" $\ pp rhs
      decl `Where` ds -> pp decl $\ "where" $\ vcat (map pp ds)

instance Pretty a => Pretty (Decls a) where
  pp (Decls ds) = vcat (map pp ds)

instance Pretty a => Pretty (Type a) where
  pp t0 =
    case t0 of
      TyCon t []  -> pp t
      TyCon t ts  -> pp t $\ fsep (map (parens . pp) ts)
      TyVar x     -> pp x
      TyTup ts    -> tuple (map pp ts)
      TyArr t1 t2 -> parens (pp t1 <+> "->" $\ pp t2)


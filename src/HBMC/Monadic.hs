module HBMC.Monadic where

import Tip.Core as Tip
import Tip.Haskell.Repr as H

import HBMC.Identifiers

justExpr :: H.Expr Var -> H.Expr Var
justExpr e = H.Apply (prelude "Just") [e]

newExpr :: H.Expr Var
newExpr = H.Apply (api "new") []

thenReturn :: [H.Stmt Var] -> Var -> H.Expr Var
ss `thenReturn` x = mkDo ss (returnExpr (var x))

(>>>) :: H.Expr Var -> H.Expr Var -> H.Expr Var
a >>> b = H.Apply (api ">>>") [a,b]

returnExpr :: H.Expr Var -> H.Expr Var
returnExpr e = H.Apply (prelude "return") [e]

trType :: Tip.Type a -> H.Type a
trType t0 =
  case t0 of
    Tip.TyCon t ts -> H.TyCon t (map trType ts)
    Tip.TyVar x    -> H.TyVar x
    _              -> error "trType: Cannot translate type\n(using HOFs, classes or Ints?)"

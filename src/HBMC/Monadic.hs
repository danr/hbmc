module HBMC.Monadic where

import Tip.Core as Tip
import Tip.Haskell.Repr as H
import Tip.Fresh

import HBMC.Identifiers

import Data.List

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

thenExpr :: H.Expr Var -> H.Expr Var -> H.Expr Var
thenExpr e1 e2 = mkDo [Stmt e1,Stmt e2] Noop

trType :: Tip.Type a -> H.Type a
trType t0 =
  case t0 of
    Tip.TyCon t ts -> H.TyCon t (map trType ts)
    Tip.TyVar x    -> H.TyVar x
    _              -> error "trType: Cannot translate type\n(using HOFs, classes or Ints?)"

isMatch :: Tip.Expr a -> Bool
isMatch Match{} = True
isMatch _       = False

trExpr :: Tip.Expr Var -> Var -> Fresh (H.Expr Var)
trExpr e00 r =
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  mkDo [ H.Bind (lcl_name x) newExpr | (x,_) <- matches ]
        <$> go (makeLets (fn_calls ++ matches) rest)
  where
  go e0 =
    case e0 of
      Tip.Let x (Match s brs) e ->
        thenExpr <$> trMatch s brs (lcl_name x)
                 <*> go e

      Tip.Let x (Gbl (Global f _ _) :@: ss) e ->
        mkDo [H.Bind (lcl_name x) (H.Apply f [nestedTup (map trSimple ss)])] <$> go e

      Match s brs -> trMatch s brs r

      Gbl (Global g _ _) :@: _ | g == noopVar -> return Noop

      s -> return (trSimple s >>> var r)

trMatch :: Tip.Expr Var -> [Case Var] -> Var -> Fresh (H.Expr Var)
trMatch e brs r | Tip.TyCon tc _ <- exprType e =
  do c <- fresh
     s <- fresh

     let ls = Local s (exprType e)

     let ctors = [ k | Tip.Case (Tip.ConPat (Global k _ _) _) _ <- brs ]

     brs' <- mapM (trCase c r ctors . replaceProj e ls) brs

     -- waitCase e $ \ (Con c s) ->
     --   ...
     --   when (c =? K_i) $ do [[ br_i (sel s // sel e) ]]=> r
     --   ...

     return $
       H.Apply (caseData tc) [trSimple e,
         H.Lam [H.ConPat (api "Con") [H.VarPat c,H.VarPat s]]
           (mkDo brs' Noop)
         ]

trMatch _ _ _ = error "trMatch: Not a TyCon!"

replaceProj :: Tip.Expr Var -> Local Var -> Tip.Case Var -> Tip.Case Var
replaceProj e s (Tip.Case p rhs) =
  Tip.Case p $ (`transformExprIn` rhs) $
    \ e0 -> case e0 of
      hd@(Gbl (Global g _ _)) :@: [e'] | e == e', Just{} <- unproj g -> hd :@: [Lcl s]

      _ -> e0

trSimple :: Tip.Expr Var -> H.Expr Var
trSimple s =
  case s of
    Lcl (Local x _) -> var x
    Gbl (Global k _ _) :@: [s] | Just{} <- unproj k -> H.Apply k [trSimple s]
    Gbl (Global k _ _) :@: ss -> H.Apply (mkCon k) (map trSimple ss)
    _ -> error "trSimple: not simple"

trCase :: Var -> Var -> [Var] -> Case Var -> Fresh (H.Stmt Var)
trCase c r cons (Tip.Case pat rhs) =
  do body <- trExpr rhs r
     let (fn,arg) =
           case pat of
             Default                     -> ("unless",List [c =? k | k <- cons])
             Tip.ConPat (Global k _ _) _ -> ("when"  ,c =? k)
     return (Stmt (H.Apply (api fn) [arg,body]))
  where
  x =? lbl = H.Apply (api "valEq") [var x,var (conLabel lbl)]

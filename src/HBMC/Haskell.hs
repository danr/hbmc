module HBMC.Haskell where

import HBMC.Monadic
import HBMC.Identifiers hiding (Var,Con,Proj)
import HBMC.Identifiers (Var())

import Tip.Haskell.Repr as H

-- Translation from constraint-generation dsl to Haskell

trFunc :: Func Var -> Decl Var
trFunc (Func f as r _r_ty chk b) =
  funDecl f [] $
    Apply (api "nomemo")
      [ String f
      , Lam [nestedTupPat (map VarPat as),VarPat r] (maybe_check (trMon b))
      ]
  where
  maybe_check
    | chk = H.Apply (api "check") . return
    | otherwise = id

trProp :: Verbosity -> Prop Var -> Expr Var
trProp v (Prop vs m) =
  Apply (api "run")
    [trMon m `thenExpr`
       (H.Apply (api "solveAndSee")
          [ var $ prelude $ case v of Quiet -> "True";  Verbose -> "False"
          , var $ prelude $ case v of Quiet -> "False"; Verbose -> "True"
          , tagShow vs
          ])]

trMon :: Mon Var -> Expr Var
trMon xs = mkDo (map trAct xs) Noop

trAct :: Act Var -> Stmt Var
trAct a =
  case a of
    Guard w p m -> Stmt (Apply (api fn) [ps,trMon m])
      where
      (fn,ps) =
        case (w,map trPred p) of
          (When,[p'])  -> ("when",p')
          (When,ps')   -> ("whens",List ps')
          (Unless,ps') -> ("unless",List ps')
    CaseData tc s v c m ->
      Stmt
        (Apply (caseData tc) [trSimp s,
          Lam [H.ConPat (api "Con") [H.VarPat v,H.VarPat c]] (trMon m)])
    BinPrim bp s1 s2 ->
      Stmt (Apply (api bp') (map trSimp [s1,s2]))
      where
      bp' = case bp of EqualHere -> "equalHere"
                       NotEqualHere -> "notEqualHere"
    s :>>>: x -> Stmt (trSimp s >>> var x)
    x :<-: rhs ->
      Bind x $
        case rhs of
          Call f ss -> Apply f [nestedTup (map trSimp ss)]
          New i _tc -> Apply (api (if i then "newInput" else "new")) []

trSimp :: Simp Var -> Expr Var
trSimp (Con _ x ss) = Apply (mkCon x) (map trSimp ss)
trSimp (Proj i x)   = Apply (proj i) [var x]
trSimp (Var x)      = var x

trPred :: Pred Var -> Expr Var
trPred (x :=? lbl) = H.Apply (api "valEq") [var x,var (conLabel lbl)]

-- Expression builders

justExpr :: Expr Var -> Expr Var
justExpr e = Apply (prelude "Just") [e]

newExpr :: Expr Var
newExpr = Apply (api "new") []

thenReturn :: [Stmt Var] -> Var -> Expr Var
ss `thenReturn` x = mkDo ss (returnExpr (var x))

(>>>) :: Expr Var -> Expr Var -> Expr Var
a >>> b = Apply (api ">>>") [a,b]

returnExpr :: Expr Var -> Expr Var
returnExpr e = Apply (prelude "return") [e]

thenExpr :: Expr Var -> Expr Var -> Expr Var
thenExpr (Do ss e1) e2 = mkDo (ss ++ [ Stmt e1, Stmt e2 ]) Noop
thenExpr e1 e2 = mkDo [Stmt e1,Stmt e2] Noop

tagShow :: [Var] -> Expr Var
tagShow []     = var   (api "TagNil")
tagShow (x:xs) = Apply (api "TagCons") [String x,var x,tagShow xs]


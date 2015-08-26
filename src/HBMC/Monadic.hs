{-# LANGUAGE RecordWildCards #-}
module HBMC.Monadic where

import Tip.Core as Tip
import Tip.Haskell.Repr as H
import Tip.Fresh

import HBMC.Identifiers

import HBMC.Bool
import Tip.Passes

import Data.Generics.Geniplate

import HBMC.ToSimple

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

trType :: Tip.Type a -> H.Type a
trType t0 =
  case t0 of
    Tip.TyCon t ts -> H.TyCon t (map trType ts)
    Tip.TyVar x    -> H.TyVar x
    _              -> error "trType: Cannot translate type\n(using HOFs, classes or Ints?)"

-- Simple termination check: there is some argument that always decreases
-- Not working for mutually recursive groups!
terminates :: Var          -- function name
           -> [Var]        -- arguments
           -> Tip.Expr Var -- body as a simple expression
           -> Bool
terminates _ [] _ = True
terminates f as e =
  or [ and [ chase a (es !! i)
           | Gbl (Global f' _ _) :@: es <- universeBi e
           , f == f' ]
     | (a,i) <- as `zip` [0..] ]
  where
  chase needle (Lcl (Local x _)) = needle == x
  chase needle (Gbl (Global g _ _) :@: [e]) | Just{} <- unproj g = chase needle e
  chase _ _ = False

trFunc :: Tip.Function Var -> Fresh [H.Decl Var]
trFunc Tip.Function{..} =
  do r <- fresh
     simp_body <- toExpr func_body
     let args = map Tip.lcl_name func_args
     let maybe_check e
           | terminates func_name args simp_body = e
           | otherwise = H.Apply (api "check") [e]
     body <-
       {-
       if superSimple simp_body
         then
           do e <- trExpr simp_body Nothing
              return $ H.Lam [H.nestedTupPat (map H.VarPat args)] e
         else
           do -}
           do b <- trExpr simp_body (Just r)
              return $
                H.Apply (api "nomemo")
                  [H.String func_name
                  ,H.Lam [H.nestedTupPat (map H.VarPat args),H.VarPat r] (maybe_check b)
                  ]
     return
       [ let tt = modTyCon wrapData . trType
         in H.TySig func_name
              [ H.TyCon s [H.TyVar tv]
              | tv <- func_tvs
              , s <- [api "Equal",prelude "Ord",api "Constructive"]
              ]
              (nestedTyTup (map (tt . Tip.lcl_type) func_args)
               `TyArr` (H.TyCon (api "H") [tt func_res]))
       , funDecl func_name [] body
       ]

superSimple :: Tip.Expr a -> Bool
superSimple e =
  case e of
    Lcl _   -> True
    _ :@: _ -> True
    Tip.Let _ (_ :@: _) r -> superSimple r
    _ -> False

data Verbosity = Quiet | Verbose deriving (Eq,Ord,Show,Read)

trProp :: Verbosity -> Tip.Formula Var -> Fresh (H.Expr Var)
trProp v fm =
  case fm of
    Tip.Formula r          (_:_) e -> error "trProp, TODO: translate type variables"
    Tip.Formula Tip.Prove  []    e -> trProp v (Tip.Formula Tip.Assert [] (neg e))
    Tip.Formula Tip.Assert []    e ->
      do let (vs,e') = fmap neg (forallView (neg e))
         let cs      = conjuncts (ifToBoolOp e')
         let news    = [ H.Bind (lcl_name v) (H.Apply (api "newInput") []) | v <- vs ]
         asserts <- mapM trToTrue cs
         return $
           H.Apply (api "run") . return $
           mkDo (news ++ map Stmt asserts)
                (H.Apply (api "solveAndSee")
                   [var $ prelude $ case v of Quiet -> "True";  Verbose -> "False"
                   ,var $ prelude $ case v of Quiet -> "False"; Verbose -> "True"
                   ,tagShow (map Tip.lcl_name vs)
                   ])

trToTrue :: Tip.Expr Var -> Fresh (H.Expr Var)
trToTrue e0 =
  case e0 of
    Builtin Equal    :@: ~[e1,e2] -> tr True  e1 e2
    Builtin Distinct :@: ~[e1,e2] -> tr False e1 e2
    _                             -> tr True  e0 (booly True)
  where
  tr pol e1 e2 =
    do (lets1,s1) <- collectLets <$> toExprSimpleEnd (addBool (boolOpToIf e1))
       (lets2,s2) <- collectLets <$> toExprSimpleEnd (addBool (boolOpToIf e2))
       let equal_fn = blankGlobal
                        (api (if pol then "equalHere" else "notEqualHere"))
                        (error "trToTrue global type")
       trExpr (makeLets (lets1 ++ lets2) (Gbl equal_fn :@: [s1,s2])) Nothing

conjuncts :: Tip.Expr a -> [Tip.Expr a]
conjuncts e0 =
  case e0 of
    Builtin And :@: es                            -> concatMap conjuncts es
    Builtin Not :@: [Builtin Or :@: es]           -> concatMap conjuncts es
    Builtin Not :@: [Builtin Implies :@: [e1,e2]] -> concatMap conjuncts [e1,neg e2]
    _                                             -> [e0]

-- [[ e ]]=> r
trExpr :: Tip.Expr Var -> Maybe Var -> Fresh (H.Expr Var)
trExpr e00 mr =
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  mkDo [ H.Bind (lcl_name x) newExpr | (x,_) <- matches ]
        <$> go (makeLets (fn_calls ++ matches) rest)
  where
  go e0 =
    case e0 of
      Tip.Let x (Match s brs) e ->
        thenExpr <$> trMatch s brs (Just (lcl_name x))
                 <*> go e

      Tip.Let x (Gbl (Global f _ _) :@: ss) e ->
        mkDo [H.Bind (lcl_name x) (H.Apply f [nestedTup (map trSimple ss)])] <$> go e

      Match s brs -> trMatch s brs mr

      Gbl (Global g _ _) :@: _ | g == noopVar -> return Noop

      s -> case mr of Just r  -> return (trSimple s >>> var r)
                      Nothing -> return (trSimple s)

trMatch :: Tip.Expr Var -> [Case Var] -> Maybe Var -> Fresh (H.Expr Var)
trMatch e brs mr | Tip.TyCon tc _ <- exprType e =
  do c <- fresh
     s <- fresh

     let ls = Local s (exprType e)

     let ctors = [ k | Tip.Case (Tip.ConPat (Global k _ _) _) _ <- brs ]

     brs' <- mapM (trCase c mr ctors . replaceProj e ls) brs

     -- waitCase e $ \ (Con c s) ->
     --   ...
     --   when (c =? K_i) $ do [[ br_i (sel s // sel e) ]]=> r
     --   ...

     return $
       H.Apply (caseData tc) [trSimple e,
         H.Lam [H.ConPat (api "Con") [H.VarPat c,H.VarPat s]]
           (mkDo (concat brs') Noop)
         ]

trMatch _ _ _ = error "trMatch: Not a TyCon!"

-- sel s // sel e
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
    Gbl (Global g _ _) :@: ss | isApi g -> H.Apply g (map trSimple ss)
    Gbl (Global k _ _) :@: ss -> H.Apply (mkCon k) (map trSimple ss)
    _ -> error $ "trSimple, not simple: " ++ ppRender s

trCase :: Var -> Maybe Var -> [Var] -> Case Var -> Fresh [H.Stmt Var]
trCase c mr cons (Tip.Case pat rhs) =
  do body <- trExpr rhs mr
     let (fn,arg) =
           case pat of
             Default                     -> ("unless",List [c =? k | k <- cons])
             Tip.ConPat (Global k _ _) _ -> ("when"  ,c =? k)
     case body of
       Noop -> return []
       _    -> return [Stmt (H.Apply (api fn) [arg,body])]
  where
  x =? lbl = H.Apply (api "valEq") [var x,var (conLabel lbl)]

-- Expression builders

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

tagShow :: [Var] -> H.Expr Var
tagShow []     = var   (api "TagNil")
tagShow (x:xs) = Apply (api "TagCons") [H.String x,var x,tagShow xs]

isMatch :: Tip.Expr a -> Bool
isMatch Match{} = True
isMatch _       = False


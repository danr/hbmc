{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
module TipMonadic where

import Tip.Pretty (Pretty,ppRender)
import Tip.Fresh

import TipSimple as S
import TipTarget as H
import qualified TipToSimple as ToS
import qualified Tip
import TipLift

import Data.Maybe

import Control.Applicative

justExpr :: Interface a => H.Expr a -> H.Expr a
justExpr e = H.Apply (prelude "Just") [e]

newExpr :: Interface a => H.Expr a
newExpr = H.Apply (api "new") []

thenReturn :: Interface a => [H.Stmt a] -> a -> H.Expr a
ss `thenReturn` x = mkDo ss (returnExpr (var x))

(>>>) :: Interface a => H.Expr a -> H.Expr a -> H.Expr a
a >>> b = H.Apply (api "equalHere") [a,b]

trType :: Tip.Type a -> Type a
trType t0 =
  case t0 of
    Tip.TyCon t ts -> TyCon t (map trType ts)
    Tip.TyVar x    -> TyVar x
    _              -> error "trType: Cannot translate type\n(using HOFs, classes or Ints?)"

trFun :: Interface a => ([a],[a]) -> Tip.Function a -> Fresh [H.Decl a]
trFun (memos,checks) Tip.Function{..} =
  do r <- fresh
     simp_body <- ToS.toExpr func_body

     let args = map Tip.lcl_name func_args

     let maybe_check e | func_name `elem` checks = H.Apply (api "check") [e]
                       | otherwise = e

     body <-
         if superSimple simp_body
            then
              do -- NB: Ignores memo and check on this function
                 x <- fresh
                 e <- trExpr simp_body Nothing
                 return $
                   H.Lam [H.TupPat (map H.VarPat args)] $
                       mkDo [H.Bind x e] (returnExpr (H.Apply (api "unJust") [var x]))
            else
              do b <- trExpr simp_body (Just r)
                 return $
                   H.Apply (api (if func_name `elem` memos then "memo" else "nomemo"))
                     [H.String func_name
                     ,H.Lam [H.TupPat (map H.VarPat args),H.VarPat r] (maybe_check b)
                     ]
     return
       [
         {-
         let tt   = modTyCon wrapData . trType
         in H.TySig func_name
              [ TyCon s [TyVar tv]
              | tv <- func_tvs
              , s <- [api "Equal",prelude "Ord",api "Constructive"]
              ]
              (TyTup (map (tt . Tip.lcl_type) func_args)
               `TyArr` (TyCon (api "H") [tt func_res])),
         -}
         funDecl func_name [] body
       ]

superSimple :: S.Expr a -> Bool
superSimple (S.Let _ S.Proj{} _)  = False
superSimple (S.Let _ S.Apply{} e) = superSimple e
superSimple S.Match{}             = False
superSimple S.Simple{}            = True

trProp :: Interface a => Tip.Formula a -> Fresh (a,H.Decl a)
trProp (Tip.Formula Tip.Prove [] (Tip.collectQuant -> (lcls,tm)))
  = do let input = [ BindTyped x (modTyCon wrapData (trType t)) (var (api "newInput"))
                   | Tip.Local x t <- lcls ]
       terms <- mapM trTerm (collectTerms tm)
       f <- fresh
       return $ (,) f $ funDecl f [] $
         mkDo (input ++ concat terms)
           (H.Apply (api "solveAndSee")
             [tagShow (map Tip.lcl_name lcls)])
trProp fm = error $ "Invalid property: " ++ ppRender fm ++ "\n(cannot be polymorphic)"

type Term a = (Bool,Tip.Expr a,Tip.Expr a)

collectTerms :: Pretty a => Tip.Expr a -> [Term a]
collectTerms (Tip.Builtin Tip.Implies Tip.:@: [pre,post])
  = let (l,r) = collectEqual pre
    in  (False,l,r):collectTerms post
collectTerms t = let (l,r) = collectEqual t in [(True,l,r)]

collectEqual :: Pretty a => Tip.Expr a -> (Tip.Expr a,Tip.Expr a)
collectEqual (Tip.Builtin Tip.Equal Tip.:@: [l,r]) = (l,r)
collectEqual p = error $ "Cannot understand property: " ++ ppRender p

trTerm :: Interface a => Term a -> Fresh [H.Stmt a]
trTerm (pol,lhs,rhs) =
  do (l_lets,l) <- ToS.toSimple lhs
     (r_lets,r) <- ToS.toSimple rhs
     dum1 <- fresh
     e <- trExpr
       (bindLets
         (l_lets ++ r_lets ++
           [(dum1,S.Apply (if pol then api "neqTup" else api "eqTup") [l,r])])
         (S.Simple (S.Var dum1)))
       Nothing
     return [H.Stmt e]

trExpr :: Interface a => S.Expr a -> Maybe a -> Fresh (H.Expr a)
trExpr e0 r =
  case e0 of
    S.Simple s ->
      case r of
        Just r' -> return (trSimple s >>> var r')
        Nothing -> return (returnExpr (justExpr (trSimple s)))

    S.Let x (S.Proj i t s) e ->
      do e' <- trExpr e r
         return (H.Apply ((if isJust r then proj else mproj) i t)
                   [trSimple s,H.Lam [VarPat x] e'])

    S.Let x (S.Apply f ss) e
      | f == callName, Var g:args <- ss
        -> do e' <- trExpr e r
              return $
                mkDo
                  [ H.Bind x (H.Apply (api "call") [var g,H.Tup (map trSimple args)]) ]
                  e'
      | f == cancelName, [Var g,y] <- ss
        -> do e' <- trExpr e r
              return $
                mkDo
                  [ H.Stmt (H.Apply (api "nocall") [var g])
                  , H.Bind x (returnExpr (trSimple y))
                  ]
                  e'
      | otherwise -> mkDo [H.Bind x (H.Apply f [Tup (map trSimple ss)])] <$> trExpr e r

    S.Match tc s s' calls alts
      | Nothing <- r -> error $ "Cannot do case inside a lifted call: " ++ ppRender e0
      | Just rr <- r ->
          do calls' <- mapM trCall calls

             c <- fresh
             let ctors = [ k | S.ConPat k S.:=> _ <- alts ]
             alts' <- mapM (trAlt c rr ctors) alts

             -- do waitCase s $ \ c s' ->
             --      [[ calls ]]
             --      when (c =? K1) $ do
             --        y <- [[ br1 ]]
             --        y >>> r
             --      ...
             return $
               H.Apply (caseData tc) [trSimple s,
                 H.Lam [H.ConPat (api "Con") [H.VarPat c,H.VarPat s']]
                   (mkDo (calls' ++ alts') Noop)
                 ]

    _ -> error $ "iota redex in match or proj: " ++ ppRender e0

trSimple :: Interface a => S.Simple a -> H.Expr a
trSimple (S.Var x)    = var x
trSimple (S.Con k ss) = H.Apply (mkCon k) (map trSimple ss)

trCall :: Interface a => S.Call a -> Fresh (H.Stmt a)
trCall (Call f args e) =
  do e' <- trExpr e Nothing
     -- x <- newCall $ \ (a1,..,an) -> [[ e ]]
     return $
       H.Bind f
         (H.Apply (api "newCall")
           [H.Lam [H.TupPat (map H.VarPat args)] e'])

trAlt :: Interface a => a -> a -> [a] -> S.Alt a -> Fresh (H.Stmt a)
trAlt c r cons (pat S.:=> rhs) =
  do body <- trExpr rhs (Just r)
     return $ Stmt $
       case pat of
         S.Default  -> H.Apply (api "unless") [List [H.Apply (=?) [var c,var (conLabel k)] | k <- cons],body]
         S.ConPat k -> H.Apply (api "when") [H.Apply (=?) [var c,var (conLabel k)],body]

 where
  (=?) = api "valEq"

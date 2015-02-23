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

import Control.Applicative

returnExpr :: Interface a => H.Expr a -> H.Expr a
returnExpr e = H.Apply (prelude "return") [e]

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

trFun :: Interface a => Tip.Function a -> Fresh [H.Decl a]
trFun Tip.Function{..} =
  do r <- fresh
     simp_body <- ToS.toExpr func_body
     b <- trExpr simp_body r
     let args = map Tip.lcl_name func_args
     return
       [
         let tt   = modTyCon wrapData . trType
         in H.TySig func_name
              [ TyCon (api s) [TyVar tv]
              | tv <- func_tvs
              , s <- ["Equal","Eq","Constructive"]
              ]
              (foldr TyArr
                 (TyCon (api "H") [tt func_res])
                 (map (tt . Tip.lcl_type) func_args)),

         funDecl func_name args
          (H.Apply (api "memo")
            [H.String func_name
            ,H.Tup (map var args)
            ,H.Lam [H.VarPat r] b
            ])
       ]

trProp :: Interface a => Tip.Formula a -> Fresh (H.Decl a)
trProp (Tip.Formula Tip.Prove [] (Tip.collectQuant -> (lcls,tm)))
  = do let input = [ BindTyped x (modTyCon wrapData (trType t)) (var (api "newInput"))
                   | Tip.Local x t <- lcls ]
       terms <- mapM trTerm (collectTerms tm)
       f <- fresh
       return $ funDecl f [] $
         mkDo (input ++ concat terms)
           (H.Apply (api "solveAndSee") [Tup (map (var . Tip.lcl_name) lcls)])
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
  do l <- fresh
     r <- fresh
     lhs' <- ToS.toExpr lhs
     rhs' <- ToS.toExpr rhs
     tr_l <- trExpr lhs' l
     tr_r <- trExpr rhs' r
     return
       [ H.Bind l (var (api "new"))
       , H.Bind r (var (api "new"))
       , H.Stmt tr_l
       , H.Stmt tr_r
       , H.Stmt (H.Apply (if pol then api "notEqualHere" else api "equalHere") [var l,var r])
       ]

trExpr :: Interface a => S.Expr a -> a -> Fresh (H.Expr a)
trExpr e0 r =
  case e0 of
    S.Simple s -> return (trSimple s >>> var r)
    S.Let x (S.Proj i t s) e ->
      do e' <- trExpr e r
         return (H.Apply (proj i t) [trSimple s,H.Lam [VarPat x] e'])
    S.Let x (S.Apply f ss) e
      | f == callName, Var g:args <- ss
        -> do e' <- trExpr e r
              return
                (H.Apply (api "call")
                  [var g,H.Tup (map trSimple args),H.Lam [VarPat x] e'])
      | f == cancelName, [Var g,y] <- ss
        -> do e' <- trExpr e r
              return $
                mkDo
                  [ H.Stmt (H.Apply (api "nocall") [var g])
                  , H.Bind x (returnExpr (trSimple y))
                  ]
                  e'
      | otherwise -> mkDo [H.Bind x (H.Apply f (map trSimple ss))] <$> trExpr e r

    S.Match s calls alts ->
      do s' <- fresh

         let change x | x == s    = s'
                      | otherwise = x

         calls' <- mapM (trCall . fmap change) calls

         c <- fresh
         let ctors = [ k | S.ConPat k S.:=> _ <- alts ]
         alts' <- mapM (trAlt c r ctors . fmap change) alts

         -- do waitCase s $ \ c s' ->
         --      [[ calls ]]
         --      when (c =? K1) $ do
         --        y <- [[ br1 ]]
         --        y >>> r
         --      ...
         return $
           H.Apply (api "caseData") [{- H.Apply (api "unwrap") [-}var s{-]-},H.Lam [VarPat c,VarPat s']
             (mkDo (calls' ++ alts') Noop)
           ]

trSimple :: Interface a => S.Simple a -> H.Expr a
trSimple (S.Var x)    = var x
trSimple (S.Con k ss) = H.Apply (mkCon k) (map trSimple ss)

trCall :: Interface a => S.Call a -> Fresh (H.Stmt a)
trCall (Call f args e) =
  do r' <- fresh
     e' <- trExpr e r'
     -- x <- newCall $ \ (a1,..,an) -> \ r' -> e => r'
     return $
       H.Bind f
         (H.Apply (api "newCall")
           [H.Lam [H.TupPat (map H.VarPat args), H.VarPat r'] e'])

trAlt :: Interface a => a -> a -> [a] -> S.Alt a -> Fresh (H.Stmt a)
trAlt c r cons (pat S.:=> rhs) =
  do body <- trExpr rhs r
     return $ Stmt $
       case pat of
         S.Default  -> H.Apply (api "unless") [List [H.Apply (=?) [var c,var (conLabel k)] | k <- cons],body]
         S.ConPat k -> H.Apply (api "when") [H.Apply (=?) [var c,var (conLabel k)],body]

 where
  (=?) = api "(=?)"

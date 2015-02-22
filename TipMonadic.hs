{-# LANGUAGE ViewPatterns #-}
module TipMonadic where

import Tip.Pretty (ppRender)
import Tip.Fresh

import TipSimple as S
import TipTarget as H
import TipData
import TipLift

import Control.Applicative

class (Name a,TipLift.Call a,Proj a,H.Interface a) => Monadic a where
--   memofun   :: a -> a
--  construct :: a -> a -- the translation of constructors
  conLabel  :: a -> a -- the label for constructors
--   returnH   :: a
--   newCall   :: a
--   new       :: a
--   waitCase  :: a
--   con       :: a -- Con
--   memcpy    :: a
--   whenH     :: a
--   unlessH   :: a
--   (=?)      :: a

returnExpr :: Monadic a => H.Expr a -> H.Expr a
returnExpr e = H.Apply (prelude "return") [e]

newExpr :: Monadic a => H.Expr a
newExpr = H.Apply (api "new") []

thenReturn :: Monadic a => [H.Stmt a] -> a -> H.Expr a
ss `thenReturn` x = mkDo ss (returnExpr (var x))

(>>>) :: Monadic a => H.Expr a -> H.Expr a -> H.Expr a
a >>> b = H.Apply (api "equalHere") [a,b]

trExpr :: Monadic a => S.Expr a -> a -> Fresh (H.Expr a)
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
      do calls' <- mapM trCall calls

         c <- fresh
         let ctors = [ k | S.ConPat k S.:=> _ <- alts ]
         alts' <- mapM (trAlt c r ctors) alts

         -- do waitCase s $ \ c ->
         --      [[ calls ]]
         --      when (c =? K1) $ do
         --        y <- [[ br1 ]]
         --        y >>> r
         --      ...
         return $
           H.Apply (api "caseData") [H.Apply (api "unwrap") [trSimple s],H.Lam [VarPat c]
             (mkDo (calls' ++ alts') Noop)
           ]

trSimple :: Monadic a => S.Simple a -> H.Expr a
trSimple (S.Var x)    = var x
trSimple (S.Con k ss) = H.Apply k (map trSimple ss)

trCall :: Monadic a => S.Call a -> Fresh (H.Stmt a)
trCall (Call f args e) =
  do r' <- fresh
     e' <- trExpr e r'
     -- x <- newCall $ \ (a1,..,an) -> \ r' -> e => r'
     return $
       H.Bind f
         (H.Apply (api "newCall")
           [H.Lam [H.TupPat (map H.VarPat args), H.VarPat r'] e'])

trAlt :: Monadic a => a -> a -> [a] -> S.Alt a -> Fresh (H.Stmt a)
trAlt c r cons (pat S.:=> rhs) =
  do body <- trExpr rhs r
     return $ Stmt $
       case pat of
         S.Default  -> H.Apply (api "unless") [List [H.Apply (=?) [var c,var (conLabel k)] | k <- cons],body]
         S.ConPat k -> H.Apply (api "when") [H.Apply (=?) [var c,var (conLabel k)],body]

 where
  (=?) = api "=?"

{-# LANGUAGE ViewPatterns, FlexibleContexts #-}
module HBMC.ToSimple where

import Tip.Pretty
import Tip.Pretty.SMT ()

import Tip.Fresh

import HBMC.Identifiers

import Tip.Core

import Control.Monad.Writer

-- e ::= let x = f s1 .. sn in e
--    |  let x = c in e
--    |  c
--    |  s
--
-- c ::= case x of K1 -> e1
--                 ...
--                 Kn -> en
--
-- s ::= proj s | K s1 .. sn | x

toExpr :: Expr Var -> Fresh (Expr Var)
toExpr e0 =
  case e0 of
    Let x m@Match{} e2 ->
      do m' <- toMatch m
         Let x m' <$> toExpr e2

    Let x e1 e2 ->
      do (lets,s1) <- toSimple e1
         makeLets lets . unsafeSubst s1 x <$> toExpr e2

    m@Match{} -> toMatch m

    _ ->
      do (lets,s) <- toSimple e0
         return (makeLets lets s)

toMatch :: Expr Var -> Fresh (Expr Var)
toMatch e0 =
  case e0 of
    Match s@Lcl{} brs ->
      Match s <$> sequence [ Case pat <$> toExpr rhs | Case pat rhs <- brs ]

    _ -> error $ "Bad match expression: " ++ ppRender e0

toSimple :: Expr Var -> Fresh ([(Local Var,Expr Var)],Expr Var)
toSimple e =
  do (s,w) <- runWriterT (toSimple' e)
     return (w,s)

toSimple' :: Expr Var -> WriterT [(Local Var,Expr Var)] Fresh (Expr Var)
toSimple' e0 =
  case e0 of
    Lcl{} -> return e0

    hd@(Gbl (Global f _ _)) :@: args ->
      do xn <- mapM toSimple' args
         case () of
           () | isCon f            -> return (hd :@: xn)
              | Just{} <- unproj f -> return (hd :@: xn)
              | otherwise          ->
                do a <- lift fresh
                   let la = Local a (exprType e0)
                   tell [(la,hd :@: xn)]
                   return (Lcl la)

    Let x e1 e2 ->
      do s1 <- toSimple' e1
         let su = unsafeSubst s1 x
         let su_lets lets = [ (x,su lt) | (x,lt) <- lets ]
         fmap su (censor su_lets (toSimple' e2))

    _ -> error $ "toSimple': " ++ ppRender e0


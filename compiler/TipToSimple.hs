{-# LANGUAGE ViewPatterns #-}
module TipToSimple where

import TipSimple as S
import Tip.Types as T
import qualified Tip as T
import Tip.Fresh
import Tip.Pretty
import Control.Monad.Writer
import Control.Applicative
import TipTarget (Interface(proj,unproj))

toExpr :: Interface a => T.Expr a -> Fresh (S.Expr a)
toExpr e0 =
  case e0 of
    T.Let (Local x _) e1 e2 ->
      do (lets,s1) <- toSimple e1
         bindLets lets . substSimple (replace x s1) <$> toExpr e2

    T.Match (collectLets -> (calls,scrut_expr)) alts ->
      do (lets,Var s) <- toSimple scrut_expr

         s' <- fresh

         let su = substSimple $ \ x -> Var (if x == s then s' else x)

         calls' <-
           sequence
             [ do e' <- toExpr e
                  return (Call (lcl_name x) (map lcl_name args) (su e'))
             | (x,T.Lam args e) <- calls
             ]

         alts' <-
           sequence
             [ do rhs' <- toExpr rhs
                  return $ (S.:=> su rhs') $ case pat of
                    T.Default                   -> S.Default
                    T.ConPat (Global k _ _ _) _ -> S.ConPat k
             | T.Case pat rhs <- alts
             ]

         let tc =
               case T.exprType scrut_expr of
                 TyCon tc' _ -> tc'
                 t -> error $ "Case on non-TyCon typed scrut:\n  " ++ ppRender e0
                              ++ "\n " ++ ppRender t

         return (bindLets lets (S.Match tc (Var s) s' calls' alts'))

    _ ->
      do (lets,s) <- toSimple e0
         return (bindLets lets (Simple s))

collectLets :: T.Expr a -> ([(T.Local a,T.Expr a)],T.Expr a)
collectLets (T.Let x ex e) = let (bs,e') = collectLets e in ((x,ex):bs,e')
collectLets e              = ([],e)

toSimple :: Interface a => T.Expr a -> Fresh ([(a,Let a)],Simple a)
toSimple e =
  do (s,w) <- runWriterT (toSimple' e)
     return (w,s)

toSimple' :: Interface a => T.Expr a -> WriterT [(a,Let a)] Fresh (Simple a)
toSimple' e0 =
  case e0 of
    Lcl (Local x _) -> return (Var x)

    Gbl (Global f _ _ ns) :@: args ->
      do xn <- mapM toSimple' args
         case ns of
           ConstructorNS -> do return (Con f xn)
           FunctionNS    -> do a <- lift fresh
                               let lt = case unproj f of
                                          Just (tc,i) -> let [Var x] = xn
                                                         in  Proj tc i (S.Var x)
                                          Nothing     -> S.Apply f xn
                               tell [(a,lt)]
                               return (Var a)

    T.Let (T.Local x _) e1 e2 ->
      do s1 <- toSimple' e1
         let subst = replace x s1
         let subst_lets lets = [ (x,substSimple subst lt) | (x,lt) <- lets ]
         fmap (substSimple subst) (censor subst_lets (toSimple' e2))

    _ -> error $ "toSimple': " ++ ppRender e0

replace :: Name a => a -> Simple a -> a -> Simple a
replace x s y | y == x    = s
              | otherwise = Var y


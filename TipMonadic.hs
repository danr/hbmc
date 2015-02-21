{-# LANGUAGE ViewPatterns #-}
module TipMonadic where

import Tip as T
import Tip.Pretty (ppRender)
import Tip.Fresh

import TipTarget as H
import TipLift

import Control.Applicative


class (Name a,Call a) => Monadic a where
  memofun   :: a -> a
  construct :: a -> a -- the translation of constructors
  conLabel  :: a -> a -- the label for constructors
  returnH   :: a
  newCall   :: a
  new       :: a
  waitCase  :: a
  con       :: a -- Con
  memcpy    :: a
  whenH     :: a
  unlessH   :: a
  (=?)      :: a

returnExpr :: Monadic a => H.Expr a -> H.Expr a
returnExpr e = H.Apply returnH [e]

newExpr :: Monadic a => H.Expr a
newExpr = H.Apply new []

thenReturn :: Monadic a => [H.Stmt a] -> a -> H.Expr a
ss `thenReturn` x = mkDo ss (returnExpr (var x))

(>>>) :: Monadic a => a -> a -> H.Expr a
a >>> b = H.Apply memcpy [var a,var b]

trExpr :: Monadic a => T.Expr a -> Fresh (H.Expr a)
trExpr e0 =
  case e0 of
    h T.:@: es ->
      do (xs,ss) <-
           unzip <$> sequence
             [ do x <- fresh; (,) x . H.Bind x <$> trExpr e | e <- es ]
         case h of
           T.Gbl (T.Global f _ _ T.FunctionNS) ->
             return (mkDo ss (H.Apply (memofun f) (map H.var xs)))
           T.Gbl (T.Global f _ _ T.ConstructorNS) ->
             return (mkDo ss (H.Apply (construct f) (map H.var xs)))
           _ -> error (ppRender h)
           -- TODO: handle call/cancel appropriately


    T.Lcl (T.Local x _) -> return (var x)

    Let (T.Local x _) b e ->
      do b' <- trExpr b
         e' <- trExpr e
         return (mkDo [Bind x b'] e')

    T.Match (collectLets -> (bs,scrut_expr)) alts ->
      do scrut <- fresh
         scrut_tr <- trExpr scrut_expr
         scrut_i <- fresh

         calls <- sequence
           [ do store <- fresh
                res <- fresh
                e' <- trExpr e
                -- x <- newCall $ \ (a1,..,an) -> \ store -> res <- [[ e ]]; res >>> store
                return $
                  H.Bind (lcl_name x)
                    (H.Apply newCall
                      [H.Lam (H.TupPat (map (H.VarPat . lcl_name) args))
                        (H.Lam (H.VarPat store)
                          (mkDo [H.Bind res e'] (res >>> store)))])
           | (x,T.Lam args e) <- bs
           ]

         r <- fresh
         c <- fresh
         v <- fresh

         let ctors = [ k | Case (T.ConPat (Global k _ _ _) _) _ <- alts ]
         alts' <- mapM (trAlt c r ctors) alts

         -- do r <- new
         --    x <- [[ scrut ]]
         --    waitCase x $ \ (Con c v) ->
         --      [[ calls ]]
         --      when (c =? K1) $ do
         --        y <- [[ br1 ]]
         --        y >>> r
         --      ...
         --    return r
         return $
           mkDo
             [ H.Bind scrut_i scrut_tr
             , H.Stmt (scrut_i >>> scrut)
             , H.Bind r newExpr
             , H.Stmt $ H.Apply waitCase [var scrut,H.Lam (H.ConPat con [VarPat c,VarPat v]) (
                 mkDo (calls ++ alts') Noop
               )]
             ]
             (returnExpr (var r))


    T.Lam{} -> error "trExpr lam"

    T.Quant{} -> error "trExpr quant... make these new ?"

trAlt :: Monadic a => a -> a -> [a] -> T.Case a -> Fresh (H.Stmt a)
trAlt c r cons (Case pat rhs) =
  do body <- do rhs' <- trExpr rhs
                y <- fresh
                return (mkDo [Bind y rhs'] (y >>> r))
     let
       cond =
         case pat of
           Default -> H.Apply unlessH [List [H.Apply (=?) [var c,var (conLabel k)] | k <- cons],body]
           T.ConPat (Global k _ _ _) _ -> H.Apply whenH [H.Apply (=?) [var c,var (conLabel k)],body]
           _ -> error (show pat)
     return (Stmt cond)

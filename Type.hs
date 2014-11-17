{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving #-}
module Main where

import Symbolic
import Control.Monad

--------------------------------------------------------------------------------

data N = S | Z
 deriving ( Ord, Eq, Show )

newtype DNat = DNat (Data N (Lift DNat))
 deriving ( Show, Choice, Equal )

dnat :: Int -> DNat
dnat 0 = DNat (Con (val Z) UNR)
dnat n = suck (dnat (n-1))

suck n = DNat (Con (val S) (The n))

instance Argument N where
  argument Z _ = []
  argument S x = [x]

instance Value DNat where
  type Type DNat = Int
  
  get (DNat (Con cn args)) =
    do l <- get cn
       case (l, args) of
         (Z, _)     -> return 0
         (S, The n) -> (+1) `fmap` get n

{-
newDNat :: Int -> H DNat
newDNat k =
  do cn <- newVal ([Z] ++ [S | k > 0])
     choose cn $ \n -> case n of
       Z -> return (dnat 0)
       S -> do n <- newDNat (k-1)
               return (suck n)
-}

newDNat :: Int -> H DNat
newDNat 0 = return (dnat 0)
newDNat k = do b <- newBit
               n' <- newDNat (k-1)
               iff b n' (suck n')

--------------------------------------------------------------------------------

data Typ = Typ :-> Typ | A | B | C
 deriving ( Eq, Ord, Show )

data T = TArrow | TA | TB | TC
 deriving ( Eq, Ord, Show )

newtype DTyp = DTyp (Data T (Lift (DTyp,DTyp)))
 deriving ( Show, Choice, Equal )

a `arrow` b = DTyp (Con (val TArrow) (The (a,b)))
tcon t      = DTyp (Con (val t) UNR)

instance Argument T where
  argument TArrow (Tuple [a,b]) = [a,b]
  argument TA     _             = []
  argument TB     _             = []
  argument TC     _             = []
  argument x y = error (show (x,y))

instance Value DTyp where
  type Type DTyp = Typ
  
  get (DTyp (Con cn args)) =
    do l <- get cn
       case (l, args) of
         (TArrow, The (a,b)) -> liftM2 (:->) (get a) (get b)
         (TA, _) -> return A
         (TB, _) -> return B
         (TC, _) -> return C

newDTyp :: Int -> H DTyp
newDTyp k =
  do cn <- newVal ([TA,TB,TC] ++ [ TArrow | k > 0 ])
     choose cn $ \c ->
       case c of
         TArrow -> do a <- newDTyp (k-1)
                      b <- newDTyp (k-1)
                      return (a `arrow` b)
         _ -> return (tcon c)

--------------------------------------------------------------------------------

data Expr
  = Var Int
  | App Expr Expr Typ
  | Lam Expr
 deriving ( Eq, Ord )

instance Show Expr where
  show = showExpr []

showExpr env (Var v)     = env !! v
showExpr env (App a b t) = "(" ++ showExpr env a ++ " " ++ showExpr env b ++ ")"
showExpr env (Lam e)     = "(\\" ++ v ++ " -> " ++ showExpr (v:env) e ++ ")"
 where
  v = head [ x | x <- vars, x `notElem` env ]
  vars = [ "x", "y", "z", "v", "w" ] ++ [ "x" ++ show i | i <- [1..] ]

data E = EVar | EApp | ELam
 deriving ( Eq, Ord, Show )

newtype DExpr = DExpr (Data E (Lift DNat,Lift DExpr,Lift (DExpr,DTyp)))
 deriving ( Show, Choice, Equal )

evar v     = DExpr (Con (val EVar) (The v, UNR, UNR))
eapp a b t = DExpr (Con (val EApp) (UNR, The a, The (b, t)))
elam e     = DExpr (Con (val ELam) (UNR, The e, UNR))

instance Argument E where
  argument EVar (Tuple [v, _, _])            = [v]
  argument EApp (Tuple [_, f, Tuple [x, t]]) = [f, x, t]
  argument ELam (Tuple [_, e, _])            = [e]

instance Value DExpr where
  type Type DExpr = Expr
  
  get (DExpr (Con cn args)) =
    do l <- get cn
       case (l, args) of
         (EVar, (The v, _, _))          -> liftM Var (get v)
         (EApp, (_, The f, The (x, t))) -> liftM3 App (get f) (get x) (get t)
         (ELam, (_, The e, _))          -> liftM Lam (get e)

--------------------------------------------------------------------------------

tcheck :: [Typ] -> Expr -> Typ -> Bool
tcheck env (Var v)      t = env !! v == t
tcheck env (App f x t1) t = tcheck env f (t1 :-> t) && tcheck env x t1
tcheck env (Lam e)      t = case t of
                              t1 :-> t2 -> tcheck (t1:env) e t2
                              _         -> False

--------------------------------------------------------------------------------

sindex :: Choice a => List a -> DNat -> H a
sindex (List xs) (DNat i) =
  switch xs $ \cxs axs ->
    case (cxs, axs) of
      (Nil, _) -> impossible "sindex"
      (Cons, The (y,ys)) ->
        switch i $ \ci ai ->
          case (ci, ai) of
            (Z, _)     -> return y
            (S, The j) -> sindex ys j

scheck :: List DTyp -> DExpr -> DTyp -> H Bit
scheck env (DExpr a@(Con cn _)) t@(DTyp td) =
  do (env1,expr1,t1) <- switch a $ \ca aa ->
       case (ca, aa) of
         (EVar, _) ->
           do return (UNR, UNR, UNR)
         
         (EApp, (_, The f, The (_, t1))) ->
           do return (The env, The f, The (t1 `arrow` t))
         
         (ELam, (_, The e, _)) ->
           switch td $ \ct at ->
             case (ct, at) of
               (TArrow, The (t1,t2)) -> return (The (cons t1 env), The e, The t2)
               _                     -> return (UNR, UNR, UNR)

     c <- orl [cn =? EApp, cn =? ELam]
     res <- lift ((do env' <- peek env1
                      e'   <- peek expr1
                      t'   <- peek t1
                      scheck env' e' t') `withExtra` c)

     switch a $ \ca aa ->
       case (ca, aa) of
         (EVar, (The v, _, _)) ->
           do t' <- sindex env v
              equal t' t
         
         (EApp, (_, _, The (x, t1))) ->
           do b1 <- peek res
              b2 <- scheck env x t1
              andl [b1,b2]
         
         (ELam, _) ->
           switch td $ \ct at ->
             case (ct, at) of
               (TArrow, _) -> peek res
               _           -> return ff

--------------------------------------------------------------------------------

newExpr :: Int -> Int -> H DExpr
newExpr k env | k < 0 =
  do impossible "newExpr"

newExpr k env =
  do cn <- newVal ([EVar] ++ [ c | k > 0, c <- [EApp, ELam] ])
     e1 <- lift (newExpr (k-1) (env+1) `withExtra` nt (cn =? EVar))
     choose cn $ \c ->
       case c of
         EVar -> liftM evar (newDNat env)
         EApp -> do a <- peek e1
                    b <- newExpr (k-1) env
                    t <- newDTyp (k+env)
                    return (eapp a b t)
         ELam -> do a <- peek e1
                    return (elam a)
  
--------------------------------------------------------------------------------

main = runH $
  do io $ putStrLn "Generating expression..."
     e <- newExpr 6 0
     io $ putStrLn "Generating scheck..."
     b <- scheck nil e ((tcon TB `arrow` tcon TC) `arrow` ((tcon TA `arrow` tcon TB) `arrow` (tcon TA `arrow` tcon TC)))
     --b <- scheck nil e ((tcon TA `arrow` (tcon TA `arrow` tcon TB)) `arrow` (tcon TA `arrow` tcon TB))
     --b <- scheck nil e (tcon TA `arrow` (tcon TB `arrow` tcon TA))
     addClause [b]
     io $ putStrLn "Solving..."
     check
     io $ putStrLn "Done!"
     (io . print) =<< get e
     


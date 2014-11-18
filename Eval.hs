{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving #-}
module Main where

import Symbolic
import Control.Monad

--------------------------------------------------------------------------------

data N = S | Z
 deriving ( Ord, Eq, Show )

newtype DNat = DNat (Data N (Lift DNat))
 deriving ( Choice, Equal )

instance Show DNat where
  show (DNat d) = show d

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

newDNat :: Int -> H DNat
newDNat k =
  do cn <- newVal ([Z] ++ [S | k > 0])
     choose cn $ \n -> case n of
       Z -> return (dnat 0)
       S -> do n <- newDNat (k-1)
               return (suck n)

{-
-- bad, bad function!
newDNat :: Int -> H DNat
newDNat 0 = return (dnat 0)
newDNat k = do b <- newBit
               n' <- newDNat (k-1)
               iff b n' (suck n')
-}

--------------------------------------------------------------------------------

data Expr
  = Var  Int
  | App2 Int Expr Expr
  | Case Int Expr Expr
  | Nl
  | Cns      Expr Expr
 deriving ( Eq, Ord )

instance Show Expr where
  show = showExpr []

showExpr env (Var v)      = env !! v
showExpr env (App2 f a b) = "f" ++ show f ++ "(" ++ showExpr env a ++ "," ++ showExpr env b ++ ")"
showExpr env (Case x a b) = "case " ++ env !! x ++ " of { [] -> " ++ showExpr env a ++ "; "
                         ++ y ++ ":" ++ ys ++ " -> " ++ showExpr (("["++y++"]"):ys:env) b ++ " }"
 where
  y:ys:_ = new env
showExpr env Nl           = "[]"
showExpr env (Cns a b)    = "(" ++ showExpr env a ++ " `cns` " ++ showExpr env b ++ ")"

new :: [String] -> [String]
new env = [ x | x <- vars, x `notElem` env ]
 where
  vars = [ "x", "y", "z", "v", "w" ] ++ [ "x" ++ show i | i <- [1..] ]

data E = EVar | EApp2 | ECase | ENl | ECns
 deriving ( Eq, Ord, Show )

newtype DExpr = DExpr (Data E (Lift DNat,Lift DExpr,Lift DExpr))
 deriving ( Choice, Equal )

instance Show DExpr where
  show (DExpr d) = show d

evar  v     = DExpr (Con (val EVar)  (The v, UNR,   UNR))
eapp2 f a b = DExpr (Con (val EApp2) (The f, The a, The b))
ecase x a b = DExpr (Con (val ECase) (The x, The a, The b))
enl         = DExpr (Con (val ENl)   (UNR,   UNR,   UNR))
ecns    a b = DExpr (Con (val ECns)  (UNR,   The a, The b))

instance Argument E where
  argument EVar  (Tuple [v, _, _]) = [v]
  argument EApp2 (Tuple [f, a, b]) = [f, a, b]
  argument ECase (Tuple [x, a, b]) = [x, a, b]
  argument ENl   _                 = []
  argument ECns  (Tuple [_, a, b]) = [a, b]

instance Value DExpr where
  type Type DExpr = Expr
  
  get (DExpr (Con cn args)) =
    do l <- get cn
       case (l, args) of
         (EVar,  (The v, _, _))         -> liftM  Var  (get v)
         (EApp2, (The f, The a, The b)) -> liftM3 App2 (get f) (get a) (get b)
         (ECase, (The x, The a, The b)) -> liftM3 Case (get x) (get a) (get b)
         (ENl,   _)                     -> return Nl
         (ECns,  (_,     The a, The b)) -> liftM2 Cns  (get a) (get b)

--------------------------------------------------------------------------------

seval :: Int -> List DExpr -> List (List Nat) -> DExpr -> H (List Nat)
seval d p env e | d < 0 =
  impossible "seval depth"

seval d p env (DExpr de@(Con cn (lx, la, lb))) =
  do check
     
     c <- orl [cn =? EVar, cn =? ECase]
     valx <- lift ((peek lx >>= sindex env) `withExtra` c)
     
     (ca,cb,lenv2) <- switch de $ \ce ae ->
       case (ce, ae) of
         (ECase, (The x, The a, The b)) ->
           do List da <- peek valx
              switch da $ \ca aa ->
                case (ca, aa) of
                  (Nil, _)            -> return (tt,ff,UNR)
                  (Cons, The (y, ys)) -> return (ff,tt,The (cons (cons y nil) (cons ys env)))

         (EApp2, (_, The a, The b)) ->
           do return (tt,tt,The env)
         
         (ECns, (_, The a, The b)) ->
           do return (tt,tt,The env)
         
         _ ->
           do return (ff,ff,UNR)

     ea <- lift ((do a <- peek la
                     seval d p env a) `withExtra` ca)
     eb <- lift ((do env2 <- peek lenv2
                     b <- peek lb
                     seval d p env2 b) `withExtra` cb)

     switch de $ \ce ae ->
       case (ce, ae) of
         (EVar, _) ->
           do peek valx
         
         (EApp2, (The f, _, _)) ->
           do a <- peek ea
              b <- peek eb
              e' <- sindex p f
              seval (d-1) p (cons a (cons b nil)) e' -- dangerous recursion, decrease d
         
         (ECase, _) ->
           do List da <- peek valx
              switch da $ \ca aa ->
                case (ca, aa) of
                  (Nil, _)  -> peek ea
                  (Cons, _) -> peek eb

         (ENl, _) ->
           do return nil
         
         (ECns, _) ->
           do a <- peek ea
              b <- peek eb
              ha <- shead a
              return (cons ha b)

shead :: List Nat -> H Nat
shead (List xs) =
  switch xs $ \cxs axs ->
    case (cxs, axs) of
      (Nil, _)          -> return (fromInt 0)
      (Cons, The (y,_)) -> return y

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

--------------------------------------------------------------------------------

newExpr :: Bool -> Int -> Int -> Int -> H DExpr
newExpr cs p e k | k < 0 =
  do impossible "newExpr"

newExpr cs p e k =
  do cn <- newVal ([EVar, ENl] ++ [ c | k > 0, c <- [EApp2, ECns]] ++ [ECase | k > 0 && cs ])
     c <- orl [cn =? EApp2, cn =? ECase, cn =? ECns]
     lab <- lift ((do a <- newExpr False p e (k-1)
                      b <- newExpr False p (if cs then e+2 else e) (k-1)
                      return (a,b)) `withExtra` c)
     nv <- newDNat e
     nf <- newDNat p
     choose cn $ \c ->
       case c of
         EVar  -> return (evar nv)
         EApp2 -> peek lab >>= \(a,b) -> return $ eapp2 nf a b
         ECase -> peek lab >>= \(a,b) -> return $ ecase nv a b
         ENl   -> return enl
         ECns  -> peek lab >>= \(a,b) -> return $ ecns a b

--------------------------------------------------------------------------------

fromList :: [Integer] -> List Nat
fromList []     = nil
fromList (x:xs) = cons (fromInt x) (fromList xs)

main = runH $
  do io $ putStrLn "Creating program..."
     let numFuns = 1 -- number of functions in the program
         depEval = 5 -- maximum number of function calls per test
         depExpr = 3 -- maximum depth of the RHS of a function definition
     es <- sequence [ newExpr True i 1 depExpr | i <- [0..numFuns-1] ]
     --let es = [ecase (dnat 0) (evar (dnat 1)) (ecns (evar (dnat 0)) (eapp2 (dnat 0) (evar (dnat 1)) (evar (dnat 3))))]
     let p = foldr cons nil es
     
     let f xs ys = reverse xs
         --f xs ys = if null xs then [] else [last xs]
         --f xs ys = if null xs then ys else reverse ys
     
     let test xs ys =
           do zs1 <- seval depEval p (cons (fromList xs) (cons (fromList ys) nil))
                                     (eapp2 (dnat (numFuns-1)) (evar (dnat 0)) (evar (dnat 1)))
              let zs2 = fromList (f xs ys)
              b <- equal zs1 zs2
              addClause [b]
     
     io $ putStrLn "Adding tests..."
     test [1,2,3,4] [] -- [5,6,7]
     --test [] [4,5,6]
     --test [1,2] [3,2]

     io $ putStrLn "Solving..."
     check
     
     fs <- sequence [ get e | e <- es ]
     let text = [ "f" ++ show i ++ "(a1,a2) = " ++ showExpr ["a1","a2"] e
                | (i,e) <- [0..] `zip` fs
                ]
     io $ putStr $ unlines text
     io $ writeFile "Found.hs" (unlines ("cns [] xs = 0:xs":"cns (x:_) xs = x:xs":text))


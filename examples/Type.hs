{-# LANGUAGE PatternGuards #-}
module Type where

import Tip.DSL

data Expr = App Expr Expr Ty | Lam Expr | Var Nat

data Ty = Ty `Arr` Ty | A | B | C deriving Eq

infixr `Arr`

label :: Int -> a -> a
label x s = s

annd :: Bool -> Bool -> Bool
True  `annd` b = b
False `annd` _ = False

eq :: Ty -> Ty -> Bool
A `eq` A = True
B `eq` B = True
C `eq` C = True
(u1 `Arr` v1) `eq` (u2 `Arr` v2) = (u1 `eq` u2) `annd` (v1 `eq` v2)
_ `eq` _ = False

tc :: [Ty] -> Expr -> Ty -> Bool
tc env (Var x)      t = case env `index` x of Just tx -> tx `eq` t
                                              Nothing -> False
tc env (App f x tx) t            = label 1 (tc env f (tx `Arr` t)) `annd` tc env x tx
tc env (Lam e)      (tx `Arr` t) = label 1 (tc (tx:env) e t)
tc _   _            _ = False

-- prop_A0 e = tc [] e ((A `Arr` A `Arr` B) `Arr` (B `Arr` C) `Arr` (A `Arr` C)) =:= False
--
-- prop_A1 e = tc [] e ((A `Arr` B) `Arr` (B `Arr` B `Arr` C) `Arr` (A `Arr` C)) =:= False

-- prop_A2 e = tc [] e ((A `Arr` A `Arr` B) `Arr` (B `Arr` B `Arr` C) `Arr` (A `Arr` C)) =:= False

-- prop_B e  = tc [] e ((B `Arr` C) `Arr` (A `Arr` B) `Arr` (A `Arr` C)) =:= False

prop_I e  = tc [] e (A `Arr` A) =:= False

prop_K e  = tc [] e (A `Arr` B `Arr` A) =:= False

prop_S e  = tc [] e ((A `Arr` B `Arr` C) `Arr` (A `Arr` B) `Arr` A `Arr` C) =:= False

prop_W e  = tc [] e ((A `Arr` A `Arr` B) `Arr` (A `Arr` B)) =:= False

prop_C e  = tc [] e ((A `Arr` B `Arr` C) `Arr` (B `Arr` A `Arr` C)) =:= False

prop_M e  = tc [] e ((A `Arr` B) `Arr` (A `Arr` A `Arr` B)) =:= False

prop_N e  = tc [] e (A `Arr` (A `Arr` A) `Arr` A) =:= False

prop_D e  = tc [] e ((A `Arr` B) `Arr` (A `Arr` B)) =:= False

prop_K1 e = tc [] e (A `Arr` B `Arr` B) =:= False


-- nats --

data Nat = S Nat | Z
  deriving Show

index :: [a] -> Nat -> Maybe a
index (x:xs) Z     = Just x
index (x:xs) (S n) = index xs n
index []     _     = Nothing

-- show --

instance Show Expr where
  show = showExpr []

showExpr env (Var v)     = case env `index` v of Just x -> x; Nothing -> "?"
showExpr env (App a b t) = "(" ++ showExpr env a ++ " " ++ showExpr env b ++ ")"
showExpr env (Lam e)     = "(\\" ++ v ++ " -> " ++ showExpr (v:env) e ++ ")"
 where
  v = head [ x | x <- vars, x `notElem` env ]
  vars = [ "x", "y", "z", "v", "w" ] ++ [ "x" ++ show i | i <- [1..] ]


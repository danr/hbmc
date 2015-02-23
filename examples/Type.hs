{-# LANGUAGE PatternGuards #-}
module Type where

import Tip.DSL
import Prelude hiding ((&&))

label :: Int -> a -> a
label c x = x

data Expr = App Expr Expr Ty | Lam Expr | Var Nat

data Ty = Ty :-> Ty | A | B | C deriving Eq

infixr 9 :->
infix  4 ===
infixr 3 &&

(===) :: Ty -> Ty -> LazyBool
A === A = true
B === B = true
C === C = true
(a :-> x) === (b :-> y) = a === b && x === y
_ === _ = false

false = LFalse
true = LTrue U
data LazyBool = LTrue U | LFalse
data U = U

(&&) :: LazyBool -> LazyBool -> LazyBool
LTrue{} && b = b
LFalse  && b = false

tc :: [Ty] -> Expr -> Ty -> LazyBool
tc env (Var x)      t | Just tx <- env `index` x = tx === t
tc env (App f x tx) t          = label 1 (tc env f (tx :-> t)) && (tc env x tx)
tc env (Lam e)      (tx :-> t) = label 1 (tc (tx:env) e t)
tc _   _            _ = LFalse

-- prop_A0 e = tc [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= false
--
-- prop_A1 e = tc [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= false
--
-- prop_A2 e = tc [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= false
--
-- prop_B e  = tc [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= false
--
-- prop_I e  = tc [] e (A :-> A) =:= false
--
-- prop_K e  = tc [] e (A :-> B :-> A) =:= false
--
prop_S e  = tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= false
--
-- prop_W e  = tc [] e ((A :-> A :-> B) :-> (A :-> B)) =:= false
--
-- prop_C e  = tc [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= false
--
-- prop_M e  = tc [] e ((A :-> B) :-> (A :-> A :-> B)) =:= false
--
-- prop_N e  = tc [] e (A :-> (A :-> A) :-> A) =:= false
--
-- prop_D e  = tc [] e ((A :-> B) :-> (A :-> B)) =:= false
--
-- prop_K1 e = tc [] e (A :-> B :-> B) =:= false


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


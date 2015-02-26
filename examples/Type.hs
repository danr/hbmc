{-# LANGUAGE PatternGuards #-}
module Type where

import HBMC
import Prelude hiding ((&&))

data Expr = App Expr Expr Ty | Lam Expr | Var Nat

data Ty = Ty :-> Ty | A | B | C deriving Eq

infixr 9 :->
infix  4 ===
infixr 3 &&

(===) :: Ty -> Ty -> Bool
A === A = True
B === B = True
C === C = True
(a :-> x) === (b :-> y) = a === b && x === y -- can flip these, too!
_ === _ = False

(&&) :: Bool -> Bool -> Bool
True  && b = b
False && _ = False

nf :: Expr -> Bool
nf (App Lam{} _ _) = False
nf (App e x _) = label 1 (nf e) && nf x
nf (Lam e)     = label 1 (nf e)
nf Var{}       = True

tc1,tc2,tc3,tc4 :: [Ty] -> Expr -> Ty -> Bool

tc1 env (Var x)      t | Just tx <- env `index` x = tx === t
tc1 env (App f x tx) t          = label 1 (tc1 env f (tx :-> t)) && (tc1 env x tx)
tc1 env (Lam e)      (tx :-> t) = label 1 (tc1 (tx:env) e t)
tc1 _   _            _ = False

tc2 env (Var x)      t | Just tx <- env `index` x = tx === t
tc2 env (App f x tx) t          = label 1 (tc2 env x tx) && (tc2 env f (tx :-> t))
tc2 env (Lam e)      (tx :-> t) = label 1 (tc2 (tx:env) e t)
tc2 _   _            _ = False

tc3 env (Var x)      t | Just tx <- env `index` x = tx === t
tc3 env (App x f tx) t          = label 1 (tc3 env f (tx :-> t)) && (tc3 env x tx)
tc3 env (Lam e)      (tx :-> t) = label 1 (tc3 (tx:env) e t)
tc3 _   _            _ = False

tc4 env (Var x)      t | Just tx <- env `index` x = tx === t
tc4 env (App x f tx) t          = label 1 (tc4 env x tx) && (tc4 env f (tx :-> t))
tc4 env (Lam e)      (tx :-> t) = label 1 (tc4 (tx:env) e t)
tc4 _   _            _ = False

tc1_S0 e = tc1 [] e (A :-> A) =:= False
tc1_S1 e = tc1 [] e (A :-> (A :-> A) :-> A) =:= False
tc1_S2 e = tc1 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc1_S3 e = tc1 [] e (A :-> B :-> B) =:= False
tc1_S4 e = tc1 [] e (A :-> B :-> A) =:= False
tc1_S5 e = tc1 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc1_M0 e = tc1 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc1_M1 e = tc1 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc1_M2 e = tc1 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc1_M3 e = tc1 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc1_L0 e = tc1 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc1_L1 e = tc1 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc1_L2 e = tc1 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc2_S0 e = tc2 [] e (A :-> A) =:= False
tc2_S1 e = tc2 [] e (A :-> (A :-> A) :-> A) =:= False
tc2_S2 e = tc2 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc2_S3 e = tc2 [] e (A :-> B :-> B) =:= False
tc2_S4 e = tc2 [] e (A :-> B :-> A) =:= False
tc2_S5 e = tc2 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc2_M0 e = tc2 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc2_M1 e = tc2 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc2_M2 e = tc2 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc2_M3 e = tc2 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc2_L0 e = tc2 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc2_L1 e = tc2 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc2_L2 e = tc2 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc3_S0 e = tc3 [] e (A :-> A) =:= False
tc3_S1 e = tc3 [] e (A :-> (A :-> A) :-> A) =:= False
tc3_S2 e = tc3 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc3_S3 e = tc3 [] e (A :-> B :-> B) =:= False
tc3_S4 e = tc3 [] e (A :-> B :-> A) =:= False
tc3_S5 e = tc3 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc3_M0 e = tc3 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc3_M1 e = tc3 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc3_M2 e = tc3 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc3_M3 e = tc3 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc3_L0 e = tc3 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc3_L1 e = tc3 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc3_L2 e = tc3 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc4_S0 e = tc4 [] e (A :-> A) =:= False
tc4_S1 e = tc4 [] e (A :-> (A :-> A) :-> A) =:= False
tc4_S2 e = tc4 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc4_S3 e = tc4 [] e (A :-> B :-> B) =:= False
tc4_S4 e = tc4 [] e (A :-> B :-> A) =:= False
tc4_S5 e = tc4 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc4_M0 e = tc4 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc4_M1 e = tc4 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc4_M2 e = tc4 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc4_M3 e = tc4 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc4_L0 e = tc4 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc4_L1 e = tc4 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc4_L2 e = tc4 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc1n_S0 e = nf e =:= True ==> tc1 [] e (A :-> A) =:= False
tc1n_S1 e = nf e =:= True ==> tc1 [] e (A :-> (A :-> A) :-> A) =:= False
tc1n_S2 e = nf e =:= True ==> tc1 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc1n_S3 e = nf e =:= True ==> tc1 [] e (A :-> B :-> B) =:= False
tc1n_S4 e = nf e =:= True ==> tc1 [] e (A :-> B :-> A) =:= False
tc1n_S5 e = nf e =:= True ==> tc1 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc1n_M0 e = nf e =:= True ==> tc1 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc1n_M1 e = nf e =:= True ==> tc1 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc1n_M2 e = nf e =:= True ==> tc1 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc1n_M3 e = nf e =:= True ==> tc1 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc1n_L0 e = nf e =:= True ==> tc1 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc1n_L1 e = nf e =:= True ==> tc1 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc1n_L2 e = nf e =:= True ==> tc1 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc2n_S0 e = nf e =:= True ==> tc2 [] e (A :-> A) =:= False
tc2n_S1 e = nf e =:= True ==> tc2 [] e (A :-> (A :-> A) :-> A) =:= False
tc2n_S2 e = nf e =:= True ==> tc2 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc2n_S3 e = nf e =:= True ==> tc2 [] e (A :-> B :-> B) =:= False
tc2n_S4 e = nf e =:= True ==> tc2 [] e (A :-> B :-> A) =:= False
tc2n_S5 e = nf e =:= True ==> tc2 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc2n_M0 e = nf e =:= True ==> tc2 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc2n_M1 e = nf e =:= True ==> tc2 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc2n_M2 e = nf e =:= True ==> tc2 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc2n_M3 e = nf e =:= True ==> tc2 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc2n_L0 e = nf e =:= True ==> tc2 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc2n_L1 e = nf e =:= True ==> tc2 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc2n_L2 e = nf e =:= True ==> tc2 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc3n_S0 e = nf e =:= True ==> tc3 [] e (A :-> A) =:= False
tc3n_S1 e = nf e =:= True ==> tc3 [] e (A :-> (A :-> A) :-> A) =:= False
tc3n_S2 e = nf e =:= True ==> tc3 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc3n_S3 e = nf e =:= True ==> tc3 [] e (A :-> B :-> B) =:= False
tc3n_S4 e = nf e =:= True ==> tc3 [] e (A :-> B :-> A) =:= False
tc3n_S5 e = nf e =:= True ==> tc3 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc3n_M0 e = nf e =:= True ==> tc3 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc3n_M1 e = nf e =:= True ==> tc3 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc3n_M2 e = nf e =:= True ==> tc3 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc3n_M3 e = nf e =:= True ==> tc3 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc3n_L0 e = nf e =:= True ==> tc3 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc3n_L1 e = nf e =:= True ==> tc3 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc3n_L2 e = nf e =:= True ==> tc3 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

tc4n_S0 e = nf e =:= True ==> tc4 [] e (A :-> A) =:= False
tc4n_S1 e = nf e =:= True ==> tc4 [] e (A :-> (A :-> A) :-> A) =:= False
tc4n_S2 e = nf e =:= True ==> tc4 [] e ((A :-> B) :-> (A :-> B)) =:= False
tc4n_S3 e = nf e =:= True ==> tc4 [] e (A :-> B :-> B) =:= False
tc4n_S4 e = nf e =:= True ==> tc4 [] e (A :-> B :-> A) =:= False
tc4n_S5 e = nf e =:= True ==> tc4 [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

tc4n_M0 e = nf e =:= True ==> tc4 [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False
tc4n_M1 e = nf e =:= True ==> tc4 [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False
tc4n_M2 e = nf e =:= True ==> tc4 [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
tc4n_M3 e = nf e =:= True ==> tc4 [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

tc4n_L0 e = nf e =:= True ==> tc4 [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
tc4n_L1 e = nf e =:= True ==> tc4 [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
tc4n_L2 e = nf e =:= True ==> tc4 [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

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


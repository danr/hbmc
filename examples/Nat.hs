module Nat where

import Prelude hiding ((+),(*),(-),(<))
import Tip.DSL

data Nat = Z | S Nat deriving (Eq,Ord)

infixl 6 -
infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

-- | Truncated subtraction
(-) :: Nat -> Nat -> Nat
S n - S m = n - m
S m - Z   = S m
Z   - Z   = Z
Z   - _   = Z

(<) :: Nat -> Nat -> Bool
Z < _     = True
Z{} < Z   = False
S{} < Z   = False
S n < S m = n < m

-- plus_idem x = x + x =:= x
-- mul_idem  x = x * x =:= x
-- plus_not_idem x = x + x =:= x ==> True =:= False

silly x y z = x * (y + z) =:= (x * y) + z

sub_comm  x y   = x - y =:= y - x
sub_assoc x y z = x - (y - z) =:= (x - y) - z

not_trans x y z = x < y =:= True ==> y < z =:= True ==> x < z =:= False


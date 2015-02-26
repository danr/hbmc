module Deriv where

import HBMC
import Prelude (Bool(..),Show(..),(&&))
import qualified Prelude as P

data N = Z | S N deriving Show

data E = N N | E :+: E | E :*: E | X deriving Show

d :: E -> E
d (f :+: g) = label 1 (d f) :+: label 2 (d g)
d (f :*: g) = (label 1 (d f) :*: g) :+: (f :*: label 2 (d g))
d X         = N (S Z)
d N{}       = N Z

infix 4 :*:
infix 3 :+:

(===) :: N -> N -> Bool
Z   === Z   = True
Z{} === S{} = False
S{} === Z{} = False
S n === S m = n === m

eqE :: E -> E -> Bool
N n       `eqE` N m       = n === m
(a :+: b) `eqE` (c :+: d) = label 1 (a `eqE` c) && label 2 (b `eqE` d)
(a :+: b) `eqE` (c :*: d) = label 1 (a `eqE` c) && label 2 (b `eqE` d)
X         `eqE` X         = True
_         `eqE` _         = False

-- FLAGS: copt
opt :: E -> E
opt (N Z :*: e)       = N Z
opt (e :*: N Z)       = N Z
opt (N (S Z) :*: e)   = e
opt (e :*: N (S Z))   = e
opt (N Z     :+: e)   = e
opt (e :+: N Z)       = e
opt (N a :+: N b)     = N (a + b)
opt (N a :*: N b)     = N (a * b)
opt (a :+: b) | a `eqE` b = N (S (S Z)) :*: label 1 (opt a)
opt ((a :+: b) :+: c) = label 1 (opt (a :+: (b :+: c)))
opt ((a :*: b) :*: c) = label 1 (opt (a :*: (b :*: c)))
opt (a :+: b)         = label 1 (opt a) :+: label 2 (opt b)
opt (a :*: b)         = label 1 (opt a) :*: label 2 (opt b)
opt e                 = e

eval :: E -> N -> N
eval X         x = x
eval (a :+: b) x = label 1 (eval a x) + label 1 (eval b x)
eval (a :*: b) x = label 1 (eval a x) * label 1 (eval b x)
eval (N n)     _ = n

(+) :: N -> N -> N
S n + m = S (n + m)
Z   + m = m

(*) :: N -> N -> N
S n * m = m + (n * m)
Z   * m = Z

prop1 e = opt (d e) =:= opt (N (S (S Z)) :+: (X :+: X)) ==> True =:= False

prop2 e = opt (d e) =:= X :*: X :+: X :*: (X :+: X) ==> True =:= False

prop3 e x = eval e x =:= eval (opt e) x

prop4 e = opt (d e) =:= opt (d (opt e))

propm4 e = opt (d e) =:= X :*: (X :*: X) :+: X :*: (X :*: X :+: X :*: (X :+: X)) ==> True =:= False

propm5 e = opt (d e) =:= X :*: (X :*: (X :*: X)) :+: X :*: (X :*: (X :*: X) :+: X :*: (X :*: X :+: X :*: (X :+: X))) ==> True =:= False

propm6 e = opt (d e) =:= X :*: (X :*: (X :*: (X :*: X))) :+: X :*: (X :*: (X :*: (X :*: X)) :+: X :*: (X :*: (X :*: X) :+: X :*: (X :*: X :+: X :*: (X :+: X)))) ==> True =:= False

muls 0 = N (S Z)
muls 1 = X
muls n = X :*: muls (n P.- 1)


module Deriv where

import HBMC
import Prelude (Bool(..),Show(..))

data N = Z | S N deriving Show

data E = N N | E :+: E | E :*: E | X deriving Show

d :: E -> E
d (f :+: g) = d f :+: d g
d (f :*: g) = (d f :*: g) :+: (f :*: d g)
d X         = N (S Z)
d N{}       = N Z

infix 4 :*:
infix 3 :+:

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
opt (a :+: N x)       = opt (N x :+: a)
opt (a :*: N x)       = opt (N x :*: a)
opt (a :+: X)         = opt (X :+: a)
opt (a :*: X)         = opt (X :*: a)
opt (a :+: b)         = opt a :+: opt b
opt (a :*: b)         = opt a :*: opt b
opt e                 = e

(+) :: N -> N -> N
S n + m = S (n + m)
Z   + m = m

(*) :: N -> N -> N
S n * m = m + (n * m)
Z   * m = Z

prop1 e = opt (d e) =:= (N (S (S Z)) :+: (X :+: X)) ==> True =:= False

prop2 e = opt (d e) =:= X :*: X :+: X :*: (X :+: X) ==> True =:= False

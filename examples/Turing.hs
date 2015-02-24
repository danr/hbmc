module Turing where

import Tip.DSL

data Action = Lft | Rgt

type Q = [((S,A),(S,A),Action)]

type State = (S,[A],[A])

data S = Stop | Succ S

data A = O | A | B | X

step :: Q -> State -> State
step q (s,lft,rgt) = act what s' lft x' rgt'
 where
  (x,rgt')     = split rgt
  ((s',x'),what) = apply q (s,x)

split :: [A] -> (A,[A])
split []     = (O,[])
split (x:xs) = (x,xs)

apply :: Q -> (S,A) -> ((S,A),Action)
apply [] _ = ((Stop,O),Lft)
apply ((sa,sa',what):q) sa0 =
  if eqT sa sa0 then
    (sa',what)
   else
    apply q sa0

act Lft s lft x rgt = (s, lft', y:x:rgt) where (y,lft') = split lft
act Rgt s lft x rgt = (s, x:lft, rgt)

eqT :: (S, A) -> (S, A) -> Bool
eqT (Stop, a)   (Stop, b)   = eqA a b
eqT (Succ p, a) (Succ q, b) = eqT (p,a) (q,b)
eqT _           _           = False

eqA :: A -> A -> Bool
eqA O O = True
eqA A A = True
eqA B B = True
eqA X X = True
eqA _ _ = False

runt :: Q -> [A] -> [A]
runt q tape = steps (Succ Stop,[],tape) q

-- FLAGS: csteps
steps :: State -> Q -> [A]
steps st q =
  case step q st of
    (Stop, tape1, tape2) -> rev tape1 tape2
    st'                  -> steps st' q

rev :: [A] -> [A] -> [A]
rev []     ys = ys
rev (O:xs) ys = ys
rev (x:xs) ys = rev xs (x:ys)

prog :: Q -> Bool
prog q = case runt q [A,A,B,B,X] of
            B:B:A:A:X:_ -> True
            _       -> False

prop q = prog q =:= False
            

module Turing where

import Tip.DSL

data Action = Lft | Rgt

type Q = [((Nat,A),(Nat,A),Action)]

type State = (Nat,[A],[A])

data Nat = Zero | Succ Nat

data A = O | A | B | X

step :: Q -> State -> State
step q (s,lft,rgt) = act what s' lft x' rgt'
 where
  (x,rgt')     = split rgt
  ((s',x'),what) = apply q (s,x)

split :: [A] -> (A,[A])
split []     = (O,[])
split (x:xs) = (x,xs)

apply :: Q -> (Nat,A) -> ((Nat,A),Action)
apply [] _ = ((Zero,O),Lft)
apply ((sa,sa',what):q) sa0 =
  if eqT sa sa0 then
    (sa',what)
   else
    apply q sa0

act Lft s lft x rgt = (s, lft', y:x:rgt) where (y,lft') = split lft
act Rgt s lft x rgt = (s, x:lft, rgt)

eqT :: (Nat, A) -> (Nat, A) -> Bool
eqT (Zero, a)   (Zero, b)   = eqA a b
eqT (Succ p, a) (Succ q, b) = eqT (p,a) (q,b)
eqT _           _           = False

eqA :: A -> A -> Bool
eqA O O = True
eqA A A = True
eqA B B = True
eqA X X = True
eqA _ _ = False

runt :: Q -> [A] -> [A]
runt q tape = steps q (Succ Zero,[],tape)

-- FLAGS: csteps
steps :: Q -> State -> [A]
steps q st =
  case step q st of
    (Zero, tape1, tape2) -> rev tape1 tape2
    st'                  -> steps q st'

runtN :: Nat -> Q -> [A] -> Maybe [A]
runtN n q tape = stepsN n q (one,[],tape)

stepsN :: Nat -> Q -> State -> Maybe [A]
stepsN Zero q st = Nothing
stepsN (Succ n) q st =
  case step q st of
    (Zero, tape1, tape2) -> Just (rev tape1 tape2)
    st'                  -> stepsN n q st'

rev :: [A] -> [A] -> [A]
rev []     ys = ys
rev (O:xs) ys = ys
rev (x:xs) ys = rev xs (x:ys)

one   = Succ Zero
two   = Succ one
three = Succ two
four  = Succ three
five  = Succ four
six   = Succ five
seven = Succ six

prog0 :: Q -> Bool
prog0 q = case runt q [B,A,A,A,A,B,X] of
                 A:A:A:A:B:B:X:_ -> True
                 _ -> False

prog1 :: Q -> Bool
prog1 q = case runtN six q [B,A,A,A,A,B,X] of
                 Just (A:A:A:A:B:B:X:_) ->
                   --case runtN two q [A,X] of
                   --  Just (A:X:_) -> True
                   --  _ -> False
                   True
                 _ -> False

prop q = prog0 q =:= False
            

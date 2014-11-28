module Main where

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :>: R a
  | Star (R a)
 deriving ( Eq, Show )

(.+.), (.>.) :: R a -> R a -> R a
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

Nil .>. q   = Nil
p   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

eps :: R a -> Bool
eps Eps       = True
eps (p :+: q) = eps p || eps q
eps (p :>: q) = eps p && eps q
eps (Star _)  = True
eps _         = False

epsR :: R a -> R a
epsR p | eps p     = Eps
       | otherwise = Nil

step :: Eq a => R a -> a -> R a
step (Atom a)  x | a == x = Eps
step (p :+: q) x          = step p x .+. step q x
step (p :>: q) x          = (step p x .>. q) .+. (epsR p .>. step q x)
step (Star p)  x          = step p x .>. Star p
step _         x          = Nil

rec :: Eq a => R a -> [a] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs


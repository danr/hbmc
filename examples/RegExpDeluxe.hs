module RegExpDeluxe where

import HBMC
import Prelude hiding ((==))

data Nat
  = Z
  | S Nat
 deriving ( Eq, Show )

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :&: R a
  | R a :>: R a
  | Star (R a)
 deriving ( Eq, Show )

data T = A | B | C
 deriving ( Eq, Ord, Show )

(.+.), (.&.), (.>.) :: R T -> R T -> R T
-- a .+. b = a :+: b
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

-- a .&. b = a :&: b
Nil .&. q   = Nil
p   .&. Nil = Nil
p   .&. q   = p :&: q

-- a .>. b = a :>: b
Nil .>. q   = Nil
p   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

eps :: R T -> Bool
eps Eps                = True
eps (p :+: q)          = label 1 (eps p) || label 2 (eps q)
eps (p :&: q)          = label 1 (eps p) && label 2 (eps q)
eps (p :>: q)          = label 1 (eps p) && label 2 (eps q)
eps (Star _)           = True
eps _                  = False

cond :: Bool -> R T
cond False = Nil
cond True  = Eps

(===) :: T -> T -> Bool
A === A = True
B === B = True
C === C = True
_ === _ = False

isZero :: Nat -> Bool
isZero Z = True
isZero _ = False

fromTo, fromTo' :: R T -> Nat -> Nat -> R T
fromTo  p i j = cond (isZero i) .+. (p .>. fromTo' p i j)

fromTo' p _     Z     = Nil
fromTo' p Z     (S j) = label 1 (fromTo p Z j)
fromTo' p (S i) (S j) = label 1 (fromTo p i j)

minus1 :: Nat -> Nat
minus1 Z     = Z
minus1 (S x) = x

rep :: R T -> Nat -> Nat -> R T
rep p i (S j) = (cond (isZero i) :+: p) :>: rep p (minus1 i) j
rep p i Z = case i of
             Z   -> Eps
             S _ -> Nil



{-
step :: R T -> T -> R T
step (Atom a)  x | a === x = Eps
step (p :+: q) x           =  label 1 (step p x) :+: label 2 (step q x)
step (p :&: q) x           =  label 1 (step p x) :&: label 2 (step q x)
step (p :>: q) x           = (label 1 (step p x) :>: q) :+: (cond (eps p) :>: label 2 (step q x))
step (Star p)  x           =  label 1 (step p x) :>: Star p
step _         x           = Nil
-}

step :: R T -> T -> R T
step (Atom a)  x | a === x = Eps
step (p :+: q) x           =  label 1 (step p x) :+: label 2 (step q x)
step (p :&: q) x           =  label 1 (step p x) :&: label 2 (step q x)
step (p :>: q)x| eps p     = (label 1 (step p x) :>: q) :+: label 2 (step q x)
               | otherwise =  label 1 (step p x) :>: q
-- step (p :>: q) x           = (label 1 (step p x) .>. q) .+. (cond (eps p) .>. label 2 (step q x))
-- step (Star p)  x           =  label 1 (step p x) .>. Star p
step _         x           = Nil

rec :: R T -> [T] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs

-- prop_koen p q s = rec (p :>: q) s =:= rec (q :>: p) s
--
-- prop_star_seq p q s = rec (Star (p :>: q)) s =:= rec (Star p :>: Star q) s
--
-- prop_switcheroo p q s = rec (p :+: q) s =:= rec (p :>: q) s
--
-- prop_bad_assoc p q r s = rec (p :+: (q :>: r)) s =:= rec ((p :+: q) :>: r) s

-- 2m48s:
-- prop_star_plus p q s = rec (Star (p :+: q)) s =:= rec (Star p :+: Star q) s

-- 10s:
-- prop_star_plus p q a b = rec (Star (p :+: q)) [a,b] =:= rec (Star p :+: Star q) [a,b]

prop_Conj p s =
  eps p =:= False ==>
    rec (p .&. (p .>. p)) s =:= False

{-
prop_FromToConj p i j i' j' s =
  eps p =:= False ==>
    rec (fromTo p i j .&. fromTo p i' j') s =:= rec (fromTo p (maxx i i') (minn j j')) s
    -}

maxx :: Nat -> Nat -> Nat
maxx Z     b     = b
maxx a     Z     = a
maxx (S a) (S b) = S (maxx a b)

minn :: Nat -> Nat -> Nat
minn Z     b     = Z
minn a     Z     = Z
minn (S a) (S b) = S (minn a b)


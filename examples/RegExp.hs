{-# LANGUAGE DeriveDataTypeable #-}
module RegExp where

import Control.Monad
import Data.Typeable
import Data.Data
import Tip.DSL
import Test.QuickCheck hiding (label)

label :: Int -> a -> a
label x s = s

data R
  = Nil
  | Eps
  | Atom C
  | R `Plus` R
  | R `Seq` R
  | Star R
 deriving ( Eq, Ord, Show, Data, Typeable )

{-
instance Arbitrary a => Arbitrary (R a) where
  arbitrary = sized go
    where
      go s = frequency
        [(1,return Nil)
        ,(1,return Eps)
        ,(3,Atom `fmap` arbitrary)
        ,(s,liftM2 (`Plus`) (go s2) (go s2))
        ,(s,liftM2 (`Seq`) (go s2) (go s2))
        ,(s,liftM  Star  (go s1))
        ]
        where
         s2 = s`div`2
         s1 = pred s
-}

infixl 7 `plus`
infixl 8 `seqq`

plus,seqq :: R  -> R  -> R
Nil `plus` q   = q
p   `plus` Nil = p
p   `plus` q   = p `Plus` q

Nil `seqq` q   = Nil
p   `seqq` Nil = Nil
Eps `seqq` q   = q
p   `seqq` Eps = p
p   `seqq` q   = p `Seq` q

eps :: R -> Bool
eps Eps       = True
eps (p `Plus` q) = if label 1 (eps p) then True else label 2 (eps q)
eps (p `Seq` q) = if label 1 (eps p) then label 2 (eps q) else False
eps (Star _)  = True
eps _         = False

epsR :: R  -> R
epsR p | eps p     = Eps
       | otherwise = Nil

data C = A | B | C
 deriving ( Eq, Ord, Show, Data, Typeable )

eq :: C -> C -> Bool
eq A A = True
eq B B = True
eq C C = True
eq _ _ = False

instance Arbitrary C where
  arbitrary = elements [A,B,C]

-- step :: Eq a => R a -> a -> R a
step :: R  -> C -> R
step (Atom a)  x | a `eq` x  = Eps
                 | otherwise = Nil
step (p `Plus` q) x          = label 1 (step p x) `plus` label 2 (step q x)
step (p `Seq` q) x          = (label 1 (step p x) `seqq` q) `plus` (epsR p `seqq` label 2 (step q x))
step (Star p)  x          = label 1 (step p x) `seqq` Star p
step _         x          = Nil

-- rec :: Eq a => R a -> [a] -> Bool
rec :: R  -> [C] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs

-- prop_koen p q s = rec (p `Seq` q) s =:= rec (q `Seq` p) s

prop_star_plus p q a b = rec (Star (p `Plus` q)) [a,b] =:= rec (Star p `Plus` Star q) [a,b]

-- prop_star_seq p q s = rec (Star (p `Seq` q)) s =:= rec (Star p `Seq` Star q) s
--
-- prop_switcheroo p q s = rec (p `Plus` q) s =:= rec (p `Seq` q) s
--
-- prop_bad_assoc p q r s = rec (p `Plus` (q `Seq` r)) s =:= rec ((p `Plus` q) `Seq` r) s

{-
reck :: R C -> [C] -> Bool
reck Eps       []  = True
reck (Atom a)  [b] = a == b
reck (p `Plus` q) s   = reck p s || reck q s
reck (p `Seq` q) s   = reck_seq p q (splits s)
reck (Star p)  []  = True
reck (Star p)  s   | not (eps p) = rec (p `Seq` Star p) s
reck _ _  = False

okay :: R C -> Bool
okay (p `Plus` q) = okay p && okay q
okay (p `Seq` q) = okay p && okay q
okay (Star p)  = okay p && not (eps p)
okay _         = True

reck_seq :: R C -> R C -> [([C],[C])] -> Bool
reck_seq p q []          = False
reck_seq p q ((l,r):lrs) = if reck p l && reck q r then True else reck_seq p q lrs

splits :: [a] -> [([a],[a])]
splits []     = [([],[])]
splits (x:xs) = ([],x:xs) : splits2 x (splits xs)

splits2 :: a -> [([a],[a])] -> [([a],[a])]
splits2 x xs = [ (x:as,bs) | (as,bs) <- xs ]

prop_same p s = rec p s =:= reck p s
-}

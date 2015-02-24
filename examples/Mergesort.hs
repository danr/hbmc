{-# LANGUAGE CPP #-}
module Mergesort(module Mergesort,module Nat) where

import Prelude (Bool(..),undefined,Ordering(..), (&&), (||), otherwise, not, fmap, Eq(..), Ord, fst, snd)

import HBMC

import Nat (Nat(..),(+),(*),(===))

-- import Test.QuickCheck hiding ((==>),(===))
-- import GHC.Types
-- import Data.Typeable

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
S _ <= Z   = False
S x <= S y = x <= y

count :: Nat -> [Nat] -> Nat
count n [] = Z
count n (x:xs)
  | n <= x && x <= n = S (count n xs)
  | otherwise = count n xs

-- FLAGS: cmsort
msort :: [Nat] -> [Nat]
msort []  = []
msort [x] = [x]
msort xs  = merge (msort (evens xs)) (msort (odds xs))

evens :: [a] -> [a]
evens [] = []
evens [x] = [x]
evens (x:_:xs) = x:evens xs

odds :: [a] -> [a]
odds [] = []
odds [_] = []
odds (_:y:xs) = y:odds xs

-- FLAGS: cmerge
merge :: [Nat] -> [Nat] -> [Nat]
merge (x:xs) (y:ys)
    | x <= y    = x:label [] (merge xs (y:ys))
    | otherwise = y:label [] (merge (x:xs) ys)
merge (x:xs) [] = x:xs
merge []     [] = []
merge [] ys = ys

ord :: [Nat] -> Bool
ord (x:y:xs) = if x <= y then ord (y:xs) else False
ord _        = True

nub :: [Nat] -> [Nat]
nub (x:xs) = x:remove x (nub xs)
nub []     = []

remove :: Nat -> [Nat] -> [Nat]
remove x [] = []
remove x (y:ys) = if x === y then ys else y:remove x ys

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

n0 = Z
n1 = S n0
n2 = S n1
n3 = S n2
n4 = S n3
n5 = S n4
n6 = S n5
n7 = S n6
n8 = S n7
n9 = S n8
n10 = S n9
n11 = S n10
n12 = S n11
n13 = S n12
n14 = S n13
n15 = S n14
n16 = S n15
n17 = S n16
n18 = S n17
n19 = S n18
n20 = S n19
n21 = S n20
n22 = S n21
n23 = S n22
n24 = S n23
n25 = S n24
n26 = S n25
n27 = S n26
n28 = S n27
n29 = S n28

#define INJ(sort,name,num) name xs ys = sort xs =:= sort ys ==> length xs <= num =:= False ==> xs =:= ys
#define NUB(sort,name,num) name xs ys = sort xs =:= sort ys ==> length xs <= num =:= False ==> nub xs =:= xs ==> xs =:= ys

INJ(msort,minj0,n0)
INJ(msort,minj1,n1)
INJ(msort,minj2,n2)
INJ(msort,minj3,n3)
INJ(msort,minj4,n4)
INJ(msort,minj5,n5)
INJ(msort,minj6,n6)
INJ(msort,minj7,n7)
INJ(msort,minj8,n8)
INJ(msort,minj9,n9)
INJ(msort,minj10,n10)
INJ(msort,minj11,n11)
INJ(msort,minj12,n12)
INJ(msort,minj13,n13)
INJ(msort,minj14,n14)
INJ(msort,minj15,n15)
INJ(msort,minj16,n16)
INJ(msort,minj17,n17)
INJ(msort,minj18,n18)
INJ(msort,minj19,n19)
INJ(msort,minj20,n20)
INJ(msort,minj21,n21)
INJ(msort,minj22,n22)
INJ(msort,minj23,n23)
INJ(msort,minj24,n24)
INJ(msort,minj25,n25)
INJ(msort,minj26,n26)
INJ(msort,minj27,n27)
INJ(msort,minj28,n28)
INJ(msort,minj29,n29)

NUB(msort,mnub0,n0)
NUB(msort,mnub1,n1)
NUB(msort,mnub2,n2)
NUB(msort,mnub3,n3)
NUB(msort,mnub4,n4)
NUB(msort,mnub5,n5)
NUB(msort,mnub6,n6)
NUB(msort,mnub7,n7)
NUB(msort,mnub8,n8)
NUB(msort,mnub9,n9)
NUB(msort,mnub10,n10)
NUB(msort,mnub11,n11)
NUB(msort,mnub12,n12)
NUB(msort,mnub13,n13)
NUB(msort,mnub14,n14)
NUB(msort,mnub15,n15)
NUB(msort,mnub16,n16)
NUB(msort,mnub17,n17)
NUB(msort,mnub18,n18)
NUB(msort,mnub19,n19)
NUB(msort,mnub20,n20)
NUB(msort,mnub21,n21)
NUB(msort,mnub22,n22)
NUB(msort,mnub23,n23)
NUB(msort,mnub24,n24)
NUB(msort,mnub25,n25)
NUB(msort,mnub26,n26)
NUB(msort,mnub27,n27)
NUB(msort,mnub28,n28)
NUB(msort,mnub29,n29)

INJ(isort,iinj0,n0)
INJ(isort,iinj1,n1)
INJ(isort,iinj2,n2)
INJ(isort,iinj3,n3)
INJ(isort,iinj4,n4)
INJ(isort,iinj5,n5)
INJ(isort,iinj6,n6)
INJ(isort,iinj7,n7)
INJ(isort,iinj8,n8)
INJ(isort,iinj9,n9)
INJ(isort,iinj10,n10)
INJ(isort,iinj11,n11)
INJ(isort,iinj12,n12)
INJ(isort,iinj13,n13)
INJ(isort,iinj14,n14)
INJ(isort,iinj15,n15)
INJ(isort,iinj16,n16)
INJ(isort,iinj17,n17)
INJ(isort,iinj18,n18)
INJ(isort,iinj19,n19)
INJ(isort,iinj20,n20)
INJ(isort,iinj21,n21)
INJ(isort,iinj22,n22)
INJ(isort,iinj23,n23)
INJ(isort,iinj24,n24)
INJ(isort,iinj25,n25)
INJ(isort,iinj26,n26)
INJ(isort,iinj27,n27)
INJ(isort,iinj28,n28)
INJ(isort,iinj29,n29)

NUB(isort,inub0,n0)
NUB(isort,inub1,n1)
NUB(isort,inub2,n2)
NUB(isort,inub3,n3)
NUB(isort,inub4,n4)
NUB(isort,inub5,n5)
NUB(isort,inub6,n6)
NUB(isort,inub7,n7)
NUB(isort,inub8,n8)
NUB(isort,inub9,n9)
NUB(isort,inub10,n10)
NUB(isort,inub11,n11)
NUB(isort,inub12,n12)
NUB(isort,inub13,n13)
NUB(isort,inub14,n14)
NUB(isort,inub15,n15)
NUB(isort,inub16,n16)
NUB(isort,inub17,n17)
NUB(isort,inub18,n18)
NUB(isort,inub19,n19)
NUB(isort,inub20,n20)
NUB(isort,inub21,n21)
NUB(isort,inub22,n22)
NUB(isort,inub23,n23)
NUB(isort,inub24,n24)
NUB(isort,inub25,n25)
NUB(isort,inub26,n26)
NUB(isort,inub27,n27)
NUB(isort,inub28,n28)
NUB(isort,inub29,n29)

-- prop_cancel2 xs ys zs =
--         msort xs =:= zs
--      /\ msort ys =:= zs
--      /\ False =:= length xs <= five
--     ==> msort xs =:= xs
--      \/ msort ys =:= ys
--      \/ xs =:= ys

-- prop_msort_ord_not xs = ord (msort xs) =:= False
--
-- prop_msort_permutation_wrong1 xs x = count x xs <= five =:= False ==> count x xs =:= count (S x) (msort xs)
-- prop_msort_permutation_wrong2 xs x = count x xs <= five =:= False ==> count (S x) xs =:= count x (msort xs)


-- prop_atotal     a b = a <= b =:= True \/ b <= a =:= True
-- prop_atotal_not a b = a <= b =:= True /\ b <= a =:= True ==> True =:= False
--
-- -- prop_merge_ord      xs ys = ord xs =:= True  ==> ord ys =:= True  ==> ord (merge xs ys) =:= True
-- prop_merge_ord_not1 xs ys = ord xs =:= True  ==> ord ys =:= True  ==> ord (merge xs ys) =:= False
-- prop_merge_ord_not2 xs ys = ord xs =:= False ==> ord ys =:= True  ==> ord (merge xs ys) =:= True
-- prop_merge_ord_not3 xs ys = ord xs =:= True  ==> ord ys =:= False ==> ord (merge xs ys) =:= True

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

(<) :: Nat -> Nat -> Bool
Z   < Z   = False
Z   < S{} = True
S{} < Z   = False
S n < S m = n < m

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

sorted :: [Nat] -> Bool
sorted (x:y:xs) = x <= y && sorted (y:xs)
sorted _        = True

usorted :: [Nat] -> Bool
usorted (x:y:xs) = x < y && usorted (y:xs)
usorted _        = True

allsmall :: Nat -> [Nat] -> Bool
allsmall n []     = True
allsmall n (x:xs) = x < n && allsmall n xs

assoc x xs ys zs = (xs ++ (ys ++ zs)) =:= ((xs ++ ys) ++ zs)
               ==> ((x:xs) ++ (ys ++ zs)) =:= (((x:xs) ++ ys) ++ (zs :: [Bool]))

assoc0 ys zs = [] ++ (ys ++ zs) =:= ([] ++ ys) ++ (zs :: [Bool])

{-
pins y x xs = not (sorted xs) || sorted (insert x xs) =:= True
          ==> sorted (x:xs) =:= True
          ==> sorted (insert y (x:xs)) =:= True
-}

pallsmall     xs = usorted xs =:= True ==> allsmall n4 xs =:= True ==> length xs <= n4 =:= True

unique :: [Nat] -> Bool
unique []     = True
unique (x:xs) = if x `elem` xs then False else unique xs

elem :: Nat -> [Nat] -> Bool
x `elem` [] = False
x `elem` (y:ys) = if x === y then True else x `elem` ys

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

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

partition :: Nat -> [Nat] -> ([Nat],[Nat])
partition _ [] = ([],[])
partition p (x:xs) =
  case partition p xs of
    (ys,zs) ->
      case p <= x of
        True  -> (x:ys,zs)
        False -> (ys,x:zs)

{-# NOINLINE singleton #-}
singleton x = [x]

-- FLAGS: cqsort
qsort :: [Nat] -> [Nat]
qsort []     = []
qsort (p:xs) =
  case partition p xs of
    (ys,zs) -> qsort ys ++ (singleton p ++ qsort zs)

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

psorted      xs = sorted xs           =:= True ==> unique xs =:= True ==> length xs <= n3 =:= True
psorted_rev  xs = sorted (rev xs)     =:= True ==> unique xs =:= True ==> length xs <= n3 =:= True
psorted_qrev xs = sorted (qrev xs []) =:= True ==> unique xs =:= True ==> length xs <= n3 =:= True

pusorted      xs = usorted xs           =:= True ==> length xs <= n4 =:= True
pusorted_rev  xs = usorted (rev xs)     =:= True ==> length xs <= n4 =:= True
pusorted_qrev xs = usorted (qrev xs []) =:= True ==> length xs <= n4 =:= True

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
#define UNQ(sort,name,num) name xs ys = sort xs =:= sort ys ==> length xs <= num =:= False ==> unique xs =:= True ==> xs =:= ys

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

UNQ(msort,munq0,n0)
UNQ(msort,munq1,n1)
UNQ(msort,munq2,n2)
UNQ(msort,munq3,n3)
UNQ(msort,munq4,n4)
UNQ(msort,munq5,n5)
UNQ(msort,munq6,n6)
UNQ(msort,munq7,n7)
UNQ(msort,munq8,n8)
UNQ(msort,munq9,n9)
UNQ(msort,munq10,n10)
UNQ(msort,munq11,n11)
UNQ(msort,munq12,n12)
UNQ(msort,munq13,n13)
UNQ(msort,munq14,n14)
UNQ(msort,munq15,n15)
UNQ(msort,munq16,n16)
UNQ(msort,munq17,n17)
UNQ(msort,munq18,n18)
UNQ(msort,munq19,n19)
UNQ(msort,munq20,n20)
UNQ(msort,munq21,n21)
UNQ(msort,munq22,n22)
UNQ(msort,munq23,n23)
UNQ(msort,munq24,n24)
UNQ(msort,munq25,n25)
UNQ(msort,munq26,n26)
UNQ(msort,munq27,n27)
UNQ(msort,munq28,n28)
UNQ(msort,munq29,n29)

INJ(qsort,qinj0,n0)
INJ(qsort,qinj1,n1)
INJ(qsort,qinj2,n2)
INJ(qsort,qinj3,n3)
INJ(qsort,qinj4,n4)
INJ(qsort,qinj5,n5)
INJ(qsort,qinj6,n6)
INJ(qsort,qinj7,n7)
INJ(qsort,qinj8,n8)
INJ(qsort,qinj9,n9)
INJ(qsort,qinj10,n10)
INJ(qsort,qinj11,n11)
INJ(qsort,qinj12,n12)
INJ(qsort,qinj13,n13)
INJ(qsort,qinj14,n14)
INJ(qsort,qinj15,n15)
INJ(qsort,qinj16,n16)
INJ(qsort,qinj17,n17)
INJ(qsort,qinj18,n18)
INJ(qsort,qinj19,n19)
INJ(qsort,qinj20,n20)
INJ(qsort,qinj21,n21)
INJ(qsort,qinj22,n22)
INJ(qsort,qinj23,n23)
INJ(qsort,qinj24,n24)
INJ(qsort,qinj25,n25)
INJ(qsort,qinj26,n26)
INJ(qsort,qinj27,n27)
INJ(qsort,qinj28,n28)
INJ(qsort,qinj29,n29)

NUB(qsort,qnub0,n0)
NUB(qsort,qnub1,n1)
NUB(qsort,qnub2,n2)
NUB(qsort,qnub3,n3)
NUB(qsort,qnub4,n4)
NUB(qsort,qnub5,n5)
NUB(qsort,qnub6,n6)
NUB(qsort,qnub7,n7)
NUB(qsort,qnub8,n8)
NUB(qsort,qnub9,n9)
NUB(qsort,qnub10,n10)
NUB(qsort,qnub11,n11)
NUB(qsort,qnub12,n12)
NUB(qsort,qnub13,n13)
NUB(qsort,qnub14,n14)
NUB(qsort,qnub15,n15)
NUB(qsort,qnub16,n16)
NUB(qsort,qnub17,n17)
NUB(qsort,qnub18,n18)
NUB(qsort,qnub19,n19)
NUB(qsort,qnub20,n20)
NUB(qsort,qnub21,n21)
NUB(qsort,qnub22,n22)
NUB(qsort,qnub23,n23)
NUB(qsort,qnub24,n24)
NUB(qsort,qnub25,n25)
NUB(qsort,qnub26,n26)
NUB(qsort,qnub27,n27)
NUB(qsort,qnub28,n28)
NUB(qsort,qnub29,n29)

UNQ(qsort,qunq0,n0)
UNQ(qsort,qunq1,n1)
UNQ(qsort,qunq2,n2)
UNQ(qsort,qunq3,n3)
UNQ(qsort,qunq4,n4)
UNQ(qsort,qunq5,n5)
UNQ(qsort,qunq6,n6)
UNQ(qsort,qunq7,n7)
UNQ(qsort,qunq8,n8)
UNQ(qsort,qunq9,n9)
UNQ(qsort,qunq10,n10)
UNQ(qsort,qunq11,n11)
UNQ(qsort,qunq12,n12)
UNQ(qsort,qunq13,n13)
UNQ(qsort,qunq14,n14)
UNQ(qsort,qunq15,n15)
UNQ(qsort,qunq16,n16)
UNQ(qsort,qunq17,n17)
UNQ(qsort,qunq18,n18)
UNQ(qsort,qunq19,n19)
UNQ(qsort,qunq20,n20)
UNQ(qsort,qunq21,n21)
UNQ(qsort,qunq22,n22)
UNQ(qsort,qunq23,n23)
UNQ(qsort,qunq24,n24)
UNQ(qsort,qunq25,n25)
UNQ(qsort,qunq26,n26)
UNQ(qsort,qunq27,n27)
UNQ(qsort,qunq28,n28)
UNQ(qsort,qunq29,n29)

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

UNQ(isort,iunq0,n0)
UNQ(isort,iunq1,n1)
UNQ(isort,iunq2,n2)
UNQ(isort,iunq3,n3)
UNQ(isort,iunq4,n4)
UNQ(isort,iunq5,n5)
UNQ(isort,iunq6,n6)
UNQ(isort,iunq7,n7)
UNQ(isort,iunq8,n8)
UNQ(isort,iunq9,n9)
UNQ(isort,iunq10,n10)
UNQ(isort,iunq11,n11)
UNQ(isort,iunq12,n12)
UNQ(isort,iunq13,n13)
UNQ(isort,iunq14,n14)
UNQ(isort,iunq15,n15)
UNQ(isort,iunq16,n16)
UNQ(isort,iunq17,n17)
UNQ(isort,iunq18,n18)
UNQ(isort,iunq19,n19)
UNQ(isort,iunq20,n20)
UNQ(isort,iunq21,n21)
UNQ(isort,iunq22,n22)
UNQ(isort,iunq23,n23)
UNQ(isort,iunq24,n24)
UNQ(isort,iunq25,n25)
UNQ(isort,iunq26,n26)
UNQ(isort,iunq27,n27)
UNQ(isort,iunq28,n28)
UNQ(isort,iunq29,n29)


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

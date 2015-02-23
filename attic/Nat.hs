module Nat where -- MiniSat.Nat

import MiniSat
import Data.List( sortBy, insertBy )

--------------------------------------------------------------------------------

data Nat = Nat [Lit]{-111..000-} Lit
 deriving ( Show )

newNat :: Solver -> Int{-maximum value-} -> IO Nat
newNat sat k =
  do true <- newLit sat
     addClause sat [true]
     xs <- sequence [ newLit sat | i <- [1..k] ]
     sequence_
       [ addClause sat [x,neg y] | (x,y) <- xs `zip` tail xs ]
     return (Nat xs true)

count :: Solver -> [Lit] -> IO Nat
count sat xs =
  do true <- newLit sat
     addClause sat [true]
     -- simplest implementation; becomes a sorting network
     -- better is a pairwise sorting network, but is it worth the trouble?
     addList sat [ Nat [x] true | x <- xs ]

--------------------------------------------------------------------------------

add :: Solver -> Nat -> Nat -> IO Nat
add sat (Nat xs true) (Nat ys _) =
  do zs <- merge xs ys
     return (Nat zs true)
 where
  -- for padding
  false = neg true

  -- merge two literals
  merge2 a b
    | a == false = do return (b,false)
    | b == false = do return (a,false)
    | a == true  = do return (true,b)
    | b == true  = do return (true,a)
    | a == b     = do return (a,a)
    | a == neg b = do return (true, false)
    | otherwise  = do x <- newLit sat
                      addClause sat [a, b, neg x]
                      addClause sat [x, neg a]
                      addClause sat [x, neg b]
                      
                      y <- newLit sat
                      addClause sat [neg a, neg b, y]
                      addClause sat [neg y, a]
                      addClause sat [neg y, b]
                      
                      return (x,y)

  -- merge two lists of the same, even length
  mergeSameEven as bs =
    do cs0 <- merge as0 bs0
       cs1 <- merge as1 bs1
       let c0:cs' = cs0 `weave` cs1
           cs     = init cs'
           c1     = last cs'
       xys <- sequence [ merge2 x y | (x,y) <- pair cs ]
       return ([c0] ++ unpair xys ++ [c1])
   where
    (as0,as1) = evenOdds as
    (bs0,bs1) = evenOdds bs

    evenOdds []       = ([], [])
    evenOdds (x:y:xs) = (x:es,y:os) where (es,os) = evenOdds xs

    []     `weave` []     = []
    (x:xs) `weave` (y:ys) = x:y:(xs `weave` ys)

    pair (x:y:xs) = (x,y):pair xs
    pair []       = []
    
    unpair ((x,y):xys) = x:y:unpair xys
    unpair []          = []

  -- merge any two lists
  merge as [] =
    do return as

  merge [] bs =
    do return bs

  merge [a] [b] =
    do (x,y) <- merge2 a b
       return [x,y]

  merge as bs =
    do cs' <- mergeSameEven as' bs' -- pad to make lengths same and even
       --assert (all (==false) (drop (n+m) cs'))
       return (take (n+m) cs')
   where
    n   = length as
    m   = length bs
    mx  = n `max` m
    new = if even mx then mx else mx+1
    as' = as ++ replicate (new-n) false
    bs' = bs ++ replicate (new-m) false
 
addList :: Solver -> [Nat] -> IO Nat
addList sat ns =
  go (sortBy first [(size n, n) | n <- ns])
 where
  go [] =
    do true <- newLit sat
       addClause sat [true]
       return (Nat [] true)
  
  go [(_,n)] =
    do return n
  
  go ((_,n):(_,m):ns) =
    do nm <- add sat n m
       go (insertBy first (size nm, nm) ns)
  
  size (Nat xs _)     = length xs
  (x,_) `first` (y,_) = x `compare` y

--------------------------------------------------------------------------------

(.<=), (.>=), (.<), (.>) :: Nat -> Int -> Lit
nat .<= k = neg (nat .> k)
nat .>= k = neg (nat .< k)
nat .<  k = nat .<= (k-1)
--nat .>  k = nat .>= (k+1)

Nat xs true .> k
  | k < 0     = true
  | k >= n    = neg true
  | otherwise = xs !! k
 where
  n = length xs

--------------------------------------------------------------------------------

(.+) :: Nat -> Int -> Nat
Nat xs true .+ k = Nat (replicate k true ++ xs) true

assertLeqOr, assertGeqOr,
  assertLtOr, assertGtOr,
  assertEqOr, assertNeqOr :: Solver -> [Lit] -> Nat -> Nat -> IO () 
--assertLeqOr sat es n m = assertGeqOr sat es m n
assertGeqOr sat es n m = assertLeqOr sat es m n
assertLtOr  sat es n m = assertLeqOr sat es (n .+ 1) m 
assertGtOr  sat es n m = assertGeqOr sat es n (m .+ 1) 

assertLeqOr sat es (Nat ns _) (Nat ms true) =
  do sequence_
       [ addClause sat (es ++ [neg a, b])
       | (a,b) <- ns `zip` (ms ++ repeat (neg true))
       ]

assertEqOr sat es n m =
  do assertLeqOr sat es n m
     assertGeqOr sat es n m

assertNeqOr sat es n m =
  do x <- newLit sat
     assertGtOr sat (x    :es) n m
     assertLtOr sat (neg x:es) n m

--------------------------------------------------------------------------------

solveMinimize :: Solver -> [Lit] -> Nat -> IO Bool
solveMinimize sat as n =
  do b <- solve sat as
     if b then
       let mini =
             do v <- modelValueNat sat n
                --putStrLn ("Trying " ++ show v ++ "...")
                b <- solve sat ((n .< v):as)
                if b then mini
                     else return True
        in mini
      else
       do return False

solveMaximize :: Solver -> [Lit] -> Nat -> IO Bool
solveMaximize sat as (Nat xs true) = solveMinimize sat as (Nat (reverse (map neg xs)) true)

--------------------------------------------------------------------------------

solveMinimizeBin :: Solver -> [Lit] -> Nat -> IO Bool
solveMinimizeBin sat as n =
  do b <- solve sat as
     if b then
       do v <- modelValueNat sat n
          let mini (mn,mx)
                | mn > mx   = do return True
                | otherwise = do --putStrLn ("Trying " ++ show (mn,mx) ++ "...")
                                 b <- solve sat ((n .< w):as)
                                 if b then do v <- modelValueNat sat n
                                              mini (mn,v-1)
                                      else do mini (w+1,mx)
               where
                w = (mn+mx) `div` 2
           in mini (0,v-1)
      else
       do return False

solveMaximizeBin :: Solver -> [Lit] -> Nat -> IO Bool
solveMaximizeBin sat as (Nat xs true) = solveMinimizeBin sat as (Nat (reverse (map neg xs)) true)

--------------------------------------------------------------------------------

modelValueNat :: Solver -> Nat -> IO Int
modelValueNat sat (Nat xs _) =
  do bs <- sequence [ modelValue sat x | x <- xs ]
     return (length [ b | b <- bs, if b == Nothing then error "!" else True, b == Just True ])

--------------------------------------------------------------------------------


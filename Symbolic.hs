{-# LANGUAGE TypeFamilies #-}
module Symbolic where

import MiniSat
import qualified Data.List as L
import Data.Maybe

--------------------------------------------------------------------------------

data Bit = Lit Lit | Bool Bool
 deriving ( Eq, Ord )

newBit :: Solver -> IO Bit
newBit s = Lit `fmap` newLit s

ff, tt :: Bit
ff = Bool False
tt = Bool True

nt :: Bit -> Bit
nt (Bool b) = Bool (not b)
nt (Lit x)  = Lit (neg x)

andl, orl :: Solver -> [Bit] -> IO Bit
andl s xs
  | ff `elem` xs = return ff
  | otherwise    = andl' [ x | Lit x <- xs ]
 where
  andl' []  = do return tt
  andl' [x] = do return (Lit x)
  andl' xs  = do y <- newLit s
                 addClause s (y : map neg xs)
                 sequence_ [ addClause s [neg y, x] | x <- xs ]
                 return (Lit y)

orl s xs = nt `fmap` andl s (map nt xs)

addClauseBit :: Solver -> [Bit] -> IO ()
addClauseBit s xs
  | tt `elem` xs = do return ()
  | otherwise    = do addClause s [ x | Lit x <- xs ]
                      return ()

iffBit :: Solver -> Bit -> Bit -> Bit -> IO Bit
iffBit s (Bool b) x y =
  do return (if b then x else y)

iffBit s _ x y | x == y =
  do return x

iffBit s c (Bool a) (Bool b) = -- a /= b now!
  do return (if a then c else nt c)

iffBit s c x y =
  do z <- newBit s
     addClauseBit s [nt c, nt x, z]
     addClauseBit s [nt c, x, nt z]
     addClauseBit s [c, nt y, z]
     addClauseBit s [c, y, nt z]
     return z

--------------------------------------------------------------------------------

data Val a = Val [(Bit,a)]

val :: a -> Val a
val x = Val [(tt,x)]

(=?) :: Eq a => Val a -> a -> Bit
Val []        =? x  = ff
Val ((a,y):xs) =? x
  | x == y      = a
  | otherwise   = Val xs =? x

domain :: Val a -> [a]
domain (Val xs) = map snd xs

newVal :: Ord a => Solver -> [a] -> IO (Val a)
newVal s xs =
  do as <- lits (length ys)
     return (Val (as `zip` ys))
 where
  ys = map head . L.group . L.sort $ xs

  lits 1 =
    do return [tt]

  lits 2 =
    do a <- newBit s
       return [a,nt a]

  lits n =
    do as <- sequence [ newBit s | i <- [1..n] ]
       addClauseBit s as
       atMostOne n as
       return as

  atMostOne n as | n <= 5 =
    do sequence_ [ addClauseBit s [nt x, nt y] | (x,y) <- pairs as ]
   where
    pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs
    pairs _      = []

  atMostOne n as =
    do a <- newBit s
       atMostOne (k+1) (a : take k as)
       atMostOne (n-k+1) (nt a : drop k as)
   where
    k = n `div` 2

iffVal :: Ord a => Solver -> Bit -> Val a -> Val a -> IO (Val a)
iffVal s c (Val xs) (Val ys) =
  Val `fmap` sequence
    [ do d <- iff s c a b
         return (d,x)
    | (ma, mb, x) <- align xs ys
    , let a = fromMaybe ff ma
          b = fromMaybe ff mb
    ]

equalVal :: Ord a => Solver -> Val a -> Val a -> IO Bit
equalVal s (Val xs) (Val ys) =
  andl s =<< sequence
    [ equal s a b
    | (ma, mb, x) <- align xs ys
    , let a = fromMaybe ff ma
          b = fromMaybe ff mb
    ]

getVal :: Solver -> Val a -> IO a
getVal s (Val ((a,x):xs)) =
  do b <- get s a
     if b then return x else getVal s (Val xs)

--------------------------------------------------------------------------------

align :: Ord b => [(a,b)] -> [(a,b)] -> [(Maybe a, Maybe a, b)]
align ((a1,b1):abs1) ((a2,b2):abs2) =
  case b1 `compare` b2 of
    LT -> (Just a1, Nothing, b1) : align abs1 ((a2,b2):abs2)
    EQ -> (Just a1, Just a2, b1) : align abs1 abs2
    GT -> (Nothing, Just a2, b2) : align ((a1,b1):abs1) abs2

align [] ys = [(Nothing, Just a, b) | (a,b) <- ys]
align xs [] = [(Just a, Nothing, b) | (a,b) <- xs]

--------------------------------------------------------------------------------

class Symbolic a where
  type Type a

  iff   :: Solver -> Bit -> a -> a -> IO a
  equal :: Solver -> a -> a -> IO Bit
  get   :: Solver -> a -> IO (Type a)

--------------------------------------------------------------------------------

instance Symbolic Bit where
  type Type Bit = Bool

  iff = iffBit

  equal s x y =
    do iff s x y (nt y)

  get s (Bool b) =
    do return b

  get s (Lit x) =
    do mb <- modelValue s x
       return (mb == Just True)

instance Ord a => Symbolic (Val a) where
  type Type (Val a) = a

  iff   = iffVal
  equal = equalVal
  get   = getVal

--------------------------------------------------------------------------------

data Lift a = The a | UNR
 deriving ( Eq, Ord, Show )

the :: Lift a -> a
the (The x) = x
the UNR     = error "the UNR"

instance Symbolic a => Symbolic (Lift a) where
  type Type (Lift a) = Type a

  iff s c x UNR =
    do return x

  iff s c UNR y =
    do return y

  iff s c (The x) (The y) =
    do z <- iff s c x y
       return (The z)

  equal s (The x) (The y) =
    do equal s x y

  equal s _ _ =
    do return (error "equal on an UNR")
    -- do return ff

  get s (The x) =
    do get s x

  get s UNR =
    do return (error "get on an UNR")

--------------------------------------------------------------------------------

type Name = String -- Int?

data Typ = TApp Name [Typ]
 deriving ( Eq, Ord, Show )

data Data = Data Typ [(Name, [Typ])]
 deriving ( Eq, Ord, Show )

data SymTerm = Con Data (Val Name) [(SymTerm,Typ)]

data Term = Fun Name [Term]
 deriving ( Eq, Ord, Show )

iffArgs :: Solver -> Bit -> [(SymTerm,Typ)] -> [(SymTerm,Typ)] -> IO [(SymTerm,Typ)]
iffArgs s c xs ys =
  sequence
  [ case (mx, my) of
      (Just x,  Just y)  -> (\z -> (z,t)) `fmap` iff s c x y
      (Nothing, Just y)  -> return (y, t)
      (Just x,  Nothing) -> return (x, t)
  | (mx, my, t) <- align xs ys
  ]

equalArgs :: Solver -> Data -> [(Bit,Name)] -> [(SymTerm,Typ)] -> [(SymTerm,Typ)] -> IO [Bit]
equalArgs s (Data _ cons) fs xs ys =
  do eqts <- sequence
             [ do eq <- equal s a b
                  return (eq, t)
             | (Just a, Just b, t) <- align xs ys
             ]
     sequence
       [ do eq <- andl s [ eq | eq <- match args eqts ]
            orl s [nt a, eq]
       | (a, f) <- fs
       , let args:_ = [ args | (c,args) <- cons, c == f ]
       ]

getArgs :: Solver -> Data -> Name -> [(SymTerm,Typ)] -> IO [Term]
getArgs s (Data _ cons) f xs =
  sequence [ get s x | x <- match args xs ]
 where
  args:_ = [ args | (c,args) <- cons, c == f ]

match :: [Typ] -> [(a,Typ)] -> [a]
match [] _    = []
match (t:ts) ((a,t'):as)
  | t == t'   = a : match ts as
  | otherwise = match (t:ts) as

instance Symbolic SymTerm where
  type Type SymTerm = Term

  iff s c (Con tp c1 x1) (Con _ c2 x2) =
    do c' <- iff s c c1 c2
       x' <- iffArgs s c x1 x2
       return (Con tp c' x')

  equal s (Con tp c1 x1) (Con _ c2 x2) =
    do eqc <- equal s c1 c2
       eqs <- equalArgs s tp [ (c1 =? f, f) | f <- fs ] x1 x2
       andl s (eqc : eqs)
   where
    fs = domain c1 `L.intersect` domain c2

  get s (Con tp c x) =
    do f <- get s c
       xs <- getArgs s tp f x
       return (Fun f xs)

switch :: Symbolic b => Solver -> SymTerm -> [(Name, Bit -> [SymTerm] -> IO b)] -> IO b
switch s (Con (Data _ cons) cn xs) alts =
  do bs <- sequence
           [ do b <- alt (cn =? f) (match args xs)
                return (c,b)
           | f <- domain cn
           , let c      = cn =? f
                 args:_ = [ args | (c,args) <- cons, c == f ]
           , (f', alt) <- alts
           , f == f'
           ]
     smash s bs

smash :: Symbolic a => Solver -> [(Bit,a)] -> IO a
smash s [(_,x)] =
  do return x

smash s ((a,x):xs) =
  do y <- smash s xs
     iff s a x y

--------------------------------------------------------------------------------

instance (Symbolic a, Symbolic b) => Symbolic (a,b) where
  type Type (a,b) = (Type a, Type b)

  iff s c (x1,y1) (x2,y2) =
    do x <- iff s c x1 x2
       y <- iff s c y1 y2
       return (x,y)

  equal s (x1,y1) (x2,y2) =
    do ex <- equal s x1 x2
       ey <- equal s y1 y2
       andl s [ex,ey]

  get s (a,b) =
    do x <- get s a
       y <- get s b
       return (x,y)

--------------------------------------------------------------------------------

data List a = ConsNil Bit a (List a)
            | Nil

newLists :: Solver -> Int -> IO a -> IO (List a)
newLists s 0 el =
  do return Nil

newLists s n el =
  do c  <- newBit s
     x  <- el
     xs <- newLists s (n-1) el
     return (ConsNil c x xs)

cons :: a -> List a -> List a
cons x xs = ConsNil tt x xs

caseList :: Symbolic b => Solver -> List a -> IO b -> (Bit -> a -> List a -> IO b) -> IO b
caseList s Nil nil _ =
  do nil

caseList s (ConsNil c x xs) nil cns =
  do b1 <- nil
     b2 <- cns c x xs
     iff s c b2 b1

maybeCons :: Solver -> [Bit] -> List a -> IO Bool
maybeCons s ass Nil                    = do return False
maybeCons s ass (ConsNil (Bool b) _ _) = do return b
maybeCons s ass (ConsNil (Lit x) _ _)
  | ff `elem` ass                      = do return False
  | otherwise                          = do solve s (x:[y | Lit y <- ass])

caseList' :: Symbolic b => Solver -> [Bit] -> List a -> IO b -> (Bit -> a -> List a -> IO b) -> IO b
caseList' s ass xs nil cns =
  do b <- maybeCons s ass xs
     caseList s (if b then xs else Nil) nil cns

instance Symbolic a => Symbolic (List a) where
  type Type (List a) = [Type a]

  iff s c (ConsNil c1 x1 xs1) (ConsNil c2 x2 xs2) =
    do c'  <- iff s c c1 c2
       x'  <- iff s c x1 x2
       xs' <- iff s c xs1 xs2
       return (ConsNil c' x' xs')

  iff s c (ConsNil c1 x1 xs1) Nil =
    do c' <- iff s c c1 ff
       return (ConsNil c' x1 xs1)

  iff s c Nil (ConsNil c2 x2 xs2) =
    do c' <- iff s c ff c2
       return (ConsNil c' x2 xs2)

  iff s c Nil Nil =
    do return Nil

  equal s Nil Nil =
    do return tt

  equal s (ConsNil c _ _) Nil =
    do return (nt c)

  equal s Nil (ConsNil c _ _) =
    do return (nt c)

  equal s (ConsNil c1 x1 xs1) (ConsNil c2 x2 xs2) =
    do e1 <- equal s c1 c2
       e2 <- equal s (x1,xs1) (x2,xs2)
       e2' <- orl s [nt c1, e2]
       andl s [e1, e2']

  get s Nil =
    do return []

  get s (ConsNil c x xs) =
    do b <- get s c
       if b
         then do a <- get s x
                 as <- get s xs
                 return (a:as)
         else do return []

--------------------------------------------------------------------------------

data Tree a = Node (Tree a) a (Tree a)
            | Empty
 deriving ( Eq, Ord, Show )

data TREE a = NodeEmpty Bit (TREE a) a (TREE a)
            | EMPTY

newTrees :: Solver -> Int -> IO a -> IO (TREE a)
newTrees s 0 el =
  do return EMPTY

newTrees s n el =
  do c <- newBit s
     x <- el
     p <- newTrees s (n-1) el
     q <- newTrees s (n-1) el
     return (NodeEmpty c p x q)

node :: TREE a -> a -> TREE a -> TREE a
node p x q = NodeEmpty tt p x q

caseTree :: Symbolic b => Solver -> TREE a -> IO b -> (Bit -> TREE a -> a -> TREE a -> IO b) -> IO b
caseTree s EMPTY emp _ =
  do emp

caseTree s (NodeEmpty c p x q) emp nod =
  do b1 <- emp
     b2 <- nod c p x q
     iff s c b2 b1

maybeNode :: Solver -> [Bit] -> TREE a -> IO Bool
maybeNode s ass EMPTY                      = do return False
maybeNode s ass (NodeEmpty (Bool b) _ _ _) = do return b
maybeNode s ass (NodeEmpty (Lit x) _ _ _)
  | ff `elem` ass                          = do return False
  | otherwise                              = do solve s (x:[y | Lit y <- ass])

caseTree' :: Symbolic b => Solver -> [Bit] -> TREE a -> IO b -> (Bit -> TREE a -> a -> TREE a -> IO b) -> IO b
caseTree' s ass p emp nod =
  do b <- maybeNode s ass p
     caseTree s (if b then p else EMPTY) emp nod

instance Symbolic a => Symbolic (TREE a) where
  type Type (TREE a) = Tree (Type a)

  iff s c (NodeEmpty c1 p1 x1 q1) (NodeEmpty c2 p2 x2 q2) =
    do c'  <- iff s c c1 c2
       p'  <- iff s c p1 p2
       x'  <- iff s c x1 x2
       q'  <- iff s c q1 q2
       return (NodeEmpty c' p' x' q')

  iff s c (NodeEmpty c1 p1 x1 q1) EMPTY =
    do c' <- iff s c c1 ff
       return (NodeEmpty c' p1 x1 q1)

  iff s c EMPTY (NodeEmpty c2 p2 x2 q2) =
    do c' <- iff s c c2 ff
       return (NodeEmpty c' p2 x2 q2)

  iff s c EMPTY EMPTY =
    do return EMPTY

  equal s EMPTY EMPTY =
    do return tt

  equal s (NodeEmpty c _ _ _) EMPTY =
    do return (nt c)

  equal s EMPTY (NodeEmpty c _ _ _) =
    do return (nt c)

  equal s (NodeEmpty c1 p1 x1 q1) (NodeEmpty c2 p2 x2 q2) =
    do e1 <- equal s c1 c2
       e2 <- equal s (p1,(x1,q1)) (p2,(x2,q2))
       e2' <- orl s [nt c1, e2]
       andl s [e1, e2']

  get s EMPTY =
    do return Empty

  get s (NodeEmpty c p x q) =
    do b <- get s c
       if b
         then do a <- get s x
                 t <- get s p
                 t' <- get s q
                 return (Node t a t')
         else do return Empty

--------------------------------------------------------------------------------

data Nat = Nat [Bit]

newNat :: Solver -> Int -> IO Nat
newNat s k =
  do xs <- sequence [ newBit s | i <- [1..k] ]
     return (Nat xs)

leq :: Solver -> Nat -> Nat -> IO Bit
leq s (Nat xs) (Nat ys) = cmp (reverse (pad n xs)) (reverse (pad n ys))
 where
  n = length xs `max` length ys
  pad n xs = xs ++ replicate (n-length xs) ff

  cmp [] [] =
    do return tt

  cmp (x:xs) (y:ys) =
    do z <- newBit s
       r <- cmp xs ys
       addClauseBit s [nt x, y, nt z]
       addClauseBit s [x, nt y, z]
       addClauseBit s [nt x, nt y, nt r, z]
       addClauseBit s [x, y, nt r, z]
       addClauseBit s [nt x, nt y, r, nt z]
       addClauseBit s [x, y, r, nt z]
       return z

fromInt :: Integer -> Nat
fromInt 0 = Nat []
fromInt n = Nat (Bool (even n):xs) where Nat xs = fromInt (n `div` 2)

count :: Solver -> [Bit] -> IO Nat
count s [] = return (Nat [])
count s xs = go [[x] | x <- xs]
 where
  go [n] =
    do return (Nat n)

  go (a:b:xs) =
    do c <- add ff a b
       go (xs ++ [c])

  add c [] [] =
    do return [c]

  add c [] ys =
    do add c [ff] ys

  add c xs [] =
    do add c xs [ff]

  add c (x:xs) (y:ys) =
    do c' <- newBit s
       addClauseBit s [nt x, nt y, c']
       addClauseBit s [nt x, nt c, c']
       addClauseBit s [nt y, nt c, c']
       addClauseBit s [   x,    y, nt c']
       addClauseBit s [   x,    c, nt c']
       addClauseBit s [   y,    c, nt c']

       z <- newBit s
       addClauseBit s [nt x, nt y, nt c, z]
       addClauseBit s [   x, nt y, nt c, nt z]
       addClauseBit s [nt x,    y, nt c, nt z]
       addClauseBit s [nt x, nt y,    c, nt z]
       addClauseBit s [nt x,    y,    c, z]
       addClauseBit s [   x, nt y,    c, z]
       addClauseBit s [   x,    y, nt c, z]
       addClauseBit s [   x,    y,    c, nt z]

       zs <- add c' xs ys
       return (z:zs)

len :: Solver -> List a -> IO Nat
len s xs =
  do Nat cs <- cnt xs
     count s cs
 where
  cnt xs =
    caseList s xs
      (return (Nat []))
      (\_ _ xs ->
         do Nat cs <- cnt xs
            return (Nat (tt:cs)))

instance Symbolic Nat where
  type Type Nat = Integer

  iff s c (Nat []) (Nat []) =
    do return (Nat [])

  iff s c (Nat []) (Nat ys) =
    do iff s c (Nat [ff]) (Nat ys)

  iff s c (Nat xs) (Nat []) =
    do iff s c (Nat xs) (Nat [ff])

  iff s c (Nat (x:xs)) (Nat (y:ys)) =
    do z <- iff s c x y
       Nat zs <- iff s c (Nat xs) (Nat ys)
       return (Nat (z:zs))

  equal s (Nat []) (Nat []) =
    do return tt

  equal s (Nat []) (Nat ys) =
    do equal s (Nat [ff]) (Nat ys)

  equal s (Nat xs) (Nat []) =
    do equal s (Nat xs) (Nat [ff])

  equal s (Nat (x:xs)) (Nat (y:ys)) =
    do eq1 <- equal s x y
       eq2 <- equal s (Nat xs) (Nat ys)
       andl s [eq1,eq2]

  get s (Nat []) =
    do return 0

  get s (Nat (x:xs)) =
    do b <- get s x
       n <- get s (Nat xs)
       return (2*n + (if b then 1 else 0))

--------------------------------------------------------------------------------

-- (linear :p) Construction of values:

choices :: Symbolic a => Solver -> [a] -> IO a
choices s [] = error "choices: empty list of alternatives"
choices s [x] = return x
choices s (x:xs) = do
    b <- newBit s
    iff s b x =<< choices s xs


{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving #-}
module Symbolic
  ( H -- :: Monad, Functor, Applicative
  , lift, peek, withSolver, withExtra, context, cutoff, check, impossible
  
  , Choice(..), Equal(..), Value(..)
  
  , Bit
  , newBit, ff, tt, nt, andl, orl, addClause, (==>)
  
  , Lift(..)
  
  , Val
  , val, domain, newVal, (=?), choose
  
  , Nat
  , newNat
  
  , Data(..)
  , switch
  )
 where

import MiniSat( Solver, Lit )
import qualified MiniSat as M
import Control.Applicative
import Data.List
import Data.Maybe

{-
================================================================================
-- The H monad
================================================================================
-}

newtype H a = H{ run :: Solver -> [Bit] -> IO (Lift a) }

instance Applicative H where
  pure x      = H (\_ _ -> return (The x))
  H f <*> H x = H (\s ctx -> do mf <- f s ctx
                                case mf of
                                  UNR   -> return UNR
                                  The f -> do mx <- x s ctx
                                              case mx of
                                                UNR   -> return UNR
                                                The x -> return (The (f x)))

instance Functor H where
  f `fmap` H m = H (\s ctx -> do mx <- m s ctx
                                 return (f `fmap` mx))

instance Monad H where
  return    = pure
  fail s    = H (\_ _ -> return UNR)
  H m >>= k = H (\s ctx -> do mx <- m s ctx
                              case mx of
                                UNR   -> return UNR
                                The x -> run (k x) s ctx)

--------------------------------------------------------------------------------

lift :: H a -> H (Lift a)
lift (H m) = H (\s ctx -> do a <- newBit -- haha!
                             mx <- m s (a:ctx)
                             return (The mx))

peek :: Lift a -> H a
peek UNR     = impossible
peek (The x) = return x

withSolver :: (Solver -> IO a) -> H a
withSolver f = H (\s _ -> The `fmap` f s)

withExtra :: H a -> Bit -> H a
H m `withExtra` b = H (\s ctx -> m s (b:ctx))

context :: H [Bit]
context = H (\_ ctx -> return (The ctx))

runH :: H a -> IO (Lift a)
runH m =
  do s <- M.newSolver
     x <- run m s []
     M.deleteSolver s
     return x

--------------------------------------------------------------------------------

cutoff :: Int -> H ()
cutoff n =
  do ctx <- context
     if length ctx >= n then impossible else return ()

check :: H ()
check =
  do ctx <- context
     b <- if ff `elem` ctx
            then return False
            else withSolver (\s -> M.solve s [ x | Lit x <- ctx ])
     if b then
       return ()
      else
       fail "context is inconsistent"

impossible :: H a
impossible =
  do ctx <- context
     addClause (map nt ctx)
     fail "impossible"

{-
================================================================================
-- Useful type classes
================================================================================
-}

class Choice a where
  iff :: Bit -> a -> a -> H a

class Value a where
  type Type a
  get :: a -> H (Type a)

class Equal a where
  equalStruct :: a -> a -> H (Struct Bit)

data Struct a
  = Tuple [Struct a]
  | Bit a
  | Empty
 deriving ( Eq, Ord, Show )

equal :: Equal a => a -> a -> H Bit
equal x y =
  do str <- equalStruct x y
     andl (bits str)

bits :: Struct Bit -> [Bit]
bits (Tuple ts) = concatMap bits ts
bits (Bit x)    = [x]
bits Empty      = []

{-
================================================================================
-- type Bit
================================================================================
-}

data Bit = Lit Lit | Bool Bool
 deriving ( Eq, Ord )

instance Show Bit where
  show (Bool b) = if b then "TT" else "FF"
  show (Lit v)  = show v

newBit :: H Bit
newBit = withSolver (\s -> Lit `fmap` M.newLit s)

ff, tt :: Bit
ff = Bool False
tt = Bool True

nt :: Bit -> Bit
nt (Bool b) = Bool (not b)
nt (Lit x)  = Lit (M.neg x)

andl, orl :: [Bit] -> H Bit
andl xs
  | ff `elem` xs = return ff
  | otherwise    = withSolver (\s -> andl' s [ x | Lit x <- xs ])
 where
  andl' s []  = do return tt
  andl' s [x] = do return (Lit x)
  andl' s xs  = do y <- M.newLit s
                   M.addClause s (y : map M.neg xs)
                   sequence_ [ M.addClause s [M.neg y, x] | x <- xs ]
                   return (Lit y)

orl xs = nt `fmap` andl (map nt xs)

addClause :: [Bit] -> H ()
addClause xs
  | tt `elem` xs = do return ()
  | otherwise    = do withSolver (\s -> M.addClause s [ x | Lit x <- xs ])
                      return ()

(==>) :: [Bit] -> [Bit] -> H ()
xs ==> ys = addClause (map nt xs ++ ys)

--------------------------------------------------------------------------------

instance Choice Bit where
  iff (Bool b) x y =
    do return (if b then x else y)

  iff _ x y | x == y =
    do return x

  iff c (Bool a) (Bool b) = -- a /= b now!
    do return (if a then c else nt c)

  iff c x y =
    do z <- newBit
       [c, x]    ==> [z]
       [c, z]    ==> [x]
       [nt c, y] ==> [z]
       [nt c, z] ==> [y]
       return z

instance Equal Bit where
  equalStruct x y = Bit `fmap` iff x y (nt y)

instance Value Bit where
  type Type Bit = Bool

  get (Bool b) = return b
  get (Lit x)  = (Just True ==) `fmap` withSolver (\s -> M.modelValue s x)

{-
================================================================================
-- Tuples
================================================================================
-}

instance (Choice a, Choice b) => Choice (a,b) where
  iff c (x1,y1) (x2,y2) =
    do x <- iff c x1 x2
       y <- iff c y1 y2
       return (x,y)

instance (Equal a, Equal b) => Equal (a,b) where
  equalStruct (x1,y1) (x2,y2) =
    do eq1 <- equalStruct x1 x2
       eq2 <- equalStruct y1 y2
       return (Tuple [eq1,eq2])

instance (Value a, Value b) => Value (a,b) where
  type Type (a,b) = (Type a, Type b)

  get (x,y) =
    do a <- get x
       b <- get y
       return (a,b)

--------------------------------------------------------------------------------

instance (Choice a, Choice b, Choice c) => Choice (a,b,c) where
  iff c (x1,y1,z1) (x2,y2,z2) =
    do x <- iff c x1 x2
       y <- iff c y1 y2
       z <- iff c z1 z2
       return (x,y,z)

instance (Equal a, Equal b, Equal c) => Equal (a,b,c) where
  equalStruct (x1,y1,z1) (x2,y2,z2) =
    do eq1 <- equalStruct x1 x2
       eq2 <- equalStruct y1 y2
       eq3 <- equalStruct z1 z2
       return (Tuple [eq1,eq2,eq3])

instance (Value a, Value b, Value c) => Value (a,b,c) where
  type Type (a,b,c) = (Type a, Type b, Type c)

  get (x,y,z) =
    do a <- get x
       b <- get y
       c <- get z
       return (a,b,c)

{-
================================================================================
-- type Lift
================================================================================
-}

data Lift a = The a | UNR
 deriving ( Eq, Ord, Show )

instance Applicative Lift where
  pure x = The x
  The f <*> The x = The (f x)
  _     <*> _     = UNR

instance Functor Lift where
  fmap f (The x) = The (f x)
  fmap f UNR     = UNR

instance Monad Lift where
  return x = The x
  The x >>= k = k x
  UNR   >>= k = UNR

instance Choice a => Choice (Lift a) where
  iff c (The x) (The y) =
    do z <- iff c x y
       return (The z)

  iff c (The x) _ =
    do return (The x)

  iff c _ (The y) =
    do return (The y)

  iff c _ _ =
    do return UNR

instance Equal a => Equal (Lift a) where
  equalStruct (The x) (The y) =
    do equalStruct x y
  
  equalStruct _ _ =
    do return Empty

instance Value a => Value (Lift a) where
  type Type (Lift a) = Maybe (Type a)
  
  get (The x) = Just `fmap` get x
  get UNR     = return Nothing
  
{-
================================================================================
-- type Val
================================================================================
-}

newtype Val a = Val [(Bit,a)] -- sorted on a
 deriving ( Eq, Ord, Show )

val :: a -> Val a
val x = Val [(tt,x)]

(=?) :: Eq a => Val a -> a -> Bit
Val []         =? x  = ff
Val ((a,y):xs) =? x
  | x == y      = a
  | otherwise   = Val xs =? x

domain :: Val a -> [a]
domain (Val xs) = map snd xs

newVal :: Ord a => [a] -> H (Val a)
newVal xs =
  do as <- lits (length ys)
     return (Val (as `zip` ys))
 where
  ys = map head . group . sort $ xs

  lits 1 =
    do return [tt]

  lits 2 =
    do a <- newBit
       return [a,nt a]

  lits n =
    do as <- sequence [ newBit | i <- [1..n] ]
       addClause as
       atMostOne n as
       return as

  atMostOne n as | n <= 5 =
    do sequence_ [ addClause [nt x, nt y] | (x,y) <- pairs as ]
   where
    pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs
    pairs _      = []

  atMostOne n as =
    do a <- newBit
       atMostOne (k+1) (a : take k as)
       atMostOne (n-k+1) (nt a : drop k as)
   where
    k = n `div` 2

choose :: Choice b => Val a -> (a -> H b) -> H b
choose (Val [(_,x)])    h = do h x
choose (Val ((a,x):xs)) h = do y <- h x; z <- choose (Val xs) h; iff a y z

--------------------------------------------------------------------------------

instance Ord a => Choice (Val a) where
  iff c (Val xs) (Val ys) =
    Val `fmap` sequence
      [ do d <- iff c a b
           return (d,x)
      | (ma, mb, x) <- align xs ys
      , let a = fromMaybe ff ma
            b = fromMaybe ff mb
      ]

instance Ord a => Equal (Val a) where
  equalStruct (Val xs) (Val ys) =
    ((Bit `fmap`) . andl) =<< sequence
      [ equal a b
      | (ma, mb, _) <- align xs ys
      , let a = fromMaybe ff ma
            b = fromMaybe ff mb
      ]

instance Value (Val a) where
  type Type (Val a) = a
  
  get (Val ((a,x):xs)) =
    do b <- get a
       if b then return x else get (Val xs)

--------------------------------------------------------------------------------

align :: Ord b => [(a,b)] -> [(a,b)] -> [(Maybe a, Maybe a, b)]
align ((a1,b1):abs1) ((a2,b2):abs2) =
  case b1 `compare` b2 of
    LT -> (Just a1, Nothing, b1) : align abs1 ((a2,b2):abs2)
    EQ -> (Just a1, Just a2, b1) : align abs1 abs2
    GT -> (Nothing, Just a2, b2) : align ((a1,b1):abs1) abs2

align [] ys = [(Nothing, Just a, b) | (a,b) <- ys]
align xs [] = [(Just a, Nothing, b) | (a,b) <- xs]

{-
================================================================================
-- type Nat
================================================================================
-}

newtype Nat = Nat [Bit]
 deriving ( Eq, Ord, Show )

newNat :: Int -> H Nat
newNat k =
  do xs <- sequence [ newBit | i <- [1..k] ]
     return (Nat xs)

pad :: Nat -> Nat -> (Nat, Nat)
pad (Nat xs) (Nat ys) = (Nat (xs ++ ffs n), Nat (ys ++ ffs m))
 where
  n = length xs
  m = length ys
  p = n `max` m
  ffs k = replicate (p-k) ff

leq :: Nat -> Nat -> H Bit
leq a b = cmp (reverse xs) (reverse ys)
 where
  (Nat xs, Nat ys) = pad a b

  cmp [] [] =
    do return tt

  cmp (x:xs) (y:ys) =
    do z <- newBit
       r <- cmp xs ys
       
       [x,    nt y] ==> [nt z]
       [nt x, y]    ==> [z]
       [x,    y,    r]    ==> [z]
       [nt x, nt y, r]    ==> [z]
       [x,    y,    nt r] ==> [nt z]
       [nt x, nt y, nt r] ==> [nt z]

       return z

fromInt :: Integer -> Nat
fromInt 0 = Nat []
fromInt n = Nat (Bool (odd n):xs) where Nat xs = fromInt (n `div` 2)

add :: Nat -> Nat -> H Nat
add (Nat xs) (Nat ys) = Nat `fmap` plus ff xs ys
 where
  plus c xs ys | c == ff && (null xs || null ys) =
    do return (xs ++ ys)

  plus c [] [] =
    do return [c]

  plus c [] ys =
    do plus c [ff] ys

  plus c xs [] =
    do plus c xs [ff]

  plus c (x:xs) (y:ys) =
    do c' <- atLeast 2 [c,x,y] []
       z  <- parity True [c,x,y] []
       zs <- plus c' xs ys
       return (z:zs)

  atLeast k (Bool True  : xs) ys = atLeast (k-1) xs ys
  atLeast k (Bool False : xs) ys = atLeast k xs ys
  atLeast k (x:xs)            ys = atLeast k xs (x:ys)
  atLeast 0 [] ys = return tt
  atLeast 1 [] ys = orl ys
  atLeast k [] ys =
    do c <- newBit
       sequence_ [ zs ==> [c] | zs <- pick k ys ]
       sequence_ [ [c] ==> zs | zs <- pick (length ys + 1 - k) ys ]
       return c
   where
    pick 0 ys     = [ [] ]
    pick k []     = []
    pick k (y:ys) = [ y:zs | zs <- pick (k-1) ys ] ++ pick k ys

  parity b (Bool True  : xs) ys = parity (not b) xs ys
  parity b (Bool False : xs) ys = parity b xs ys
  parity b (x:xs)            ys = parity b xs (x:ys)
  parity b [] []  = return (if b then ff else tt)
  parity b [] [y] = return (if b then y else nt y)
  parity b [] ys  =
    do c <- newBit
       sequence_ [ addClause zs | zs <- par b c ys ]
       return c
   where
    par b c []     = [ [nt c] | b ] ++ [ [c] | not b ]
    par b c (y:ys) = [ nt y : zs | zs <- par (not b) c ys ] ++
                     [ y : zs | zs <- par b c ys ]

--------------------------------------------------------------------------------

instance Choice Nat where
  iff c a b =
    Nat `fmap` sequence [ iff c x y | (x,y) <- xs `zip` ys ]
   where
    (Nat xs, Nat ys) = pad a b

instance Equal Nat where
  equalStruct a b =
    ((Bit `fmap`) . andl) =<< sequence [ equal x y | (x,y) <- xs `zip` ys ]
   where
    (Nat xs, Nat ys) = pad a b

instance Value Nat where
  type Type Nat = Int
  
  get (Nat []) =
    do return 0

  get (Nat (x:xs)) =
    do b <- get x
       n <- get (Nat xs)
       return (if b then 1+2*n else 2*n)

{-
================================================================================
-- type Data
================================================================================
-}

data Data l arg = Con (Val l) arg
 deriving ( Eq, Ord, Show )

switch :: (Ord l, Choice b) => Data l arg -> (l -> arg -> H b) -> H b
switch (Con cn arg) h = choose cn (\cn -> h cn arg)

class EqualArg l where
  equalArg :: l -> Struct Bit -> [Struct Bit]

--------------------------------------------------------------------------------

instance (Ord l, Choice arg) => Choice (Data l arg) where
  iff c (Con cn1 arg1) (Con cn2 arg2) =
    do cn  <- iff c cn1 cn2
       arg <- iff c arg1 arg2
       return (Con cn arg)

instance (Ord l, EqualArg l, Equal arg) => Equal (Data l arg) where
  equalStruct (Con c1 arg1) (Con c2 arg2) =
    do eq <- equal c1 c2
       eqstr <- equalStruct arg1 arg2
       eqs <- choose c1 $ \l -> do eq <- andl (concatMap bits (equalArg l eqstr))
                                   orl [nt (c1 =? l), eq]
       Bit `fmap` andl [eq,eqs]

{-
================================================================================
-- type List
================================================================================
-}

data L = Nil | Cons
 deriving ( Eq, Ord, Show )

newtype List a = List (Data L (Lift (a, List a)))
 deriving ( Choice, Equal )

nil       = List $ Con (val Nil)  UNR
cons x xs = List $ Con (val Cons) (The (x, xs))

instance Value a => Value (List a) where
  type Type (List a) = [Type a]
  
  get (List (Con cn args)) =
    do l <- get cn
       case l of
         Nil  -> do return []
         Cons -> do ~(Just (a,as)) <- get args
                    return (a:as)

instance EqualArg L where
  equalArg Nil  _              = []
  equalArg Cons (Tuple [x,xs]) = [x,xs]

caseList (List d) nl cns =
  switch d $ \l args ->
    case (l, args) of
      (Nil, _)           -> nl
      (Cons, The (x,xs)) -> cns x xs

--------------------------------------------------------------------------------
{-
apa =
  do s <- M.newSolver
     r <- run bepa s []
     print r
     M.deleteSolver s

bepa =
  do a <- newNat 3
     b <- newNat 3
     eq <- equal a b
     addClause [nt eq]
     let l = cons a (cons b nil)
     eq2 <- equal l l
     addClause [nt eq2]
     check
     xs <- get l
     withSolver $ \_ -> print xs
-}
--------------------------------------------------------------------------------


module Size where

import Symbolic
import MiniSat as M
import Nat as N

newtype BitBag = Bag [Bit]
 deriving ( Eq, Ord, Show )

bag0, bag1 :: BitBag
bag0 = Bag []
bag1 = Bag [tt]

union :: BitBag -> BitBag -> BitBag
Bag xs `union` Bag ys = Bag (xs ++ ys)

instance Choice BitBag where
  iff c (Bag xs) (Bag ys) =
    do zs <- sequence (zipWith (iff c) (pad xs) (pad ys))
       return (Bag zs)
   where
    n      = length xs `max` length ys
    pad as = as ++ replicate (n-length as) ff

class Sized a where
  size :: a -> H (Struct BitBag)

instance (Ord l, Argument l, Sized arg) => Sized (Data l arg) where
  size (Con cn arg) =
    do sxs <- size arg
       bb <- choose cn $ \c ->
         return (foldr union bag0 (concatMap collapse (argument c sxs)))
       return (Bit (bag1 `union` bb))

instance Sized a => Sized (Lift a) where
  size (The x) = size x
  size UNR     = return Empty

instance Sized a => Sized (List a) where
  size (List d) = size d

instance (Sized a, Sized b) => Sized (a,b) where
  size (x,y) =
    do sx <- size x
       sy <- size y
       return (Tuple [sx,sy])

instance (Sized a, Sized b, Sized c) => Sized (a,b,c) where
  size (x,y,z) =
    do sx <- size x
       sy <- size y
       sz <- size z
       return (Tuple [sx,sy,sz])

bagSize :: BitBag -> H N.Nat
bagSize (Bag xs) =
  withSolver $ \s ->
    do true <- M.newLit s
       M.addClause s [true]
       let lit (Bool True) = true
           lit (Lit x)     = x
       N.count s [ lit x | x <- xs, x /= Bool False ]


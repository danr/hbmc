{-# LANGUAGE ScopedTypeVariables #-}
module TipData where

import Tip.Types as T
import Tip.Fresh
import Data.List

type DataInfo a = [(a,(a,[Int]))]

dataInfo :: forall a . Eq a => Datatype a -> (DataInfo a,[Type a])
dataInfo (Datatype tc _tvs cons) = (indexes,types)
  where
    types :: [Type a]
    types = merge [ args | Constructor _ args <- cons ]

    indexes =
        [ (c,(tc,index args (types `zip` [0..])))
        | Constructor c args <- cons
        ]

    index :: [Type a] -> [(Type a,Int)] -> [Int]
    index []     _  = []
    index (a:as) ts = i : index as (l ++ r)
      where
        (l,(_,i):r) = break ((a ==) . fst) ts

-- | Merging
merge :: Eq a => [[a]] -> [a]
merge []       = []
merge (xs:xss) = help xs (merge xss)
  where
    help :: Eq a => [a] -> [a] -> [a]
    help xs (y:ys) = y:help (delete y xs) ys
    help xs []     = xs

class Name a => Proj a where
  proj   :: a -> Int -> a
  unproj :: a -> Maybe (a,Int)


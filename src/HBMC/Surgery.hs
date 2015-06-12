{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module HBMC.Surgery where

import Tip.Pretty
import Text.PrettyPrint

import Data.List (partition)

data Surgery a b c = Surgery { view :: a, perform :: b -> c }
  deriving Functor

spartition :: [Surgery a b c] -> ([a],[b -> c])
spartition [] = ([],[])
spartition (Surgery a f:ss) = let (as,fs) = spartition ss in (a:as,f:fs)

andList :: [Surgery a b c] -> Surgery [a] [b] [c]
andList (spartition -> (as,fs)) = Surgery as (zipWith ($) fs)

orList :: [Surgery a b c] -> Surgery [a] (Int,b) c
orList (spartition -> (as,fs)) = Surgery as (\(i,b) -> (fs !! i) b)

mapRes :: (c -> c') -> Surgery a b c -> Surgery a b c'
mapRes = fmap

mapFrom :: (b' -> b) -> Surgery a b c -> Surgery a b' c
mapFrom f (Surgery a g) = Surgery a (g . f)

mapInit :: (a -> a') -> Surgery a b c -> Surgery a' b c
mapInit f (Surgery a g) = Surgery (f a) g

-- | And-Or Tree
data AOT a = And [AOT a] | Or [AOT a] | Unit a
  deriving (Eq,Ord,Show,Functor)

collectAnd,collectOr :: AOT a -> [AOT a]

-- collectAnd (And es) = es
collectAnd (And es) = concatMap collectAnd es
collectAnd (Or [e]) = collectOr e
collectAnd e        = [e]

-- collectOr (Or es)   = es
collectOr (Or es)   = collapseAnd1 (concatMap collectOr es)
collectOr (And [e]) = collectOr e
collectOr e         = [e]

collapseAnd1 es
  | null and1s = rest
  | otherwise  = And []:rest
  where
  (and1s, rest) = partition (\ e -> case e of And [] -> True; _ -> False) es

tri :: Pretty a => Doc -> Doc -> [a] -> Doc
tri a m []  = a
tri a m [x] = pp x
tri a m es  = parens (m $\ sep (map pp es))

instance Pretty a => Pretty (AOT a) where
  pp e@Or{}       = tri "false" "or" (collectOr e)
  pp e@And{}      = tri "true" "and" (collectAnd e)
  pp (Unit a)     = brackets (pp a)

-- | And-Or Tree Answer
data AOTA a = AndA [AOTA a] | OrA Int (AOTA a) | UnitA a
  deriving (Eq,Ord,Show,Functor)

type AOSurgery a b c = Surgery (AOT a) (AOTA b) c

ret :: c -> Surgery () () c
ret c = Surgery () (\() -> c)

retAO :: c -> AOSurgery a b c
retAO = mapInit (\() -> And []) . mapFrom (\(AndA []) -> ()) . ret

andAO :: [AOSurgery a b c] -> AOSurgery a b [c]
andAO = mapInit And . mapFrom (\ (AndA as) -> as) . andList

orAO :: [AOSurgery a b c] -> AOSurgery a b c
orAO = mapInit Or . mapFrom (\ (OrA i a) -> (i,a)) . orList


{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
module HBMC.Surgery where

import Tip.Pretty
import Text.PrettyPrint

import Data.List (partition)

data Surgery a b c where
  Surgery :: a i -> (b i -> c) -> Surgery a b c

view :: Surgery a b c -> Indexed a
view (Surgery a _) = Indexed a

viewAOT :: AOSurgery a b c -> AOView a
viewAOT (Surgery a _) = viewAO a

instance Functor (Surgery a b) where
  fmap g (Surgery a f) = Surgery a (g . f)

mapRes :: (c -> c') -> Surgery a b c -> Surgery a b c'
mapRes = fmap

middle :: (forall i . (a i -> a' i, b' i -> b i)) -> Surgery a b c -> Surgery a' b' c
middle fg (Surgery a h) = case fg of (f,g) -> Surgery (f a) (h . g)

data AOView a = ViewAnd [AOView a] | ViewOr [AOView a] | ViewUnit a

viewAnd, viewOr :: AOView a -> AOView a -> AOView a
viewAnd (ViewAnd xs) (ViewAnd ys) = ViewAnd (xs ++ ys)
viewAnd x            (ViewAnd ys) = ViewAnd ([x]++ ys)
viewAnd (ViewAnd xs) y            = ViewAnd (xs ++[y])
viewAnd x            y            = ViewAnd ([x]++[y])

viewOr (ViewOr xs) (ViewOr ys) = viewOr' (xs ++ ys)
viewOr x           (ViewOr ys) = viewOr' ([x]++ ys)
viewOr (ViewOr xs) y           = viewOr' (xs ++[y])
viewOr x           y           = viewOr' ([x]++[y])

viewOr' xs
  | null [ () | ViewAnd [] <- xs ] = ViewOr xs
  | otherwise                      = ViewOr (ViewAnd []:[ x | x <- xs, case x of ViewAnd [] -> False; _ -> True ])

viewAO :: AOT a i -> AOView a
viewAO (And a b) = viewAnd (viewAO a) (viewAO b)
viewAO (Or  a b) = viewOr  (viewAO a) (viewAO b)
viewAO (Unit a)  = ViewUnit a
viewAO Noop      = ViewAnd []

instance Pretty a => Pretty (AOT a i) where
  pp = pp . viewAO

instance Pretty a => Pretty (AOView a) where
  pp (ViewOr  as) = tri "false" "or" (map pp as)
  pp (ViewAnd as) = tri "true" "and" (map pp as)
  pp (ViewUnit a) = brackets (pp a)

tri :: Doc -> Doc -> [Doc] -> Doc
tri a m []  = a
tri a m [x] = x
tri a m es  = parens (m $\ sep es)

mapAO :: (a -> a') -> AOT a i -> AOT a' i
mapAO f (And a b) = And (mapAO f a) (mapAO f b)
mapAO f (Or a b)  = Or (mapAO f a) (mapAO f b)
mapAO f (Unit a)  = Unit (f a)
mapAO _ Noop      = Noop

mapInit :: (a -> a') -> AOSurgery a b c -> AOSurgery a' b c
mapInit f = middle (mapAO f,id)

data AOT a i where
  And  :: AOT a i -> AOT a j -> AOT a (i,j)
  Or   :: AOT a i -> AOT a j -> AOT a (Either i j)
  Unit :: a -> AOT a i
  Noop :: AOT a ()

data AOTA b i where
  AndA   :: AOTA b i -> AOTA b j -> AOTA b (i,j)
  LeftA  :: AOTA b i -> AOTA b (Either i j)
  RightA :: AOTA b j -> AOTA b (Either i j)
  UnitA  :: b -> AOTA b i
  NoopA  :: AOTA b ()

type AOSurgery a b c = Surgery (AOT a) (AOTA b) c

data Indexed a = forall i . Indexed (a i)

retAO :: c -> AOSurgery a b c
retAO c = Surgery Noop (\ NoopA -> c)

both :: AOSurgery a b c -> AOSurgery a b c' -> AOSurgery a b (c,c')
both (Surgery a f) (Surgery a' f') = Surgery (And a a') (\ (AndA b b') -> (f b, f' b'))

oneOf :: AOSurgery a b c -> AOSurgery a b c' -> AOSurgery a b (Either c c')
oneOf (Surgery a f) (Surgery a' f') = Surgery (Or a a') $ \ lr -> case lr of LeftA b   -> Left (f b)

andAO :: [AOSurgery a b c] -> AOSurgery a b [c]
andAO = foldr (\ u v -> fmap (uncurry (:)) (both u v)) (retAO [])

orAO :: [AOSurgery a b c] -> AOSurgery a b c
orAO [] = error "orAO: empty list"
orAO xs = foldr1 (\ u v -> fmap (either id id) (oneOf u v)) xs

orAOf :: AOSurgery a b c -> [AOSurgery a b c] -> AOSurgery a b c
orAOf c [] = c
orAOf _ xs = orAO xs


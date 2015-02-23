{-# LANGUAGE TypeFamilies #-}
module Str where

import Symbolic
import Data.List ( tails )

--------------------------------------------------------------------------------

newtype Str a = Str [Val (Maybe a)]
 deriving ( Eq, Ord, Show )

empty :: Str a
empty = Str []

unit :: a -> Str a
unit x = Str [val (Just x)]

(+++) :: Str a -> Str a -> Str a
Str xs +++ Str ys = Str (xs ++ ys)

instance Ord a => Choice (Str a) where
  iff b (Str xs) (Str ys) =
    do zs <- sequence
             [ iff b x y
             | (x,y) <- zipp xs ys
             ]
       return (Str zs)
   where
    zipp []     []     = []
    zipp xs     []     = zipp xs [val Nothing]
    zipp []     ys     = zipp [val Nothing] ys
    zipp (x:xs) (y:ys) = (x,y) : zipp xs ys

instance Value (Str a) where
  type Type (Str a) = [a]
  
  get (Str xs) =
    do ms <- sequence [ get x | x <- xs ]
       return [ x | Just x <- ms ]

--------------------------------------------------------------------------------

concatt :: [Str a] -> Str a
concatt xss = Str (concat [ xs | Str xs <- xss ])

(=:) :: Eq a => Str a -> [a] -> H ()
Str xs =: ys =
  do a:_ <- match xs ys
     addClause [a]
 where
  match [] ys =
    do return ([ ff | y <- ys ] ++ [ tt ])
  
  match (x:xs) ys =
    do as <- match xs ys
       cs <- sequence
             [ do here  <- andl [x =? Just y, b2]
                  there <- andl [x =? Nothing, b1]
                  orl [here, there]
             | (b1:b2:_,y) <- tails as `zip` ys
             ]
       c  <- andl [x =? Nothing, last as]
       return (cs ++ [c])

--------------------------------------------------------------------------------


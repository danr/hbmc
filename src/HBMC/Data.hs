{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
module HBMC.Data where

import Tip.Types
import Tip.Fresh
import Data.List

import Tip.Utils (recursive)
import Tip.Core  (defines,uses,constructor)
import Tip.Pretty

import HBMC.Identifiers

import Tip.Core (Datatype(..),Constructor(..))
import Control.Applicative

import qualified HBMC.Object as O

import Data.Map (Map)
import qualified Data.Map as M

type Proj a = (Type a,Int)

data DataInfo a =
  DataInfo
    { tr_con       :: Global a -> O.Cons a
    , projs_of_con :: Global a -> [Proj a]
    , tr_type      :: Type a -> O.Type a
    }

dataInfo :: forall a . Ord a => [Datatype a] -> DataInfo a
dataInfo dts = DataInfo{..}
  where
  tr_con :: Global a -> O.Cons a
  tr_con = fst . (con_map M.!)

  projs_of_con :: Global a -> [Proj a]
  projs_of_con = snd . (con_map M.!)

  con_map :: Map (Global a) (O.Cons a,[Proj a])
  con_map =
    M.fromList
      [ (constructor dt c []
        ,(O.Cons cname [ tr_type t | (_,t) <- args ] (tr_type (TyCon dname []))
         ,number [ t | (_,t) <- args ]
         )
        )
      | dt@(Datatype dname _ cons) <- dts
      , c@(Constructor cname _ args) <- cons
      ]

  tr_type :: Type a -> O.Type a
  tr_type = (type_map M.!)

  type_map =
    M.fromList
      [ (TyCon dname []
        ,O.Type dname [] [tr_con (constructor dt c []) | c <- cons ]
        )
      | dt@(Datatype dname _ cons) <- dts
      ]


-- > number [True,False,True,False,False]
-- [(True,0),(False,0),(True,1),(False,1),(False,2)]
number :: Eq a => [a] -> [(a,Int)]
number = reverse . go . reverse
  where
  go []     = []
  go (x:xs) = (x,sum [ 1 | y <- xs, x == y ]):go xs


{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module HBMC.Data where

import Tip.Types
import Tip.Fresh
import Data.List

import Tip.Utils (recursive)
import Tip.Core  (defines,uses)
import Tip.Pretty

import HBMC.Identifiers
import HBMC.Lib hiding (Type,caseData)

import Tip.Core (Datatype(..),Constructor(..))
import Control.Applicative

type DataInfo a = [(a,(a,[Int]))]

dataDescs :: forall a . (Show a,PrettyVar a,Ord a) => Bool -> [Datatype a] -> a -> LiveDesc a
dataDescs lazy_datatypes dts = lkup_desc
  where
  rec_dts = recursiveDatatypes dts
  lkup_desc x = case lookup x tbl of Just desc -> desc
                                     Nothing   -> error $ "Data type not found:" ++ varStr x ++ " (" ++ show x ++ ")"
  tbl =
    [ (tc,
       maybe_thunk $ DataDesc (varStr tc) [ c | Constructor c _ _ <- cons ]
       [ case ty of
           TyCon tc [] ->
             ( [ c | (c,(_,ixs)) <- indexes, i `elem` ixs ]
             , lkup_desc tc)
       | (i,ty) <- [0..] `zip` types ])
    | dt@(Datatype tc [] cons) <- dts
    , let (indexes,types) = dataInfo dt
    , let maybe_thunk | tc `elem` rec_dts || lazy_datatypes = ThunkDesc
                      | otherwise                           = id
    ]

recursiveDatatypes :: Ord a => [Datatype a] -> [a]
recursiveDatatypes = recursive defines uses

dataInfo :: forall a . Eq a => Datatype a -> (DataInfo a,[Type a])
dataInfo (Datatype tc _tvs cons) = (indexes,types)
  where
    types :: [Type a]
    types = merge [ map snd args | Constructor _ _ args <- cons ]

    indexes =
        [ (c,(tc,index (map snd args) (types `zip` [0..])))
        | Constructor c _ args <- cons
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


{-# LANGUAGE ScopedTypeVariables #-}
module HBMC.Identifiers where

import Tip.Core
import Tip.Pretty
import Tip.Fresh
import Tip.Haskell.Translate -- Why is HsId exported from here?!
import Tip.Utils.Rename

import Data.Generics.Geniplate

import Data.Set (Set)
import qualified Data.Set as S

toHsId :: Var -> HsId Var
toHsId (Prelude x)  = Qualified "Prelude" (Just "P") x
toHsId (Api x)      = Qualified "LibHBMC" (Just "H") x
toHsId (Proj x)     = Qualified "LibHBMC" (Just "H") ("proj" ++ show (x+1))
toHsId (Var "main") = Exact "main"
toHsId x            = Other x

data Var
  = Var String
  | Con String
  | Api String
  | Prelude String
  | Proj Int
  | Refresh Var Int
 deriving (Show,Eq,Ord)

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i
varMax _             = 0

instance PrettyVar Var where
  varStr x =
    case x of
      Var ""      -> "x"
      Var x       -> x
      Con x       -> varStr (Var x)
      Refresh v i -> varStr v
      Proj i      -> "proj" {- <> pp x <> "_" -} ++ show (i+1)
      Api x       -> x
      Prelude x   -> x

renameTheory :: forall a . (Ord a,PrettyVar a) => Theory a -> Theory Var
renameTheory thy = renameWith disambigId thy
 where
  cons = S.fromList [ c | Constructor c _ _ <- universeBi thy ]

  disambigId :: a -> [Var]
  disambigId i = vs : [ Refresh vs x | x <- [0..] ]
    where
      var_or_con
        | i `S.member` cons = Con
        | otherwise         = Var

      vs = case varStr i of
             [] -> var_or_con "x"
             xs -> var_or_con xs

instance Name Var where
  fresh     = refresh (Var "")
  refresh v = Refresh v `fmap` fresh
  getUnique = varMax


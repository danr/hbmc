module ShowBinLists where

import Tip.Prelude
import qualified Prelude

data B = I | O deriving Prelude.Show

shw Z             = []
shw x | even x    = O : shw (half x)
      | otherwise = I : shw (half x)

rd (I : xs) = S (double (rd xs))
rd (O : xs) = double (rd xs)
rd []       = Z

x # y = rd (shw x ++ shw y)

prop_assoc x y z = x#(y#z) === (x#y)#z
sat_comm   x y   = x#y === y#x



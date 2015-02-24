module HBMC(module HBMC,module Tip.DSL) where

import Tip.DSL

{-# NOINLINE label #-}
label :: label -> a -> a
label l e = e

{-# NOINLINE memo #-}
memo :: a -> a
memo e = e

{-# NOINLINE check #-}
check :: a -> a
check e = e


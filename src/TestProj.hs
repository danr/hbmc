module TestProj where

import Tip

data ABC = A | B ABC | C ABC

f x z = case x of
        A   -> A
        B u -> f u z
        C u -> f u x

prop_f x y = f x y === f y x

g (x:y:zs) = g zs
g _        = []

prop_g xs ys = g xs === g ys

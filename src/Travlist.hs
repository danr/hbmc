module Travlist where

import Tip

data ABC = A | B | C

travlist (A:xs) = B:travlist xs
travlist (B:xs) = A:travlist xs
travlist (C:xs) = C:xs
travlist []     = []

prop xs = neg (travlist xs === [A,B,C,A,B])


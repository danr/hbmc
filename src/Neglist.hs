module Neglist where

import Tip

-- neglist (x:xs) = not x:neglist xs
neglist (True:xs)  = False:neglist xs
neglist (False:xs) = True:neglist xs
neglist []         = []

prop xs = neg (neglist xs === [True,False,True,False])


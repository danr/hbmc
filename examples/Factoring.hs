module Factoring where

import Tip.Prelude
import qualified Prelude

pred (S x) = x
pred Z     = Z

six    = S (S (S (S (S (S Z)))))
twenty = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))
twelve = six + six
nine   = S (S (S (S (S (S (S (S (S Z))))))))
four   = S (S (S (S Z)))
ten    = S nine

-- factors_105 x y z = question (x * (y * z) === ten * ten + S four .&&. x > S Z .&&. y > S Z .&&. z > S Z)

-- factors_35 x y = question (x * y === pred (six * six) .&&. x > S Z .&&. y > S Z)
-- factors_143 x y = question (x * y === pred (twelve * twelve) .&&. x > S Z .&&. y > S Z)
-- factors_391 x y = question (x * y === (twenty * twenty) - nine .&&. x > S Z .&&. y > S Z)
-- factors_385 x y z = question (x * (y * z) === pred twenty * pred twenty + (twenty + four) .&&. x > S Z .&&. y > S Z .&&. z > S Z)

simple x = question (x * x =/= x)

module Parse where

import Tip.Prelude
import qualified Prelude as P

data Char = PAR1 | PAR2 | PLUS | MULT | CHARX
          | DIG0 | DIG1 | DIG2
          | DIG3 | DIG4 | DIG5
          | DIG6 | DIG7 | DIG8 | DIG9
 deriving ( P.Show )

PAR1 `eqC` PAR1 = True
PAR2 `eqC` PAR2 = True
PLUS `eqC` PLUS = True
MULT `eqC` MULT = True
CHARX `eqC` CHARX = True
DIG0 `eqC` DIG0 = True
DIG1 `eqC` DIG1 = True
DIG2 `eqC` DIG2 = True
DIG3 `eqC` DIG3 = True
DIG4 `eqC` DIG4 = True
DIG5 `eqC` DIG5 = True
DIG6 `eqC` DIG6 = True
DIG7 `eqC` DIG7 = True
DIG8 `eqC` DIG8 = True
DIG9 `eqC` DIG9 = True
_    `eqC` _    = False

data Expr
  = X
  | Add Expr Expr
  | Mul Expr Expr
  | Num Nat
 deriving ( P.Show )

type String = [Char]

show :: Expr -> String
show X         = [CHARX]
show (Add a b) = show a ++ [PLUS] ++ show b
show (Mul a b) = showF a ++ [MULT] ++ showF b
show (Num n)   = showNum n

showF a@(Add _ _) = PAR1 : show a ++ [PAR2]
showF a           = show a

showNum Z = [DIG0]
showNum n = num [] n
 where
  num ds Z = ds
  num ds n = num (a:ds) n'
   where
    (a,n') = mod10 n

mod10 :: Nat -> (Char,Nat)
mod10 n =
  case min10 n of
    Left d   -> (d, Z)
    Right n' -> let (d,n'') = mod10 n' in (d, S n'')

min10 n =
  case n of
    Z -> Left DIG0
    S n1 ->
      case n1 of
        Z -> Left DIG1
        S n2 -> 
          case n2 of
            Z -> Left DIG2
            S n3 -> 
              case n3 of
                Z -> Left DIG3
                S n4 -> 
                  case n4 of
                    Z -> Left DIG4
                    S n5 -> 
                      case n5 of
                        Z -> Left DIG5
                        S n6 -> 
                          case n6 of
                            Z -> Left DIG6
                            S n7 -> 
                              case n7 of
                                Z -> Left DIG7
                                S n8 -> 
                                  case n8 of
                                    Z -> Left DIG8
                                    S n9 -> 
                                      case n9 of
                                        Z -> Left DIG9
                                        S n9 -> Right n9

--min10 (S (S (S (S (S (S (S (S (S (S n)))))))))) = Right n

[] `eqS` [] = True
(x:xs) `eqS` (y:ys) = x `eqC` y && xs `eqS` ys
_ `eqS` _ = False

prop1 e = show e === [CHARX,PLUS,DIG0,MULT,CHARX] ==> True === False
prop2 e = show e === [PAR1,CHARX,PLUS,DIG1,DIG3,PAR2,MULT,CHARX] ==> True === False
prop3 e = show e === [PAR1,PAR1,CHARX,PLUS,DIG5,PAR2,PLUS,DIG7,PAR2,MULT,CHARX] ==> True === False

depth (S d) (Add a b) = depth d a && depth d b
depth (S d) (Mul a b) = depth d a && depth d b
depth d     (Num n)   = depthN d n
depth _     X         = True
depth _     _         = False

depthN (S d) (S n) = depthN d n
depthN _     Z     = True
depthN _     _     = False



e = Add X (Num Z `Mul` X)

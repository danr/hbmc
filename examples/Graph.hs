module Graph where

import qualified Prelude as P
import Tip.Prelude

enumFromTo :: Nat -> Nat -> [Nat]
enumFromTo n m
  | n >= m    = []
  | otherwise = n : enumFromTo (S n) m

petersen Z = []
petersen n@(S pn) =
  concat
    [ [(u,v),(n+u,n+v)]
    | (u,v) <- (pn,Z) : [ (x,S x) | x <- enumFromTo Z pn ]
    ] ++
  [ (x,n+x) | x <- enumFromTo Z n ]

dodeca Z = []
dodeca n@(S pn) =
     ((pn,Z) : [ (x,S x) | x <- enumFromTo Z pn ])
  ++ ([ (x,n+x) | x <- enumFromTo Z n ])
  ++ ([ (n+x,n+n+x) | x <- enumFromTo Z n ])
  ++ ((n,n+n+pn):[ (n+S x,n+n+x) | x <- enumFromTo Z pn ])
  ++ ([ (n+n+x,n+n+n+x) | x <- enumFromTo Z n ])
  ++ ((n+n+n+pn,n+n+n) : [ (n+n+n+x,n+n+n+S x) | x <- enumFromTo Z pn ])

{-
knight n =
  catMaybes
  [ case (tr u v,tr x y) of
      (Just p1,Just p2) -> Just (p1,p2)
      _ -> Nothing
  | ((u,v),(x,y)) <-
    concat
      [ [ ((x,y),(t x,s x))
        , ((x,y),(s x,t x))
        , ((x,y),(t x,p x))
        , ((x,y),(p x,t x))
        , ((x,y),(d x,p x))
        , ((x,y),(p x,d x))
        , ((x,y),(d x,s x))
        , ((x,y),(s x,d x))
        ]
      | x <- enumFromTo (S (S Z)) (S (S n))
      , y <- enumFromTo (S (S Z)) (S (S n))
      ]
  ]
  where t x = S (S x)
        s x = S x
        p x = pred x
        d x = pred (pred x)

tr (S (S x)) (S (S y)) = Just (S (S (S (S (S (S (S (S Z))))))) * y + x)
tr _ _ = Nothing

catMaybes xs = [ x | Just x <- xs ]

pred (S x) = x
pred Z     = Z
-}

type Graph = [(Nat,Nat)]

type Assignment = [Nat]

colouring :: Graph -> Assignment -> Bool
colouring g a =
  and
    [ case (index a u,index a v) of
       (Just c1,Just c2) -> c1 /= c2
       _                 -> False
    | (u,v) <- g
    ]

prop_p5 a = question (colouring (petersen n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S Z))))

prop_p7 a = question (colouring (petersen n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S (S (S Z))))))

prop_p9 a = question (colouring (petersen n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S (S (S (S (S Z))))))))

prop_p11 a = question (colouring (petersen n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S (S (S (S (S (S (S Z))))))))))

prop_p21 a = question (colouring (petersen n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))

prop_p31 a = question (colouring (petersen n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))

prop_d5 a = question (colouring (dodeca n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S Z))))

prop_d7 a = question (colouring (dodeca n) a && and [ c < S (S (S Z)) | c <- a ])
  where n = S (S (S (S (S (S (S Z))))))

path :: [Nat] -> Graph -> Bool
path (x:y:xs) g = or [ u == x && v == y || u == y && v == x | (u,v) <- g ] && path (y:xs) g
path _        _ = True

tour :: [Nat] -> Graph -> Bool
tour []       []           = True
tour (_:_)    []           = False
tour []       (_:_)        = False
tour p@(x:xs) g@((u,v):vs) = x == last x xs && path (x:xs) g && unique xs && length p == S (S (maximum (max u v) vs))

last x []     = x
last x (y:ys) = last y ys

maximum x [] = x
maximum x ((y,z):yzs) = maximum (max x (max y z)) yzs

prop_t3 p = question (tour p (dodeca n))
   where n = S (S (S Z))

prop_t5 p = question (tour p (dodeca n))
   where n = S (S (S (S (S Z))))

prop_tp5 p = question (tour p (petersen n))
   where n = S (S (S (S (S Z))))

data B = I | O

bin Z             = []
bin x | even x    = O : bin (half x)
      | otherwise = I : bin (half x)

type Bin = [B]

type BGraph = [(Bin,Bin)]

beq :: Bin -> Bin -> Bool
beq [] [] = True
beq (I:xs) (I:ys) = beq xs ys
beq (O:xs) (O:ys) = beq xs ys
beq _ _ = False

belem :: Bin -> [Bin] -> Bool
belem x xs = or [ beq x y | y <- xs ]

bunique :: [Bin] -> Bool
bunique []     = True
bunique (x:xs) = not (belem x xs) && bunique xs

bgraph :: Graph -> BGraph
bgraph g = [ (bin u,bin v) | (u,v) <- g ]

bpath :: [Bin] -> BGraph -> Bool
bpath (x:y:xs) g = or [ beq u x && beq v y || beq u y && beq v x | (u,v) <- g ] && bpath (y:xs) g
bpath _        _ = True

btour :: [Bin] -> Graph -> Bool
btour []       []           = True
btour (_:_)    []           = False
btour []       (_:_)        = False
btour p@(x:xs) g@((u,v):vs) = beq x (last x xs) && bpath (x:xs) (bgraph g) && bunique xs && length p == S (S (maximum (max u v) vs))

prop_bt3 p = question (btour p (dodeca n))
   where n = S (S (S Z))

prop_bt4 p = question (btour p (dodeca n))
   where n = S (S (S (S Z)))

prop_bt5 p = question (btour p (dodeca n))
   where n = S (S (S (S (S Z))))

prop_btp5 p = question (btour p (petersen n))
   where n = S (S (S (S (S Z))))

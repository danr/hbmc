{-

Use magic lets:

  case b of True  -> f (g x)
            False -> g (f y)

=>(lift f)

  case b of True  -> let arg_f = g x in f arg_f
            False -> let arg_f = y in g (f arg_f)

=>(lift g)(don't lift f again: applied to magic argument (or same argument))

  case b of True  -> let arg_f = let arg_g = x in g arg_g in f arg_f
            False -> let arg_f = y in let arg_g = f arg_f in g arg_g

=>(let/let)

  case b of True  -> let arg_g = x in let arg_f = g arg_g in f arg_f
            False -> let arg_f = y in let arg_g = f arg_f in g arg_g


=>(pull magic let)

  let arg_g = case b of True -> x
                        False -> f arg_f

  case b of True  -> let arg_f = g arg_g in f arg_f
            False -> let arg_f = y       in g arg_g

=>(pull magic let)

  let arg_g = case b of True  -> x
                        False -> f arg_f

  let arg_f = case b of True  -> g arg_g
                        False -> y

  case b of True  -> f arg_f
            False -> g arg_g


-----
   if b then merge xs y else merge x ys
=> if b then let a1 = xs; a2 = y;  in merge a1 a2
        else let a1 = x;  a2 = ys; in merge a1 a2
=> let a1 = if b then xs else y
   let a2 = if b then x else ys
   in  merge a1 a2
-}
{-# LANGUAGE GADTs #-}
module HBMC.Merge where

import HBMC.Surgery
import Tip.Core

-- | Assumes commuteMatch has happened, only wades through initial lets
findPoints :: Expr a -> AOSurgery (Global a,[Expr a]) (Expr a) (Expr a,Expr a)
findPoints e0 =
  case e0 of
    Let x e1 e2 -> mapRes (\ (e2',e2_bot) -> (Let x e1 e2,Let x e1 e2_bot)) (findPoints e2)
    _           -> matchPoints e0

-- todo: make this some proper bottom
bot :: Expr a
bot = Builtin At :@: []

-- | Performs surgery on the match points.
--   Two expressions are returned, the first is the actual new expression,
--   whereas the second is merely the skeleton
--
{-


     case x of
        K y -> f (f y)
        J z -> g (f z)

   =>



     (case x of
       K y -> y
       J z -> z
     ,case x of
       K y -> f y
       J z -> g z
     )

     (case x of
       K y -> farg
       J z -> farg
     ,case x of
       K y -> f farg
       J z -> g farg
     )


     let arg = case x of
                  K y -> y
                  J z -> z
     let farg = f arg
     in  case x of
            K y -> f farg
            J z -> g farg

----------------

    case s of
      A -> f (g (h x))
      B -> g (h (f x))
      C -> h (f (g x))

    let f' = f (case s of
               A -> g'
               B -> x
               C -> g')
        g' = g (case s of
               A -> h'
               B -> h'
               C -> x)
        h' = h (case s of
               A -> x
               B -> f'
               C -> f')
    in  case s of
          A -> f'
          B -> g'
          C -> h'

---------------
    case s of
      A -> f (g (h x))
      B -> g (h (f x))
      C -> h (f (g x))
=>
    let farg = f arg_f {- comes later, I promise! -}
    case s of
      A -> let arg_f = g (h x) in farg
      B -> let arg_f =      x  in g (h farg)
      C -> let arg_f =    g x  in h farg
=>
    let farg = f arg_f
    let garg = g arg_g
    case s of
      A -> let arg_f = garg in let arg_g = h x    in farg
      B -> let arg_f =    x in let arg_g = h farg in garg
      C -> let arg_f = garg in let arg_g = x      in h farg
=>
    let farg = f arg_f
    let garg = g arg_g
    let harg = h arg_h
    case s of
      A -> let arg_f = garg in let arg_g = harg let arg_h =  x    in farg
      B -> let arg_f =    x in let arg_g = harg let arg_h =  farg in garg
      C -> let arg_f = garg in let arg_g = x    let arg_h =  farg in harg
=>
    let farg = f arg_f
    let garg = g arg_g
    let harg = h arg_h
    let arg_f = case s of
                  A -> garg
                  B -> x
                  C -> garg
    let arg_g = case s of
                  A -> harg
                  B -> harg
                  C -> x
    let arg_h = case s of
                  A -> x
                  B -> farg
                  C -> farg
    case s of
      A -> farg
      B -> garg
      C -> harg

    arg_f <- new
    arg_g <- new
    arg_h <- new
    farg <- f arg_f
    garg <- g arg_g
    harg <- h arg_h
    case s of
      A ->
        copy garg arg_f
        copy harg arg_g
        copy x    arg_h
        copy farg res
      ...


-----------------
     if b then f (g x)
          else g (f y)
=>
    let gtwiddly1 = g (if b then x else ftwiddly2)
        ftwiddly2 = f (if b then gtwiddly1 else y)
    in  if b then fwtiddly2 else gtwiddly1
----------
if b is true:

    let gtwiddly1 = g x
        ftwiddly2 = f gtwiddly1 = f (g x)
    in  f (g x)
----------
if b is false:

    let gtwiddly1 = g ftwiddly2 = g (f y)
        ftwiddly2 = f y
    in  g (f y)



-------------
     if b then f (g x)
          else g (f y)
=>
    let arg = if b then g x else y
    in  if b then f arg else g (f arg)
=>


-}
matchPoints :: Expr a -> AOSurgery (Global a,[Expr a]) (Expr a) (Expr a,Expr a)
matchPoints e0 =
  case e0 of
    hd :@: es ->
      orAOf (retAO (e0,bot)) $
        [ mapRes (\ (e',e_bot) -> (hd :@: (l ++ [e'] ++ r),e_bot))
                 (matchPoints e)
        | (l,e,r) <- cursor es
        ] ++
        (case hd of
          Gbl g -> [Surgery (Unit (g,es)) (\(UnitA e) -> (e,e))]
          _     -> [])

    Lcl{} -> retAO (e0,bot)

    Let x e1 e2 -> mapRes (\ (e1',e1_bot) -> (Let x e1' e2,e1_bot)) (matchPoints e1)
                   -- incomplete for now. can let lift+memoise to simplify

    Match e brs ->
      orAO
        [ mapRes (\ (e',e_bot) -> (Match e' brs,e_bot)) (matchPoints e)
        , mapRes (\ rhss -> let (brs',brs_bot) = unzip [ (Case lhs rhs,Case lhs rhs_bot)
                                                       | (Case lhs _,(rhs,rhs_bot)) <- brs `zip` rhss
                                                       ]
                            in  (Match e brs',Match e brs_bot))
                 (andAO [ orAO [matchPoints rhs,retAO (rhs,bot)]
                        | Case _ rhs <- brs
                        ])
        ]

    Lam{}   -> error "matchPoints: Lambda"
    Quant{} -> error "matchPoints: Quant"

cursor :: [a] -> [([a],a,[a])]
cursor xs = [ let (l,x:r) = splitAt i xs in (l,x,r) | i <- [0..length xs-1] ]


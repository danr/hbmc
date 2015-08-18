{-# LANGUAGE ScopedTypeVariables #-}
module HBMC.Merge where

-- import HBMC.Surgery
import Tip.Core
import Tip.Fresh
import Tip.Utils
import Tip.Scope

import Data.Generics.Geniplate

import Control.Applicative
import Data.Foldable (asum)
import Data.Traversable (sequenceA)
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

{-
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

--------
  nested case
--------

  case s of
    A -> f (g x)
    B -> case t of
            C -> g (f y)
            D -> f z

==>

  let f_val = f f_arg
  case s of
    A -> let f_arg = g x in f_val
    B -> case t of
            C -> let f_arg = y in g f_val
            D -> let f_arg = z in f_val

==>

  let f_val = f f_arg
  let g_val = g g_arg
  case s of
    A -> let f_arg = let g_arg = x in g_val in f_val
    B -> case t of
            C -> let f_arg = y in let g_arg = f_val in g_val
            D -> let f_arg = z in f_val

==> [let/let]

  let f_val = f f_arg
  let g_val = g g_arg
  case s of
    A -> let f_arg = g_val in let g_arg = x in f_val
    B -> case t of
            C -> let f_arg = y in let g_arg = f_val in g_val
            D -> let f_arg = z in f_val

==> [magic let pull ... what happens when other than magic lets are in the way?
                        they can be let lifted first (and memoised), of course!
                        then all lets that are left are magic]

  let f_val = f f_arg
  let g_val = g g_arg
  let f_arg = case s of
                A -> g_val
                B -> case t of
                    C -> y
                    D -> z
  let g_arg = case s of
                A -> x
                B -> case t of
                    C -> f_val
                    D -> undefined
  case s of
    A -> f_val
    B -> case t of
            C -> g_val
            D -> f_val

-------

  case s of
    A -> f x
    B -> case f y of
           C -> a
           D -> b

==>

  let f_val = f f_arg
  case s of
    A -> let f_arg = x in f_val
    B -> case let f_arg = y in f_val of
            C -> a
            D -> b

==> [magic let pull]

  let f_val = f f_arg
  let f_arg = case s of
                A -> x
                B -> y
  case s of
    A -> f_val
    B -> case f_val of
            C -> a
            D -> b

--------
  pulling too far
--------

     case s of
        A -> a
        B -> case t of
            C -> f x
            D -> f y


==>
     let f_val = f f_arg
     let f_arg = case s of
            A -> _|_
            B -> case t of
                C -> x
                D -> y
     case s of
        A -> a
        B -> case t of
            C -> f_val
            D -> f_val

==>
     f_val <- new
     f_arg <- new
     f f_arg >>> f_val
     when (s = A) noop
     when (s = B) $
       do when (t = C) (x >>> f_arg)
          when (t = D) (y >>> f_arg)
     when (s = A) (a >>> res)
     when (s = B) $
       do when (t = C) (f_val >>> res)
          when (t = D) (f_val >>> res)

==>
     f_val <- new
     f_arg <- new
     f f_arg >>> f_val
     when (s = A) $
       do noop
          a >>> res

     when (s = B) $
       do when (t = C) (x >>> f_arg)
          when (t = D) (y >>> f_arg)
          when (t = C) (f_val >>> res)
          when (t = D) (f_val >>> res)

i.e. np

-}

-- should make it so that constructors are not counted
calls :: forall a . Ord a => Expr a -> [Global a]
calls e =
  usort . concat $
    [ duplicates . concat $
        [ usortOn globalSig
            [ g
            | Gbl g :@: _ <- universeBi rhs :: [Expr a]
            , not (null (polytype_args (gbl_type g)))
            ]
        | Case _ rhs <- brs
        ]
    | Match _ brs <- universeBi e :: [Expr a]
    ]

isFunction :: Ord a => Scope a -> Global a -> Bool
isFunction scp g = case lookupGlobal (gbl_name g) scp of
                     Just FunctionInfo{} -> True
                     _                   -> False

hoistAll :: Name a => Scope a -> Expr a -> Fresh (Expr a)
hoistAll scp e = last <$> hoistAllTrace scp e

hoistAllTrace :: Name a => Scope a -> Expr a -> Fresh [Expr a]
hoistAllTrace scp e =
  case filter (isFunction scp) (calls e) of
    f:_ -> fmap (e:) (hoistAllTrace scp =<< hoist f e)
    _   -> return [e]

hoist :: Name a => Global a -> Expr a -> Fresh (Expr a)
hoist f (Let x ex e) = Let x ex <$> hoist f e
hoist f e0 =
  do let (arg_tys,res_ty) = gblType f
     f_val  <- (`Local` res_ty) <$> refreshNamed "val" (gbl_name f)
     f_args <- sequence [ (`Local` arg_ty) <$> refreshNamed "arg" (gbl_name f)
                        | arg_ty <- arg_tys ]
     let Just e = hoist' f f_val f_args e0
     return (Let f_val (Gbl f :@: map Lcl f_args) e)

hoist' :: (Functor f,Applicative f,Alternative f,Eq a) =>
          Global a -> Local a -> [Local a] -> Expr a -> f (Expr a)
hoist' f f_val f_args e0 =
  case e0 of
    hd :@: es ->
      asum
        [ fmap (\ e' -> hd :@: (l ++ [e'] ++ r)) (go e)
        | (l,e,r) <- cursor es
        ]
      <|>
        case hd of
          Gbl g | g `globalEq` f -> pure (lets (f_args `zip` es) (Lcl f_val))
          _ -> empty

    Lcl{} -> empty

    Let x e1 e2 ->
          fmap (\ e' -> Let x e' e2) (go e1)
      <|> fmap (\ e' -> Let x e1 e') (go e2)

    Match e brs ->
          fmap (\ e' -> Match e' brs) (go e)
      <|> fmap (Match e)
            (sequenceA
              [ fmap (Case pat) (go rhs <|> pure rhs)
              | Case pat rhs <- brs
              ])

    Lam{}   -> error "hoist' Lam"
    Quant{} -> error "hoist' Quant"
  where
  go = hoist' f f_val f_args

lets :: [(Local a,Expr a)] -> Expr a -> Expr a
lets []           e = e
lets ((x,ex):xes) e = Let x ex (lets xes e)

cursor :: [a] -> [([a],a,[a])]
cursor xs = [ let (l,x:r) = splitAt i xs in (l,x,r) | i <- [0..length xs-1] ]

globalSig :: Global a -> (a,[Type a])
globalSig g = (gbl_name g,gbl_args g)

globalEq :: Eq a => Global a -> Global a -> Bool
globalEq f g = globalSig f == globalSig g

duplicates :: Ord a => [a] -> [a]
duplicates xs = usort [ x | x <- xs, count x > 1 ]
  where count x = length (filter (== x) xs)


{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module HBMC.Merge where

-- import HBMC.Surgery
import Tip.Core
import Tip.Fresh
import Tip.Utils
import Tip.Scope hiding (locals)

import Data.Generics.Geniplate

import Data.Maybe

import Control.Applicative
import Data.Foldable (asum)
import Data.Traversable (sequenceA)

import HBMC.Identifiers

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

  let f_val = f f_argf
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

mergeTrace :: Scope Var -> Expr Var -> Fresh [Expr Var]
mergeTrace scp e =
  do trc <- hoistAllTrace scp e
     return (trc ++ letPasses (last trc))

merge :: Scope Var -> Expr Var -> Fresh (Expr Var)
merge scp e = last <$> mergeTrace scp e

letPasses :: Expr Var -> [Expr Var]
letPasses e0 = scanl (flip ($)) e0
  [commuteLet,pullLet,pushLets,simplifySameMatch,simplifyEqualLets]

-- step 1. introduce magic lets
--
--    case x of
--      A -> f y
--      B -> f z
--
-- => let valf = f argf
--    case x of
--      A -> let argf = y in valf
--      B -> let argf = z in valf

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

hoistAll :: Scope Var -> Expr Var -> Fresh (Expr Var)
hoistAll scp e = last <$> hoistAllTrace scp e

hoistAllTrace :: Scope Var -> Expr Var -> Fresh [Expr Var]
hoistAllTrace scp e =
  case filter (isFunction scp) (calls e) of
    f:_ -> fmap (e:) (hoistAllTrace scp =<< hoist f e)
    _   -> return [e]

hoist :: Global Var -> Expr Var -> Fresh (Expr Var)
hoist f (Let x ex e) = Let x ex <$> hoist f e
hoist f e0 =
  do let (arg_tys,res_ty) = gblType f
     f_val  <- (`Local` res_ty) <$> makeMagic "val" (gbl_name f)
     f_args <- sequence [ (`Local` arg_ty) <$> makeMagic "arg" (gbl_name f)
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
          Gbl g | g `globalEq` f -> pure (makeLets (f_args `zip` es) (Lcl f_val))
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

-- step 2. let/let and match/let

-- Only works on magic lets(!)
commuteLet :: (IsMagic a,TransformBi (Expr a) (f a)) => f a -> f a
commuteLet =
  transformExprIn $
    \ e0 -> case e0 of
      Let x (Let y ye xe) e  | isMagic y -> commuteLet (Let y ye (Let x xe e))
      Match (Let x xe e) brs | isMagic x -> commuteLet (Let x xe (Match e brs))
      hd :@: es
        | (l,Let x xe e,r):_ <- [ llr | llr@(l,Let x _ _,r) <- cursor es, isMagic x ]
        -> commuteLet (Let x xe (hd :@: (l ++ [e] ++ r)))
      _ -> e0

-- step 3. pull magic lets upwards
--
--    case x of
--      A -> let argf = y in valf
--      B -> let argf = z in valf
--      C -> c
-- => let argf = case x of
--                 A -> y
--                 B -> z
--                 -- C case removed
--    case x of
--      A -> valf
--      B -> valf
--      C -> c

pullLet :: Expr Var -> Expr Var
pullLet (Let x rhs b) = Let x rhs (pullLet b)
pullLet e =
  case filter isMagic (letBound e) of
    []  -> e
    x:_ -> let Just skel = letSkeleton x e
           in  Let x skel (pullLet (removeLet x e))

letBound :: Expr a -> [Local a]
letBound e = [ x | Let x _ _ <- universeBi e ]

letSkeleton :: Eq a => Local a -> Expr a -> Maybe (Expr a)
letSkeleton x = go
  where
  go (Match s brs) =
    case catMaybes [fmap (Case pat) (go rhs) | Case pat rhs <- brs] of
      []   -> Nothing
      brs' -> Just (Match s brs')
  go (Let y rhs b) | x == y    = Just rhs
                   | otherwise = go b
  go (_ :@: es)    = asum (map go es)
  go Lcl{}         = Nothing

removeLet :: Eq a => Local a -> Expr a -> Expr a
removeLet x =
  transformBi $ \ e0 -> case e0 of
    Let y _ e | x == y -> e
    _                  -> e0

-- step 4. push singleton lets

pushLets :: Ord a => Expr a -> Expr a
--    let x = case s of
--           A -> y
--    let y = ...
--    case s of
--      A -> a
--      B -> b
-- => let y = ...
--    case s of
--      A -> let x = y in a
--      B -> b
pushLets (Let x (Match s [Case p xrhs]) rest)
  | (bound,Match s' brs) <- collectLets rest
  , s' == s
  , Just (l,Case p' rhs,r) <- findCase p brs
  = pushLets (makeLets bound (Match s (l ++ [Case p' (Let x xrhs rhs)] ++ r)))

--    let x = e
--    let y = ... (no x)
--    case s of
--      A -> a (no x)
--      B -> b[x]
--      C -> c (no x)
-- => let y = ...
--    case s of
--      A -> a
--      B -> let x = e in b [x]
--      C -> c (no x)
pushLets (Let x xrhs rest)
  | notMatch xrhs
  , (bound,Match s brs) <- collectLets rest
  , null (filter (\ (_y,rhs) -> x `elem` locals rhs) bound)
  , [Case p rhs] <- [ br | br <- brs, x `elem` locals (case_rhs br) ]
  , Just (l,Case p' rhs,r) <- findCase p brs
  = pushLets (makeLets bound (Match s (l ++ [Case p' (Let x xrhs rhs)] ++ r)))

pushLets (Let x xe rest) = Let x xe (pushLets rest)
pushLets (Match s brs)   = Match s [ Case p (pushLets rhs) | Case p rhs <- brs ]
pushLets e = e

notMatch :: Expr a -> Bool
notMatch Match{} = False
notMatch _       = True

findCase :: Eq a => Pattern a -> [Case a] -> Maybe ([Case a],Case a,[Case a])
findCase p (br@(Case Default rhs):brs) =
      fmap (\ (l,b,r) -> (br:l,b,r)) (findCase p brs)
  <|> Just ([],br,brs)
findCase p brs = listToMaybe [ (l,br,r) | (l,br@(Case p' _),r) <- cursor brs, p == p' ]

-- step 5. simplify match where all rhs are same

simplifySameMatch :: Eq a => Expr a -> Expr a
simplifySameMatch =
  transformExprIn $ \ e0 ->
    case e0 of
      Match e (Case _ rhs:brs)
        | all ((== rhs) . case_rhs) brs
        -> case rhs of
             Lcl y -> Lcl y
             _     -> Match e [Case Default rhs]
                   -- NB: Could be proj, so we must retain what we cased
                   -- on to get here. The simple case above cannot be proj
      _ -> e0

-- step 6. simplify equal, simple, lets, globally

simplifyEqualLets :: (IsMagic a,Ord a) => Expr a -> Expr a
simplifyEqualLets e =
  case [ (x,s) | Let x s _ <- universeBi e
               , isMagic x
               , simple s
               , 1 == sum [ 1 | Lcl y <- universeBi e, x == y ]
               , 0 == sum [ 1 | Match (Lcl y) _ <- universeBi e, x == y ]
               ]
    ++ [ (x,Lcl y) | Let x (Lcl y) _ <- universeBi e ]
    of
    (x,s):_ -> simplifyEqualLets (unsafeSubst s x (removeLet x e))
    _       -> e
  where
  simple Lcl{}       = True
  simple (hd :@: es) = all simple es
  simple _           = False

-- utils

globalSig :: Global a -> (a,[Type a])
globalSig g = (gbl_name g,gbl_args g)

globalEq :: Eq a => Global a -> Global a -> Bool
globalEq f g = globalSig f == globalSig g


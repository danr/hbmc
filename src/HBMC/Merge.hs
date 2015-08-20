{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
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
import HBMC.Projections

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

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

  let f_res = f f_arg
  case s of
    A -> let f_arg = g x in f_res
    B -> case t of
            C -> let f_arg = y in g f_res
            D -> let f_arg = z in f_res

==>

  let f_res = f f_arg
  let g_res = g g_arg
  case s of
    A -> let f_arg = let g_arg = x in g_res in f_res
    B -> case t of
            C -> let f_arg = y in let g_arg = f_res in g_res
            D -> let f_arg = z in f_res

==> [let/let]

  let f_res = f f_argf
  let g_res = g g_arg
  case s of
    A -> let f_arg = g_res in let g_arg = x in f_res
    B -> case t of
            C -> let f_arg = y in let g_arg = f_res in g_res
            D -> let f_arg = z in f_res

==> [magic let pull ... what happens when other than magic lets are in the way?
                        they can be let lifted first (and memoised), of course!
                        then all lets that are left are magic]

  let f_res = f f_arg
  let g_res = g g_arg
  let f_arg = case s of
                A -> g_res
                B -> case t of
                    C -> y
                    D -> z
  let g_arg = case s of
                A -> x
                B -> case t of
                    C -> f_res
                    D -> undefined
  case s of
    A -> f_res
    B -> case t of
            C -> g_res
            D -> f_res

-------

  case s of
    A -> f x
    B -> case f y of
           C -> a
           D -> b

==>

  let f_res = f f_arg
  case s of
    A -> let f_arg = x in f_res
    B -> case let f_arg = y in f_res of
            C -> a
            D -> b

==> [magic let pull]

  let f_res = f f_arg
  let f_arg = case s of
                A -> x
                B -> y
  case s of
    A -> f_res
    B -> case f_res of
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
     let f_res = f f_arg
     let f_arg = case s of
            A -> _|_
            B -> case t of
                C -> x
                D -> y
     case s of
        A -> a
        B -> case t of
            C -> f_res
            D -> f_res

==>
     f_res <- new
     f_arg <- new
     f f_arg >>> f_res
     when (s = A) noop
     when (s = B) $
       do when (t = C) (x >>> f_arg)
          when (t = D) (y >>> f_arg)
     when (s = A) (a >>> res)
     when (s = B) $
       do when (t = C) (f_res >>> res)
          when (t = D) (f_res >>> res)

==>
     f_res <- new
     f_arg <- new
     f f_arg >>> f_res
     when (s = A) $
       do noop
          a >>> res

     when (s = B) $
       do when (t = C) (x >>> f_arg)
          when (t = D) (y >>> f_arg)
          when (t = C) (f_res >>> res)
          when (t = D) (f_res >>> res)

i.e. np

-}

mergeTrace :: Scope Var -> Expr Var -> Fresh [Expr Var]
mergeTrace scp e0 =
  do e <- magicLets e0
     trc <- hoistAllTrace scp e
     return (nub (e0 : trc ++ letPasses (last trc)))

merge :: Scope Var -> Expr Var -> Fresh (Expr Var)
merge scp e = last <$> mergeTrace scp e

letPasses :: Expr Var -> [Expr Var]
letPasses e0 = scanl (flip ($)) e0
  [fixpoint (commuteLet . pullLet NothingReplacement)
  ,fixpoint (pushLets [])
  ,mergeMatches,simplifySameMatch,simplifyEqualLets]

-- step 1. introduce magic lets
--
--    case x of
--      A -> f y
--      B -> f z
--
-- => let resf = f argf
--    case x of
--      A -> let argf = y in resf
--      B -> let argf = z in resf

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
    f:_ -> do (lhs,rhs,e') <- hoist f e
              rest <- hoistAllTrace scp e'
              return (map (Let lhs rhs) (e':rest))
              -- fmap (e:) (hoistAllTrace scp =<< hoist f e)
    _   -> return [e]

hoist :: Global Var -> Expr Var -> Fresh (Local Var,Expr Var,Expr Var)
hoist f e | trace ("hoist:" ++ ppRender (f,e)) False = undefined
-- hoist f (Let x ex e) = Let x ex <$> hoist f e
hoist f e0 =
  do let (arg_tys,res_ty) = gblType f
     f_res  <- (`Local` res_ty) <$> makeMagic "res" (gbl_name f)
     f_args <- sequence [ (`Local` maybeTy arg_ty) <$> makeMagic "arg" (gbl_name f)
                        | arg_ty <- arg_tys ]
     let Just e = hoist' f f_res f_args e0
     return
       ( f_res
       , foldr
              (\ x e' ->
                Match (Lcl x)
                  [ Case (ConPat (nothingGbl (lcl_type x)) []) (noopExpr (lcl_type x))
                  , Case (ConPat (justGbl (lcl_type x)) []) e'
                  ])
              (Gbl f :@: [ projExpr 0 (Lcl arg) (unMaybeTy (lcl_type arg)) | arg <- f_args ])
              f_args
       , e)

hoist' :: (Functor f,Applicative f,Alternative f) =>
          Global Var -> Local Var -> [Local Var] -> Expr Var -> f (Expr Var)
hoist' f f_res f_args e0 =
  case e0 of
    hd :@: es ->
      asum
        [ fmap (\ e' -> hd :@: (l ++ [e'] ++ r)) (go e)
        | (l,e,r) <- cursor es
        ]
      <|>
        case hd of
          Gbl g | g `globalEq` f -> pure (makeLets (f_args `zip` map justExpr es) (Lcl f_res))
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
  go = hoist' f f_res f_args

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

-- step 0. make lets magic and pull them upwards
--
--    case u of
--       C a -> let b = h a in f (g b) b
--       D a -> g a
-- => let *b = case u of
--               C a -> h a
--               D a -> noop
--    case u of
--      C a -> f (g b) b
--      D a -> g a

introMagicLets :: Expr Var -> Fresh (Expr Var)
introMagicLets =
  transformExprInM $
    \ e0 -> case e0 of
      Let x xe b -> do i <- fresh
                       x' <- makeMagic (show (i :: Int)) (lcl_name x)
                       let lx' = Local x' (lcl_type x)
                       Let lx' xe <$> (Lcl lx' // x) b
      _ -> return e0

magicLets :: Expr Var -> Fresh (Expr Var)
magicLets
  = fmap ((\ u -> trace ("magicLets:" ++ ppRender u) u) .
          mergeMatches . pullLet NoopReplacement) . introMagicLets

mergeMatches :: Expr Var -> Expr Var
mergeMatches e0 | trace ("mM:" ++ ppRender e0) False = undefined
mergeMatches e0 =
  case e0 of
    Let{} | let (bound,e) = collectLets e0 ->
      case catMaybes
             [ fmap ((,) ((l1++mid++r2),(x,y))) (tryMerge u v)
             | (l1,(x,u),r) <- cursor bound
             , (mid,(y,v),r2) <- cursor r
             ] of
      ((bound',(x,y)),m):_ ->
         let e' = unsafeSubst (Lcl x) y (makeLets bound' e)
         in  mergeMatches (Let x m e')
      _ -> makeLets bound (mergeMatches e)
    Match s brs -> Match s [ Case p (mergeMatches rhs) | Case p rhs <- brs ]
    _ -> e0

tryMerge :: Expr Var -> Expr Var -> Maybe (Expr Var)
tryMerge e1 e2 | trace ("tM:" ++ ppRender (e1,e2)) False = undefined
tryMerge e1 e2 | e1 == e2 = Just e1
tryMerge (Match s1 brs1) (Match s2 brs2)
  | s1 == s2 = fmap (Match s1) (mergeBranches (sort brs1) (sort brs2))
tryMerge _ _ = Nothing

mergeBranches :: [Case Var] -> [Case Var] -> Maybe [Case Var]
mergeBranches (Case _ e1:_) (Case _ e2:_) | trace ("mB:" ++ ppRender (e1,e2)) False = undefined
mergeBranches (br1@(Case p1 rhs1):brs1) (br2@(Case p2 rhs2):brs2)
  | p1 == p2
  = (:)
      <$> (if isEmpty rhs1      then Just br2
           else if isEmpty rhs2 then Just br1
           else fmap (Case p1) (tryMerge rhs1 rhs2))
      <*> mergeBranches brs1 brs2
mergeBranches [] [] = Just []
mergeBranches _  _  = Nothing


-- step 3. pull magic lets upwards
--
--    case x of
--      A -> let argf = Just y in resf
--      B -> let argf = Just z in resf
--      C -> c
-- => let argf = case x of
--                 A -> Just y
--                 B -> Just z
--                 C -> Nothing
--    case x of
--      A -> resf
--      B -> resf
--      C -> c

data Replacement = NothingReplacement | NoopReplacement

replacementExpr :: Replacement -> Type Var -> Expr Var
replacementExpr NothingReplacement = nothingExpr
replacementExpr NoopReplacement    = noopExpr

pullLet :: Replacement -> Expr Var -> Expr Var
pullLet repl (Let x rhs b)
  | isMagic x = Let x (pullLet repl rhs) (pullLet repl b)
  | otherwise = Let x rhs (pullLet repl b)
pullLet repl e =
  case filter isMagic (letBound e) of
    []  -> e
    x:_ -> let Just skel = letSkeleton repl x e
           in  Let x skel (pullLet repl (removeLet x e))

letBound :: Expr a -> [Local a]
letBound e = [ x | Let x _ _ <- universeBi e ]

letSkeleton :: Replacement -> Local Var -> Expr Var -> Maybe (Expr Var)
letSkeleton repl x = go
  where
  go e0@(Match s brs) =
    let e = Match s
               [ case go rhs of
                   Just rhs' -> Case pat rhs'
                   Nothing   -> Case pat (replacementExpr repl (exprType rhs))
               | Case pat rhs <- brs
               ]
    in  Just (if isEmpty e then replacementExpr repl (exprType e0) else e)
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

inRhss :: Local Var -> [(a,Expr Var)] -> Bool
inRhss x = not . null . filter (\ (_,rhs) -> x `elem` locals rhs)

fixpoint :: (Pretty a,Eq a) => (a -> a) -> a -> a
fixpoint f x | trace ("fixpoint: " ++ ppRender (x,y)) False = undefined
             | y == x    = x
             | otherwise = fixpoint f y
  where y = f x

pushLets :: [Local Var] -> Expr Var -> Expr Var
--    ... no x ...
--    let x = case s of
--           A -> xrhs
--           B -> Nothing / noop
--    let y = ... (no x) ...
--    case s (no x) of
--      A -> a
--      B -> b
-- => let y = ...
--    case s of
--      A -> let x = xrhs in a
--      B -> b
pushLets seen (Let x (Match s (filter (not . isEmptyCase) -> [Case p xrhs])) rest)
  | isMagic x
  , (bound,Match s' brs) <- collectLets rest
  , not (inRhss x bound)
  , x `notElem` seen
  , x `notElem` locals s
  , s' == s
  , Just (l,Case p' rhs,r) <- findCase p brs
  = pushLets seen (makeLets bound (Match s (l ++ [Case p' (Let x xrhs rhs)] ++ r)))

--    let x = e
--    let y = ... (no x)
--    case s (no x) of
--      A -> a (no x)
--      B -> b[x]
--      C -> c (no x)
-- => let y = ...
--    case s of
--      A -> a
--      B -> let x = e in b [x]
--      C -> c (no x)
pushLets seen (Let x xrhs rest)
  | isMagic x
  , (bound,Match s brs) <- collectLets rest
  , not (inRhss x bound)
  , x `notElem` seen
  , x `notElem` locals s
  , [Case p rhs] <- [ br | br <- brs, x `elem` locals (case_rhs br) ]
  , Just (l,Case p' rhs,r) <- findCase p brs
  = pushLets seen (makeLets bound (Match s (l ++ [Case p' (Let x xrhs rhs)] ++ r)))

pushLets seen (Let x xe rest) = Let x xe (pushLets (seen ++ locals xe) rest)
pushLets _    (Match s brs)   = Match s [ Case p (pushLets [] rhs) | Case p rhs <- brs ]
pushLets _    e = e

isEmptyCase :: Case Var -> Bool
isEmptyCase (Case _ rhs) = isEmpty rhs

isEmpty :: Expr Var -> Bool
isEmpty (Match _ rhss) = all (isEmpty . case_rhs) rhss
isEmpty (Gbl n :@: []) = gbl_name n `elem` [nothingVar,noopVar]
isEmpty _              = False


notMatch :: Expr a -> Bool
notMatch Match{} = False
notMatch _       = True

findCase :: Eq a => Pattern a -> [Case a] -> Maybe ([Case a],Case a,[Case a])
findCase p (br@(Case Default rhs):brs) =
      fmap (\ (l,b,r) -> (br:l,b,r)) (findCase p brs)
  <|> Just ([],br,brs)
findCase p brs = listToMaybe [ (l,br,r) | (l,br@(Case p' _),r) <- cursor brs, p == p' ]

-- step 5. simplify match where all rhs are same
--         ... cannot do this because of projections ...

simplifySameMatch :: Eq a => Expr a -> Expr a
simplifySameMatch =
  transformExprIn $ \ e0 ->
    case e0 of
      {- must check that rhs contains no projections of the matched thing
      Match e (Case _ rhs:brs)
        | all ((== rhs) . case_rhs) brs
        -> rhs
      -}
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


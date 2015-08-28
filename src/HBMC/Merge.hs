{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module HBMC.Merge where

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
import HBMC.ToSimple

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

mergeTrace :: Scope Var -> Expr Var -> Fresh [Expr Var]
mergeTrace scp e = sequence $ scanl (>>=) (return e)
-- step 1. to simple
    [ toExpr
-- step 2. move all lets with a case trail to the top level
    , return . pullLets
-- step 3. merge all that call a common function
    , mergeCommon scp
-- step 4. move lets down as far as possible
    , return . pushLets
-- step 5. call the merged functions
    , callMerged
-- step 6. an optimisation: simplify match that return the same value
    , return . simplifySameMatch
-- step 7. return simple again
    , toExpr
    ]

--    case s of
--      A -> let x = e in a
--      B -> b
-- => let x = case s of A -> e
--                      B -> noop
--    in case s of A -> a
--                 B -> b
pullLets :: Expr Var -> Expr Var
pullLets e =
  case letBound e of
    []  -> e
    x:_ ->
      case letSkeleton x e of
        Just skel -> widenLetScope (Let x (pullLets skel) (pullLets (removeLet x e)))
        _         -> error $ "pullLets: " ++ ppRender (x,e)

letBound :: Expr a -> [Local a]
letBound e = [ x | Let x _ _ <- universeBi e ]

letSkeleton :: Local Var -> Expr Var -> Maybe (Expr Var)
letSkeleton x = go
  where
  go e0@(Match s brs) =
    Just $ mkMatch s
       [ case go rhs of
           Just rhs' -> Case pat rhs'
           Nothing   -> Case pat (noopExpr (exprType e0))
       | Case pat rhs <- brs
       ]
  go (Let y rhs b) | x == y    = Just rhs
                   | otherwise = go b
  go (_ :@: es)    = asum (map go es)
  go Lcl{}         = Nothing

removeLet :: Eq a => Local a -> Expr a -> Expr a
removeLet x =
  transformBi $ \ e0 -> case e0 of
    Let y _ e | x == y -> e
    _                  -> e0

mkMatch :: Expr Var -> [Case Var] -> Expr Var
mkMatch s brs
  | isNoop e = noopExpr (exprType e)
  | otherwise = e
  where
  e = Match s brs

-- The invariant is that all lets are now at the top level in one big soup
mergeCommon :: Scope Var -> Expr Var -> Fresh (Expr Var)
mergeCommon scp = go
  where
  go e0 =
    let (bound,e) = collectLets e0 in

    case catMaybes
           [ fmap ((,) (l1++mid++r2,(x,y))) (tryMerge u v)
           | (l1,(x,u),r) <- cursor bound
           , (Gbl g :@: _):_ <- [rhss u]
           , isFunction scp g
           , (mid,(y,v),r2) <- cursor r
           , allSameHeads (rhss u ++ rhss v)
           ] of

      ((bound',(x,y)),m):_ ->
         do e' <- (Lcl x // y) (makeLets bound' e)
            go (Let x m e')

      _ -> return e0

isFunction :: Ord a => Scope a -> Global a -> Bool
isFunction scp g = case lookupGlobal (gbl_name g) scp of
                     Just FunctionInfo{} -> True
                     _                   -> False

sameHeads :: Expr Var -> Expr Var -> Bool
sameHeads (hd1 :@: _) (hd2 :@: _) = hd1 == hd2
sameHeads _           _           = False

allSameHeads :: [Expr Var] -> Bool
allSameHeads []     = True
allSameHeads (e:es) = all (sameHeads e) es

rhss :: Expr Var -> [Expr Var]
rhss (Match _ brs) = concatMap (rhss . case_rhs) brs
rhss e             = [ e | not (isNoop e) ]

tryMerge :: Expr Var -> Expr Var -> Maybe (Expr Var)
-- tryMerge e1 e2 | trace ("tM:" ++ ppRender (e1,e2)) False = undefined
tryMerge e1 e2 | e1 == e2 = Just e1
tryMerge (Match s1 brs1) (Match s2 brs2)
  | s1 == s2 = fmap (Match s1) (mergeBranches (sort brs1) (sort brs2))
tryMerge _ _ = Nothing

-- TODO: Handle default cases
mergeBranches :: [Case Var] -> [Case Var] -> Maybe [Case Var]
-- mergeBranches (Case _ e1:_) (Case _ e2:_) | trace ("mB:" ++ ppRender (e1,e2)) False = undefined
mergeBranches (br1@(Case p1 rhs1):brs1) (br2@(Case p2 rhs2):brs2)
  | p1 == p2
  = (:)
      <$> (if isNoop rhs1      then Just br2
           else if isNoop rhs2 then Just br1
           else fmap (Case p1) (tryMerge rhs1 rhs2))
      <*> mergeBranches brs1 brs2
mergeBranches [] [] = Just []
mergeBranches _  _  = Nothing



-- Push lets!!

pushLets :: Expr Var -> Expr Var
pushLets e@Let{} =
  let (lets,rest) = collectLets e
      cands       = leaves lets
  in  case catMaybes [ fmap ((,) c) (tryPush c rest) | c <- cands ] of
        (c,rest'):_ ->
          let remain (x,_) = x `notElem` map fst c
          in  pushLets (makeLets (filter remain lets) rest')
        _ -> makeLets lets (pushLets rest)
pushLets (Match s brs) = Match s [ Case p (pushLets rhs) | Case p rhs <- brs ]
pushLets e = e

tryPush :: Lets Var -> Expr Var -> Maybe (Expr Var)
tryPush lets (Match s brs)
  | and [ x `notElem` locals s | (x,_) <- lets ]
  , Just dirs <- sequence [ fmap ((,) x) (direction e) | (x,e) <- lets ]
  , (_,(s0,Case p _)):ds <- dirs
  , s0 == s
  , and [ s' == s && p' == p | (_,(s',Case p' _)) <- ds ]
  , Just (l,Case p' rhs,r) <- findCase p brs
  , let rhs' = Case p (makeLets [ (x,e) | (x,(_,Case _ e)) <- dirs ] rhs)
  = Just (Match s (l ++ [rhs'] ++ r))
tryPush _ _ = Nothing

direction :: Expr Var -> Maybe (Expr Var,Case Var)
direction (Match s brs)
  | [c] <- [ br | br@(Case _ rhs) <- brs, not (isNoop rhs) ]
  = Just (s,c)
direction _ = Nothing

leaves :: forall a . Ord a => Lets a -> [Lets a]
leaves lets =
  [ map fst scc
  | (scc,prevs) <- withPrevious sccs
  , and [ x `notElem` prev | ((x,e),_) <- scc, (_,prev) <- concat prevs ]
  ]
  where
  sccs = reverse (orderLets lets)

findCase :: Eq a => Pattern a -> [Case a] -> Maybe ([Case a],Case a,[Case a])
findCase p (br@(Case Default rhs):brs) =
      fmap (\ (l,b,r) -> (br:l,b,r)) (findCase p brs)
  <|> Just ([],br,brs)
findCase p brs = listToMaybe [ (l,br,r) | (l,br@(Case p' _),r) <- cursor brs, p == p' ]


-- if we have a case with >= 2 branches, and they all call the same function:
--
--    let x = case s of A -> f a
--                      B -> case t of
--                             C -> noop
--                             D -> f d
--
-- => let arg = case s of A -> Just a
--                        B -> case t of
--                               C -> Nothing
--                               D -> Just d
--    let x = case arg of Just x  -> f (sel x)
--                        Nothing -> noop
--
-- When all cases are present, no Maybe is introduced:
--
--    let x = case s of A -> f a
--                      B -> f b
--
-- => let arg = case s of A -> a
--                        B -> b
--    let x = f arg

callMerged :: Expr Var -> Fresh (Expr Var)
callMerged = transformExprInM top
  where
  top (Let lhs m rest)
    | rs@((Gbl f :@: as):_) <- rhss m
    , length rs >= 2
    , allSameHeads rs
    = do let need_maybe = any isNoop (universeBi m)

             (maybe_ty,proj_expr)
                | need_maybe = ( maybeTy
                               , \ x -> projExpr 0 (Lcl x)
                                                 (unMaybeTy (lcl_type x)))
                | otherwise  = (id     ,Lcl)

         args <- sequence [ do arg <- refreshNamed "arg" (lcl_name lhs)
                               return (Local arg (maybe_ty (exprType a))
                                      ,callSkeleton (exprType a) need_maybe i m)
                          | (i,a) <- [0..] `zip` as
                          ]

         let call = Gbl f :@: [ proj_expr x | (x,_) <- args ]

         let case_match x e =
               Match (Lcl x)
                 [ Case (ConPat (nothingGbl (unMaybeTy (lcl_type x))) [])
                        (noopExpr (exprType e))
                 , Case (ConPat (justGbl (unMaybeTy (lcl_type x))) []) e
                 ]

         let cases
               | need_maybe = foldr (\ (x,_) e -> case_match x e) call args
               | otherwise  = call

         return (makeLets (args ++ [(lhs,cases)]) rest)

  top e0 = return e0

callSkeleton :: Type Var -> Bool -> Int -> Expr Var -> Expr Var
callSkeleton ty need_maybe i = go
  where
  go (Match s brs) = mkMatch s [ Case pat (go rhs) | Case pat rhs <- brs ]
  go e          | isNoop e                = nothing_expr ty
  go (_ :@: es) | i >= 0 && i < length es = just_expr (es !! i)
  go e = error $ "callSkeleton: " ++ ppRender (i,e)

  (nothing_expr,just_expr)
    | need_maybe = (nothingExpr,justExpr)
    | otherwise  = (error "callSkeleton: did need Nothing!",id)


-- simplify match where all rhs are same
-- cannot do this when there are projections:
-- must check that rhs contains no projections of the matched thing
simplifySameMatch :: Ord a => Expr a -> Expr a
simplifySameMatch =
  transformExprIn $ \ e0 ->
    case e0 of
      Match s all_brs@(Case _ rhs:brs)
        | all ((== rhs) . case_rhs) brs
        , and [ x `notElem` locals s
              | Case _ e <- all_brs
              , x <- locals e
              ]
        -> rhs

      _ -> e0

-- utils

globalSig :: Global a -> (a,[Type a])
globalSig g = (gbl_name g,gbl_args g)

globalEq :: Eq a => Global a -> Global a -> Bool
globalEq f g = globalSig f == globalSig g

fixpoint :: (Pretty a,Eq a) => (a -> a) -> a -> a
fixpoint f x
  -- | trace ("fixpoint: " ++ ppRender (x,y)) False = undefined
  | y == x    = x
  | otherwise = fixpoint f y
  where y = f x


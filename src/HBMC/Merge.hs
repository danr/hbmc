{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module HBMC.Merge where

import Tip.Core
import Tip.Fresh
import Tip.Utils
import Tip.Scope hiding (locals,globals)

import Data.Generics.Geniplate

import Data.Maybe

import Control.Applicative
import Data.Foldable (asum)
import Data.Traversable (sequenceA)

import HBMC.Identifiers
import HBMC.Projections

import Data.List
import Data.List.Ordered( sortOn )

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

merge :: Scope Var -> Expr Var -> Fresh (Expr Var)
merge scp e0 =
  -- traceShow ("merge",pp e0) $
  case e0 of
    Let y b e  -> Let y b <$> merge scp e
    Match e brs ->
      let cands =
            [ usort (universeBi rhs) :: [Global Var]
            | Case _ rhs <- brs
            ]

      in  case [ f
               | f <- usort (concat cands)
               , isFunction scp f
               , sum [ 1 | fs <- cands,  f `elem` fs ] >= 2 ] of
            [] -> Match <$> merge scp e
                        <*> sequence
                              [ Case pat <$> merge scp rhs | Case pat rhs <- brs ]

            f:_ ->
              do fname' <- refresh (gbl_name f)
                 let f' = f { gbl_name = fname' }
                     S xs      = shrink $ surgery (gbl_name f) (Match e brs)
                     n:_       = map (length . fst) (sortOn (negate . length . fst) xs)
                     xs'       = filter ((n ==) . length . fst) xs
                     (ess,k):_ = sortOn (negate . similarity . fst) xs'
                     same = [ if all (e ==) es then Just e else Nothing
                            | e:es <- transpose ess
                            ]
                     m = k [ Gbl f' :@: [ e | (e,Nothing) <- es `zip` same ] | es <- ess ]
                 (mvs,as) <-
                   unzip <$> sequence
                     [ case me of
                         Nothing -> do x <- fresh
                                       let lx = Local x dummyType
                                       return (Just lx,Lcl lx)
                         Just e  -> do return (Nothing,e)
                     | me <- same
                     ]
                 let vs = catMaybes mvs
                 Let (Local fname' dummyType)
                     (Lam vs (Gbl f :@: as))
                     <$> merge scp m
    _ -> return e0

similarity :: (Pretty a,Eq a) => [[a]] -> Int
similarity ess =
  let res =
        sum
          [ sum [ 1 | e' <- l ++ r, e == e' ]
          | es <- transpose ess
          , (l,e,r) <- cursor es
          ]
  in  -- traceShow (pp ess,res)
      res

newtype Surg a b c = S [([a],[b] -> c)]

instance Functor (Surg a b) where
  fmap f (S xs) = S [ (as,\ bs -> f (k bs)) | (as,k) <- xs ]

instance Applicative (Surg a b) where
  pure x = S [([],\ [] -> x)]
  S fs <*> S xs = s [ (as ++ bs
                      ,\ us -> let (vs,ws) = splitAt (length as) us
                               in  k vs (j ws)
                      )
                    | (as,k) <- fs
                    , (bs,j) <- xs
                    ]

instance Alternative (Surg a b) where
  empty = S []
  S xs <|> S ys = s (xs ++ ys)

s :: [([a],[b] -> c)] -> Surg a b c
s = mini . S

mini :: Surg a b c -> Surg a b c
mini (S xs) =
  let (sings,others) = partition (null . fst) xs
  in  S (take 1 sings ++ others)

shrink :: Ord a => Surg a b c -> Surg a b c
shrink (S xs) = S (usortOn fst xs)

hole :: a -> Surg a b b
hole a = S [([a],\ [b] -> b)]

isFunction :: Ord a => Scope a -> Global a -> Bool
isFunction scp g = case lookupGlobal (gbl_name g) scp of
                     Just FunctionInfo{} -> True
                     _                   -> False

surgery :: (Show a,PrettyVar a,Ord a) => a -> Expr a -> Surg [Expr a] (Expr a) (Expr a)
surgery f e0 =
  let res@(S xs) =
        case e0 of
          Lcl{} -> pure e0
          Lam{} -> pure e0
          Match e brs ->
                (`Match` brs) <$> surgery f e
            <|> Match e <$>
                   sequenceA [ Case pat <$> surgery f rhs | Case pat rhs <- brs ]
          Let x b e ->
                (\ b' -> Let x b' e) <$> surgery f b
            <|> (\ e' -> Let x b e') <$> surgery f e
          hd :@: es ->
            shrink $
                aguard (case hd of Gbl g -> f == gbl_name g; _ -> False) (hole es)
            <|> asum
                  [ (\ e' -> hd :@: (l ++ [e'] ++ r)) <$> surgery f e
                  | (l,e,r) <- cursor es
                  ]
            <|> pure e0
  in   -- traceShow (pp e0,pp (map fst xs))
       res

aguard :: Alternative f => Bool -> f a -> f a
aguard True  m = m
aguard False _ = empty


{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module TipTarget (module TipTarget, module Tip.Haskell.Repr) where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import TipLift (Call)

import Tip.Haskell.Repr

-- Equal
-- EqualData equalData
-- ConstructiveData constrs
-- Thunk
-- Data
-- Maybe Nothing Just
-- Value
-- Type
-- dflt
-- get
-- getData

class (Show a,TipLift.Call a) => Interface a where
  prelude   :: String -> a
  api       :: String -> a

  proj      :: a -> Int -> a
  unproj    :: a -> Maybe (a,Int)
  mproj     :: a -> Int -> a

  mainFun   :: a

  conLabel  :: a -> a -- the translation of constructors
  conRepr   :: a -> a -- concrete datatype representation
  thunkRepr :: a -> a
  wrapData  :: a -> a
  caseData  :: a -> a -- caseNat
  mkCon     :: a -> a -- the pure constructors

  isCon     :: a -> Bool -- is this a constructor?

tagShow :: Interface a => [a] -> Expr a
tagShow []     = var   (api "TagNil")
tagShow (x:xs) = Apply (api "TagCons") [String x,var x,tagShow xs]

returnExpr :: Interface a => Expr a -> Expr a
returnExpr e = Apply (prelude "return") [e]


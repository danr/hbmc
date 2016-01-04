{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
module HBMC.Identifiers where

import Tip.Core
import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Fresh
-- import Tip.Haskell.Translate -- Why is HsId exported from here?!
import Tip.Utils.Rename
import Tip.Utils
import Tip.Pass.Booleans

import Data.Maybe

import Data.Generics.Geniplate

import Data.Set (Set)
import qualified Data.Set as S

import qualified HBMC.Object as O

boolNames :: BoolNames Var
boolNames = BoolNames
  { boolName    = System "Bool" Nothing
  , trueName    = SystemCon "True" Nothing
  , falseName   = SystemCon "False" Nothing
  , isTrueName  = System "isTrue" Nothing
  , isFalseName = System "isFalse" Nothing
  }

dummyType :: Type Var
dummyType = TyCon (System "Dummy" Nothing) []

instance O.Names Var where
  unkName   = System "?" Nothing
  unitName  = System "()" Nothing
  boolName  = System "BL" Nothing
  falseName = SystemCon "FF" Nothing
  trueName  = SystemCon "TT" Nothing
  copyName  = System ">>>" Nothing
  equalHereName    = System "equalHere" Nothing
  notEqualHereName = System "notEqualHere" Nothing

data Var
  = X
  | Var String
  | Con String
  | System    String (Maybe (Type Var))
  | SystemCon String (Maybe (Type Var))
  | Proj (Type Var) Int
  | Int :~ Var
 deriving (Show,Eq,Ord)

isCon :: Var -> Bool
isCon Con{}       = True
isCon SystemCon{} = True
isCon (_ :~ x)    = isCon x
isCon _           = False

proj :: Type Var -> Int -> Var
proj = Proj

unproj :: Var -> Maybe (Type Var,Int)
unproj (Proj t i) = Just (t,i)
unproj _          = Nothing

varMax :: Var -> Int
varMax (i :~ v) = varMax v `max` i
varMax _        = 0

varStr' :: Var -> String
varStr' x =
  case x of
    X             -> "x"
    Var ""        -> "x"
    Var x         -> x
    Con x         -> varStr' (Var x)
    i :~ v        -> varStr' v
    Proj _ i      -> "proj" {- <> pp x <> "_" -} ++ show (i+1)
    System    x m -> x ++ maybe "" ppRender m
    SystemCon x m -> x ++ maybe "" ppRender m

instance PrettyVar Var where
  varStr x =
    case x of
      i :~ v -> varStr' v -- ++ "_" ++ show i
      _      -> varStr' x

renameTheory :: forall a . (Ord a,PrettyVar a) => Theory a -> Theory Var
renameTheory thy = renameWith disambigId thy
 where
  cons = S.fromList [ c | Constructor c _ _ <- universeBi thy ]

  disambigId :: a -> [Var]
  disambigId i = vs : [ x :~ vs | x <- [0..] ]
    where
      var_or_con
        | i `S.member` cons = Con
        | otherwise         = Var

      vs = case varStr i of
             [] -> var_or_con "x"
             xs -> var_or_con xs

instance Name Var where
  fresh            = refresh X
  freshNamed x     = refresh (Var x)
  refreshNamed x s = freshNamed (varStr' s ++ x)
  refresh (_ :~ v) = refresh v
  refresh v        = (:~ v) `fmap` fresh
  getUnique        = varMax

laterGbl :: Global Var
laterGbl = blankGlobal (System "later" Nothing) dummyType

laterExpr :: Expr Var -> Expr Var
laterExpr e = Gbl laterGbl :@: [e]

blankGlobal :: Var -> Type Var -> Global Var
blankGlobal g t = Global g (PolyType [] [] t) []


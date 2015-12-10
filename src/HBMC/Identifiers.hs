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

instance O.Names Var where
  unkName   = System "?" Nothing
  unitName  = System "()" Nothing
  boolName  = System "Bool" Nothing
  falseName = System "False" Nothing
  trueName  = System "True" Nothing
  copyName  = System ">>>" Nothing
  equalHereName    = System "equalHere" Nothing
  notEqualHereName = System "notEqualHere" Nothing

api :: String -> Var
api = Api

isApi :: Var -> Bool
isApi Api{} = True
isApi _     = False

prelude :: String -> Var
prelude = Prelude

conLabel :: Var -> Var
conLabel  = Prefixed "L"

conRepr :: Var -> Var
conRepr   = Prefixed ""

thunkRepr :: Var -> Var
thunkRepr = Prefixed "Thunk"

wrapData :: Var -> Var
wrapData  = Prefixed "D"

caseData :: Var -> Var
caseData  = Prefixed "case"

mkCon :: Var -> Var
mkCon     = Prefixed "con"

data Var
  = X
  | Var String
  | Con String
  | Api String
  | System    String (Maybe (Type Var))
  | SystemCon String (Maybe (Type Var))
  | Prelude String
  | Proj (Type Var) Int
  | Int :~ Var
  | Prefixed String Var
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
    Api x         -> x
    Prelude x     -> x
    System    x m -> x ++ maybe "" ppRender m
    SystemCon x m -> x ++ maybe "" ppRender m
    Prefixed "" x -> varStr' x
    Prefixed d x  -> d ++ "_" ++ varStr' x

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

-- A family of monomorphic Maybes

maybeTC    = System "Maybe" . Just
justVar    = SystemCon "Just" . Just
nothingVar = SystemCon "Nothing" . Just

maybeTy :: Type Var -> Type Var
maybeTy x = TyCon (maybeTC x) []

unMaybeTC :: Var -> Maybe (Type Var)
unMaybeTC (System "Maybe" jx) = jx
unMaybeTC _ = Nothing

isMaybeTC :: Var -> Bool
isMaybeTC = isJust . unMaybeTC

unMaybeTy :: Type Var -> Type Var
unMaybeTy (TyCon mmtc []) | Just tc <- unMaybeTC mmtc = tc
unMaybeTy _ = error "unMaybeTy: Not a Maybe Type!"

justGbl :: Type Var -> Global Var
justGbl t = Global (justVar t) (PolyType [] [t] (maybeTy t)) []

nothingGbl :: Type Var -> Global Var
nothingGbl t = Global (nothingVar t) (PolyType [] [] (maybeTy t)) []

justExpr :: Expr Var -> Expr Var
justExpr e = Gbl (justGbl (exprType e)) :@: [e]

nothingExpr :: Type Var -> Expr Var
nothingExpr t = Gbl (nothingGbl t) :@: []

noopVar :: Type Var -> Var
noopVar = SystemCon "noop" . Just

noopExpr :: Type Var -> Expr Var
noopExpr t = Gbl (blankGlobal (noopVar t) t) :@: []

isNoop :: Expr Var -> Bool
isNoop (Match _ rhss) = all (isNoop . case_rhs) rhss
isNoop (Gbl (Global (SystemCon "Nothing" _) _ _) :@: []) = True
isNoop (Gbl (Global (SystemCon "noop" _)    _ _) :@: []) = True
isNoop _              = False

isNoopCase :: Case Var -> Bool
isNoopCase (Case _ rhs) = isNoop rhs

blankGlobal :: Var -> Type Var -> Global Var
blankGlobal g t = Global g (PolyType [] [] t) []

addMaybesToTheory :: [Var] -> Theory Var -> Theory Var
addMaybesToTheory vs thy@Theory{..} = thy { thy_datatypes = maybe_decls ++ thy_datatypes }
  where
  maybe_decls =
    [ Datatype (maybeTC t) []
        [ Constructor (nothingVar t) (System "isNothing" (Just t)) []
        , Constructor (justVar t) (System "isJust" (Just t)) [(System "fromJust" (Just t),t)]
        ]
    | t <- usort [ t | System "Maybe" (Just t) <- vs ]
    ]


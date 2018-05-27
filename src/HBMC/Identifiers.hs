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

boolNames :: BoolNames Var
boolNames = BoolNames
  { boolName    = System "Bool" Nothing
  , trueName    = SystemCon "True" Nothing
  , falseName   = SystemCon "False" Nothing
  , isTrueName  = System "isTrue" Nothing
  , isFalseName = System "isFalse" Nothing
  }

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
  = Var String
  | Con String
  | Api String
  | System    String (Maybe (Type Var))
  | SystemCon String (Maybe (Type Var))
  | Prelude String
  | Proj Int
  | Refresh Int Var
  | Prefixed String Var
 deriving (Show,Eq,Ord)

isCon :: Var -> Bool
isCon Con{}       = True
isCon SystemCon{} = True
isCon (Refresh _ x) = isCon x
isCon _     = False

proj :: Int -> Var
proj = Proj

unproj :: Var -> Maybe Int
unproj (Proj i) = Just i
unproj _        = Nothing

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh i v) = varMax v `max` i
varMax _             = 0

varStr' :: Var -> String
varStr' x =
  case x of
    Var ""        -> "x"
    Var x         -> x
    Con x         -> varStr' (Var x)
    Refresh i v   -> varStr' v
    Proj i        -> "proj" {- <> pp x <> "_" -} ++ show (i+1)
    Api x         -> x
    Prelude x     -> x
    System    x m -> x ++ maybe "" ppRender m
    SystemCon x m -> x ++ maybe "" ppRender m
    Prefixed "" x -> varStr' x
    Prefixed d x -> d ++ "_" ++ varStr' x

instance PrettyVar Var where
  varStr x =
    case x of
      Refresh i v -> varStr' v -- ++ "_" ++ show i
      _           -> varStr' x

renameTheory :: forall a . (Ord a,PrettyVar a) => Theory a -> Theory Var
renameTheory thy = renameWith disambigId thy
 where
  cons = S.fromList [ c | Constructor c _ _ _ <- universeBi thy ]

  disambigId :: a -> [Var]
  disambigId i = vs : [ Refresh x vs | x <- [0..] ]
    where
      var_or_con
        | i `S.member` cons = Con
        | otherwise         = Var

      vs = case varStr i of
             [] -> var_or_con "x"
             xs -> var_or_con xs

instance Name Var where
  freshNamed x = flip Refresh (Var x) `fmap` fresh
  getUnique    = varMax

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
    [ Datatype (maybeTC t) [] []
        [ Constructor (nothingVar t) [] (System "isNothing" (Just t)) []
        , Constructor (justVar t) [] (System "isJust" (Just t)) [(System "fromJust" (Just t),t)]
        ]
    | t <- usort [ t | System "Maybe" (Just t) <- vs ]
    ]


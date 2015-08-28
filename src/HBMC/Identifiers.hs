{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
module HBMC.Identifiers where

import Tip.Core
import Tip.Pretty
import Tip.Pretty.SMT ()
import Tip.Fresh
import Tip.Haskell.Translate -- Why is HsId exported from here?!
import Tip.Utils.Rename
import Tip.Utils

import Data.Generics.Geniplate

import Data.Set (Set)
import qualified Data.Set as S

import HBMC.Bool

instance Booly Var where
  bool    = System "Bool" Nothing
  true    = SystemCon "True" Nothing
  false   = SystemCon "False" Nothing
  isTrue  = System "isTrue" Nothing
  isFalse = System "isFalse" Nothing

toHsId :: Var -> HsId Var
toHsId (Prelude x)  = Qualified "Prelude" (Just "P") x
toHsId (Api x)      = Qualified "HBMC.Lib" (Just "H") x
toHsId (Proj x)     = Qualified "HBMC.Lib" (Just "H") ("proj" ++ show (x+1))
toHsId (Var "main") = Exact "main"
toHsId x            = Other x

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
  | Refresh Var Int
  | Prefixed String Var
 deriving (Show,Eq,Ord)

isCon :: Var -> Bool
isCon Con{}       = True
isCon SystemCon{} = True
isCon (Refresh x _) = isCon x
isCon _     = False

proj :: Int -> Var
proj = Proj

unproj :: Var -> Maybe Int
unproj (Proj i) = Just i
unproj _        = Nothing

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i
varMax _             = 0

varStr' :: Var -> String
varStr' x =
  case x of
    Var ""        -> "x"
    Var x         -> x
    Con x         -> varStr' (Var x)
    Refresh v i   -> varStr' v
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
      Refresh v i -> varStr' v ++ "_" ++ show i
      _           -> varStr' x

renameTheory :: forall a . (Ord a,PrettyVar a) => Theory a -> Theory Var
renameTheory thy = renameWith disambigId thy
 where
  cons = S.fromList [ c | Constructor c _ _ <- universeBi thy ]

  disambigId :: a -> [Var]
  disambigId i = vs : [ Refresh vs x | x <- [0..] ]
    where
      var_or_con
        | i `S.member` cons = Con
        | otherwise         = Var

      vs = case varStr i of
             [] -> var_or_con "x"
             xs -> var_or_con xs

instance Name Var where
  fresh        = refresh (Var "")
  freshNamed x = refresh (Var x)
  refreshNamed x s = freshNamed (varStr' s ++ x)
  refresh (Refresh v _) = refresh v
  refresh v    = Refresh v `fmap` fresh
  getUnique    = varMax

-- A family of monomorphic Maybes

maybeTC    = System "Maybe" . Just
justVar    = SystemCon "Just" . Just
nothingVar = SystemCon "Nothing" . Just

maybeTy :: Type Var -> Type Var
maybeTy x = TyCon (maybeTC x) []

unMaybeTy :: Type Var -> Type Var
unMaybeTy (TyCon (System "Maybe" (Just x)) []) = x
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


{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad
import Control.Applicative
import Data.Ord
import qualified Data.Foldable as F
import System.Environment
import Text.PrettyPrint
import Text.Show.Pretty hiding (Name)
import Tip
import Tip.CommuteMatch
import Tip.Delambda
import Tip.Fresh
import Tip.HaskellFrontend
import Tip.Id
import Tip.Lift
import Tip.Params
import Tip.Pretty
import Tip.Simplify
import Tip.Utils.Renamer

import Data.Generics.Geniplate

import TipLift
import TipMonadic
import TipTarget
import TipExample
import TipToSimple
import TipData
-- Main


main :: IO ()
main = do
    f:es <- getArgs
    thy <- readHaskellFile Params
      { file = f
      , include = []
      , flags = [] -- [PrintCore,PrintProps,PrintExtraIds]
      , only = es -- []
      , extra = []
      , extra_trans = [] -- es
      }
    -- putStrLn (ppRender thy)
    let thy0 = addBoolToTheory (renameWith disambigId thy)

    let thy1 = (commuteMatch <=< simplifyExpr aggressively <=< delambda) `vifne` thy0

    -- ppp thy1

    let (dis,_) = unzip (map dataInfo (thy_data_decls thy1))
        di      = concat dis

    let thy2 = (removeLabelsFromTheory <=< projectPatterns di) `vifne` thy1


    let func_decls = [ fn | fn <- thy_func_decls thy2, Tip.func_name fn /= labelName ]

    let data_decls =
          [ d | d <- thy_data_decls thy2
              , and [ False | Tip.BuiltinType Tip.Integer :: Tip.Type Var <- universeBi d ]
              ]

    let decls = runFreshFrom (maximumOn varMax thy2) $
          do fn_decls <- mapM trFun func_decls
             dt_decls <- mapM trDatatype data_decls
             prop_decls <- mapM trProp (thy_form_decls thy2)
             return (Decls (concat fn_decls ++ concat dt_decls ++ prop_decls))

    putStrLn "{-# LANGUAGE ScopedTypeVariables #-}"
    putStrLn "{-# LANGUAGE TypeFamilies #-}"
    putStrLn "{-# LANGUAGE FlexibleInstances #-}"
    putStrLn "{-# LANGUAGE MultiParamTypeClasses #-}"
    putStrLn "{-# LANGUAGE GeneralizedNewtypeDeriving #-}"
    putStrLn "import NewNew"
    ppp decls

vifne :: F.Foldable f => (f Var -> Fresh a) -> f Var -> a
f `vifne` x = runFreshFrom (maximumOn varMax x) (f x)

maximumOn :: (F.Foldable f,Ord b) => (a -> b) -> f a -> b
maximumOn f = f . F.maximumBy (comparing f)

data Var
  = Var String | Refresh Var Int
  | Api String | Prelude String
  | Label | Skip | Call | Cancel | Proj Var Int
 deriving (Show,Eq,Ord)

instance Booly Var where
  true  = Var "True"
  false = Var "False"
  bool  = Var "Bool"

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i
varMax _             = 0

instance Interface Var where
  api     = Api
  prelude = Prelude

  proj = Proj
  unproj (Proj v i) = Just (v,i)
  unproj _          = Nothing

  conLabel  f = Var $ "Lbl_" ++ ppRender f
  conRepr   f = Var $ ppRender f ++ "_Repr"
  thunkRepr f = Var $ "Thunk_" ++ ppRender f
  wrapData  f = Var $ "Wrap_" ++ ppRender f
  mkCon     f = Var $ "con" ++ ppRender f

instance Pretty Var where
  pp x =
    case x of
      Var ""      -> text "x"
      Var xs      -> text xs
      Refresh v i -> pp v <> int i
      Proj x i    -> "proj" {- <> pp x <> "_" -} <> pp (i+1)
      Api x       -> text x
      Prelude x   -> text x
      _           -> text (show x)

disambigId :: Id -> [Var]
disambigId i = vs : [ Refresh vs x | x <- [0..] ]
  where
    vs = case ppId i of
           "label" -> Label
           []      -> Var "x"
           xs      -> Var xs

instance Name Var where
  fresh     = refresh (Var "")
  refresh v = Refresh v `fmap` fresh

instance Call Var where
  labelName  = Label
  skipName   = Skip
  callName   = Call
  cancelName = Cancel

-- add bool

class Booly a where
  bool  :: a
  true  :: a
  false :: a

instance Booly String where
  bool  = "Bool"
  true  = "True"
  false = "False"

addBool :: forall f a . (TransformBi (Pattern a) (f a),TransformBi (Head a) (f a),Booly a) => f a -> f a
addBool = transformBi f . transformBi g
  where
    f :: Head a -> Head a
    f (Builtin (Lit (Bool b))) = Gbl (gbl b)
    f hd                       = hd

    g :: Pattern a -> Pattern a
    g (Tip.LitPat (Bool b))    = Tip.ConPat (gbl b) []
    g pat                      = pat

    gbl b =
      Global
        (if b then true else false)
        (PolyType [] [] (Tip.TyCon bool []))
        []
        ConstructorNS

addBoolToTheory :: Booly a => Theory a -> Theory a
addBoolToTheory Theory{..} = addBool Theory{thy_data_decls=bool_decl:thy_data_decls,..}
  where
    bool_decl = Datatype bool [] [Constructor false [],Constructor true []]

-- project

projectPatterns :: forall f a . (TransformBiM Fresh (Tip.Expr a) (f a),Interface a) => DataInfo a -> f a -> Fresh (f a)
projectPatterns di =
  transformBiM $ \ e0 ->
    case e0 of
      Match e alts ->
        Match e <$> -- nabmi fa lo nu .ebu na sampu ju'i .i pu'o fu'irgau
          sequence
            [ case pat of
                Default -> return (Case Default rhs)
                Tip.ConPat k vars
                  | Just (tc,ixs) <- lookup (gbl_name k) di
                  -> Case (Tip.ConPat k []) <$>
                       substMany
                         [ (v,Gbl (fun (proj tc i)) :@: [e])
                         | (v,i) <- vars `zip` ixs
                         ]
                         rhs
                _ -> error $ "projectPatterns: " ++ ppShow di ++ "\n" ++ ppRender e0
            | Case pat rhs <- alts
            ]
      _  -> return e0

-- example

pprint :: Show a => a -> IO ()
pprint = putStrLn . ppShow

ppp :: Pretty a => a -> IO ()
ppp = putStrLn . ppRender

instance Pretty String where
  pp = text

instance Call String where
  labelName  = "label"
  skipName   = "skip"
  callName   = "call"
  cancelName = "cancel"

instance Name String where
  fresh     = refresh "u"
  refresh x = fresh >>= \ i -> return (x ++ "_" ++ show (i :: Int))

{-
instance Proj String where
  proj tc i = "proj_" ++ tc ++ "_" ++ show i
  unproj ('p':'r':'o':'j':'_':s) =
    case break ('_' ==) (reverse s) of
      (i,'_':rtc) | [(n,[])] <- reads (reverse i) -> Just (reverse rtc,n)
      _ -> Nothing
  unproj _ = Nothing
-}

{-
instance Monadic String where
  memofun   f = "memo_" ++ f
  construct f = "con_" ++ f
  conLabel  f = "lbl_" ++ f
  returnH   = "return"
  newCall   = "newCall"
  new       = "new"
  waitCase  = "waitCase"
  con       = "Con"
  memcpy    = "memcpy"
  whenH     = "when"
  unlessH   = "unless"
  (=?)      = "(=?)"
-}

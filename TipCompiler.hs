{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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

    ppp thy1

    let (dis,_) = unzip (map dataInfo (thy_data_decls thy1))
        di      = concat dis

    let thy2 = (removeLabelsFromTheory <=< projectPatterns di) `vifne` thy1

    ppp thy2

    forM_ (thy_func_decls thy2) $
      \ Function{..} ->
          do ppp func_name
             putStrLn "="
             let e = toExpr `vifne` func_body
             ppp e
             putStrLn ""
             ppp ((\ e' -> do { x <- fresh; trExpr e' x }) `vifne` e)

vifne :: F.Foldable f => (f Var -> Fresh a) -> f Var -> a
f `vifne` x = runFreshFrom (maximumOn varMax x) (f x)

maximumOn :: (F.Foldable f,Ord b) => (a -> b) -> f a -> b
maximumOn f = f . F.maximumBy (comparing f)

data Var = Var String | Refresh Var Int | Label | Skip | Call | Cancel | Proj Var Int
  deriving (Show,Eq,Ord)

instance Booly Var where
  true  = Var "True"
  false = Var "False"
  bool  = Var "Bool"

instance Proj Var where
  proj = Proj
  unproj (Proj v i) = Just (v,i)
  unproj _          = Nothing

instance Monadic Var where
  memofun   f = Var $ "memo_" ++ ppRender f
  construct f = Var $ "con_" ++ ppRender f
  conLabel  f = Var $ "lbl_" ++ ppRender f
  returnH   = Var $ "return"
  newCall   = Var $ "newCall"
  new       = Var $ "new"
  waitCase  = Var $ "waitCase"
  con       = Var $ "Con"
  memcpy    = Var $ "memcpy"
  whenH     = Var $ "when"
  unlessH   = Var $ "unless"
  (=?)      = Var $ "(=?)"

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i
varMax _             = 0

instance Pretty Var where
  pp x =
    case x of
      Var ""      -> text "x"
      Var xs      -> text xs
      Refresh v i -> pp v <> int i
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
        (PolyType [] [] (TyCon bool []))
        []
        ConstructorNS

addBoolToTheory :: Booly a => Theory a -> Theory a
addBoolToTheory Theory{..} = addBool Theory{thy_data_decls=bool_decl:thy_data_decls,..}
  where
    bool_decl = Datatype bool [] [Constructor false [],Constructor true []]

-- project

projectPatterns :: forall f a . (TransformBiM Fresh (Tip.Expr a) (f a),Proj a) => DataInfo a -> f a -> Fresh (f a)
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

instance Proj String where
  proj tc i = "proj_" ++ tc ++ "_" ++ show i
  unproj ('p':'r':'o':'j':'_':s) =
    case break ('_' ==) (reverse s) of
      (i,'_':rtc) | [(n,[])] <- reads (reverse i) -> Just (reverse rtc,n)
      _ -> Nothing
  unproj _ = Nothing

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

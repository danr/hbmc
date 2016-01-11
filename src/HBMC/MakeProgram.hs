{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module HBMC.MakeProgram where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Tip.Core
import Tip.Fresh
import Tip.Utils

import HBMC.Identifiers hiding (Con,Proj,Var)
import HBMC.Identifiers (Var())

import HBMC.Data

import HBMC.Params
import Tip.Passes
import Tip.Pass.Booleans

import Data.Generics.Geniplate

import qualified HBMC.Program as P
import qualified HBMC.Object as Object

import Data.List
import Data.Ord

import Control.Monad
import Control.Applicative( (<$>), (<*>) )

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

import qualified Data.Map as M
import Data.Map( Map )

calls :: Var -> Expr Var -> [[Expr Var]]
calls f e = [ es | Gbl (Global f' _ _) :@: es <- universeBi e, f == f' ]

decreasing :: [Var] -> [[Expr Var]] -> [[Bool]]
decreasing as ess =
  [ [ e `isProjectionOf` a
    | (a,e) <- as `zip` es
    ]
  | es <- ess
  ]

isProjectionOf :: Expr Var -> Var -> Bool
isProjectionOf e0 v =
  let res =
        case e0 of
          Gbl (Global g _ _) :@: [e]
            | Just{} <- unproj g -> case e of
                                      Lcl (Local x _) -> x == v
                                      _               -> e `isProjectionOf` v
          _ -> False
  in  -- traceShow (pp e0, v, res)
      res

-- unused for now
bestLaterCoordinate :: Var -> [Var] -> Expr Var -> Int
bestLaterCoordinate f as
  = fst
  . maximumBy (comparing snd)
  . zip [0..]
  . map (length . filter id)
  . transpose
  . decreasing as
  . calls f

anyTerminatingCoordinate :: Var -> [Var] -> Expr Var -> Bool
anyTerminatingCoordinate f as
  = any and
  . transpose
  . decreasing as
  . calls f

-- Insert laters to all unsafe calls in a mutually recursive group
insertLaters :: Params -> [Function Var] -> [Function Var]
insertLaters params grp =
  let res =
        [ Function{
            func_body =
              if length grp > 1 || not self_terminates || always_later params
                then laterExpr func_body
                else func_body
            , ..
          }
        | (_l,Function{..},r) <- cursor grp
        , let func_vars  = map lcl_name func_args
        , let self_terminates =
                anyTerminatingCoordinate func_name func_vars func_body
        ]
  in  -- traceShow (pp grp, pp res)
      res
  where func_name_ = func_name

laterCallsTo :: [Var] -> Expr Var -> Expr Var
laterCallsTo gs = transformBi $
  \ e0 -> case e0 of
    Gbl (Global g _ _) :@: es | g `elem` gs -> laterExpr e0
    _ -> e0

-- unused for now
laterCallsCoord :: Int -> Var -> [Var] -> Expr Var -> Expr Var
laterCallsCoord i f as = transformBi $
  \ e0 -> case e0 of
    Gbl (Global f' _ _) :@: es
      | f' == f, not ((es !! i) `isProjectionOf` (as !! i)) -> laterExpr e0
    _ -> e0

trFunction :: Params -> DataInfo Var -> [Component Var] -> Function Var -> Fresh (P.PreFunction Var)
trFunction p di fn_comps Function{..} =
  do let (rec,_mut_rec) = case lookupComponent func_name fn_comps of
                            Just (Rec xs) -> (True,length xs > 1)
                            _             -> (False,False)
     let args = map lcl_name func_args
     let mem  = memo p && rec
     body <- trExpr di func_body

     return (func_name,
               ((if mem then (if dyno p then P.DynoMemo else P.DoMemo)
                        else P.Don'tMemo)
                ,(args,body)))

type Prop a = ([(a,Object.Type a)],P.Expr a)

trFormula :: DataInfo Var -> Formula Var -> Fresh (Prop Var)
trFormula di fm =
  case fm of
    Formula r      _ (_:_) e -> error "trFormula, TODO: translate type variables"
    Formula Prove  i []    e -> trFormula di (Formula Assert i [] (neg e))
    Formula Assert _ []    e ->
      do let (vs,e') = fmap neg (forallView (neg e))
         let cs      = conjuncts (ifToBoolOp e')
         asserts <- mapM (trToTrue di) cs
         return ([ (x,tr_type di t) | Local x t <- vs ],P.ConstraintsOf asserts)

trToTrue :: DataInfo Var -> Expr Var -> Fresh (P.Expr Var)
trToTrue di e0 =
  case e0 of
    Builtin Equal    :@: ~[e1,e2] -> tr Equal    e1 e2
    Builtin Distinct :@: ~[e1,e2] -> tr Distinct e1 e2
    _                             -> tr Equal    e0 (boolExpr boolNames True)
  where
  tr pol e1 e2 =
    do let k = removeBuiltinBoolFrom boolNames . boolOpToIf
       trExpr di (Builtin pol :@: [k e1,k e2])

conjuncts :: Expr a -> [Expr a]
conjuncts e0 =
  case e0 of
    Builtin And :@: es                            -> concatMap conjuncts es
    Builtin Not :@: [Builtin Or :@: es]           -> concatMap conjuncts es
    Builtin Not :@: [Builtin Implies :@: [e1,e2]] -> concatMap conjuncts [e1,neg e2]
    _                                             -> [e0]

trExpr :: DataInfo Var -> Expr Var -> Fresh (P.Expr Var)
trExpr di = go
  {-
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  ([x :<-: New False (tyConOf t) | (Local x t,_) <- matches ] ++)
         <$> go (makeLets (fn_calls ++ matches) rest)
  -}
  where
  go :: Expr Var -> Fresh (P.Expr Var)
  go e0 =
    case e0 of
      Let x (Lam vs e) b -> P.LetApp (lcl_name x) (map lcl_name vs) <$> go e <*> go b

      Let x e b -> P.Let (lcl_name x) <$> go e <*>  go b

      {-
      Let x (Match s brs) e ->
        (++) <$> trMatch di s brs (Just (lcl_name x)) <*> go e

      Let x (Gbl (Global f _ _) :@: ss) e ->
        (lcl_name x :<-: Call f (map trSimple ss) :) <$> go e
      -}

      Match s brs ->
        P.Case
          <$> go s
          <*> sequence
           [ do rhs' <- go rhs
                let pat' = case pat of
                             ConPat g _ -> Just (tr_con di g)
                             Default    -> Nothing
                return (pat',[],rhs')
           | Case pat rhs <- brs
           ]

      Gbl later :@: [e] | later == laterGbl -> P.Later <$> go e

      Gbl (Global (SystemCon "noop" _) _ _) :@: _ -> return P.noop

      Builtin Equal    :@: [e1,e2] -> P.EqPrim P.EqualHere    <$> go e1 <*> go e2
      Builtin Distinct :@: [e1,e2] -> P.EqPrim P.NotEqualHere <$> go e1 <*> go e2

      Lcl (Local x _) -> return (P.Var x)

      Gbl (Global k _ _) :@: [s] | Just (t,i) <- unproj k  -> do s' <- go s
                                                                 return (P.Proj s' (tr_type di t) i)
      Gbl g@(Global k _ _) :@: ss | isCon k -> P.Con (tr_con di g) <$> mapM go ss

      Gbl (Global f _ _) :@: es -> P.App P.Don'tMemo f <$> mapM go es
                                        -- don't memo for now, will be added later

      _ -> error $ "trExpr " ++ ppRender e0

isMatch :: Expr a -> Bool
isMatch Match{} = True
isMatch _       = False

tyConOf :: Type a -> a
tyConOf (TyCon x _) = x

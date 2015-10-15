{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module HBMC.Monadic where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Tip.Core as Tip
import Tip.Core hiding (Case(..))
import Tip.Fresh
import Tip.Utils

import HBMC.Identifiers hiding (Con,Proj,Var)
import HBMC.Identifiers (Var())

import HBMC.Bool
import HBMC.Params
import Tip.Passes

import Data.Generics.Geniplate

import HBMC.ToSimple

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

-- the other constructors
type ConInfo a = a -> Maybe [a]

-- Translation to constraint-generation DSL:

data Verbosity = Quiet | Verbose deriving (Eq,Ord,Show,Read)

data Func a = Func a [a] a Bool Bool (Mon a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Prop a = Prop [a] (Mon a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Ret a
  = Simp (Simp a)
  | Unit      -- a dummy unit to return for equalHere
  | Dead      -- a dummy value to return for Noop (no need to return anything here)
  | CaseRet (Case a) -- return what the case returns
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Rhs a
  = New Bool a
  | Call a [Simp a]
  | CaseRhs (Case a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Case a = Case a (Simp a) a [(a,Mon a)]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data BinPrim = EqualHere | NotEqualHere
  deriving (Eq,Ord,Show)

data Mon a = Mon [Act a] (Ret a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Act a
  = Simp a :>>>: a
  | a :<-: Rhs a
  | BinPrim BinPrim (Simp a) (Simp a)
-- | InsistIsn't a a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Simp a
  = Con a a [Simp a]
  | Proj Int a
  | Var a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

{-
simpMon :: Eq a => Mon a -> Mon a
simpMon (Mon as s) =
  Mon (map simpAct . collapse $ as) s
  where
  collapse m =
    case
      [ (l ++ [ab'] ++ m ++ r)
      | (l,a,r1) <- cursor m
      , (m,b,r)  <- cursor r1
      , Just ab' <- [collapseAct a b] ] of
      m':_ -> collapse m'
      []   -> m

simpAct :: Eq a => Act a -> Act a
simpAct (Case tc s v c m) = Case tc s v c (simpMon m)
simpAct a = a

collapseAct :: Eq a => Act a -> Act a -> Maybe (Act a)
collapseAct
  (Guard When a m)
  (Guard When b n)
  | m == n = Just (Guard When (a ++ b) m)

collapseAct
  (Guard g1 a m)
  (Guard g2 b n)
  | g1 == g2 && a == b = Just (Guard g1 a (m ++ n))

collapseAct
  (Case tc s1 v1 c1 m1)
  (Case _  s2 v2 c2 m2)
  | s1 == s2 = Just (Case tc s1 v1 c1 (m1 ++ map (su v1 v2 . su c1 c2) m2))

collapseAct _ _ = Nothing
-}

su :: (Eq a,Functor f) => a -> a -> f a -> f a
su for what = fmap (\ x -> if x == what then for else x)

-- Simple termination check: there is some argument that always decreases
-- Not working for mutually recursive groups!
terminates :: Var          -- function name
           -> [Var]        -- arguments
           -> Expr Var -- body as a simple expression
           -> Bool
terminates _ [] _ = True
terminates f as e =
  or [ and [ chase a (es !! i)
           | Gbl (Global f' _ _) :@: es <- universeBi e
           , f == f' ]
     | (a,i) <- as `zip` [0..] ]
  where
  chase needle (Gbl (Global g _ _) :@: [Lcl (Local x _)])
    | Just{} <- unproj g
    = needle == x
  chase _ _ = False

trFunction :: Params -> ConInfo Var -> [Component Var] -> Function Var -> Fresh (Func Var)
trFunction p ci fn_comps Function{..} =
  do let (rec,mut_rec) = case lookupComponent func_name fn_comps of
                           Just (Rec xs) -> (True,length xs > 1)
                           _             -> (False,False)
     let args = map lcl_name func_args
     let chk = not (terminates func_name args func_body) || mut_rec
     let mem = memo p && rec
     body <- trExpr ci func_body
     return (Func func_name args (tyConOf func_res) mem chk body)

     {- let tt = modTyCon wrapData . trType
        in H.TySig func_name
              [ H.TyCon s [H.TyVar tv]
              | tv <- func_tvs
              , s <- [api "Equal",prelude "Ord",api "Constructive"]
              ]
              (nestedTyTup (map (tt . lcl_type) func_args)
               `TyArr` (H.TyCon (api "H") [tt func_res]))
       -}

{-
superSimple :: Expr a -> Bool
superSimple e =
  case e of
    Lcl _   -> True
    _ :@: _ -> True
    Let _ (_ :@: _) r -> superSimple r
    _ -> False
    -}

trFormula :: ConInfo Var -> Formula Var -> Fresh (Prop Var)
trFormula ci fm =
  case fm of
    Formula r      (_:_) e -> error "trFormula, TODO: translate type variables"
    Formula Prove  []    e -> trFormula ci (Formula Assert [] (neg e))
    Formula Assert []    e ->
      do let (vs,e') = fmap neg (forallView (neg e))
         let cs      = conjuncts (ifToBoolOp e')
         let news    = [ x :<-: New True (tyConOf t) | Local x t <- vs ]
         asserts <- mapM (trToTrue ci) cs
         return (Prop (map lcl_name vs) (Mon (news ++ concat asserts) Unit))

trToTrue :: ConInfo Var -> Expr Var -> Fresh [Act Var]
trToTrue ci e0 =
  case e0 of
    Builtin Equal    :@: ~[e1,e2] -> tr True  e1 e2
    Builtin Distinct :@: ~[e1,e2] -> tr False e1 e2
    _                             -> tr True  e0 (booly True)
  where
  tr pol e1 e2 =
    do (lets1,s1) <- collectLets <$> toExprSimpleEnd (addBool (boolOpToIf e1))
       (lets2,s2) <- collectLets <$> toExprSimpleEnd (addBool (boolOpToIf e2))
       let equal_fn = blankGlobal
                        (api (if pol then "equalHere" else "notEqualHere"))
                        (error "trToTrue global type")
       Mon acts Unit <- trExpr ci (makeLets (lets1 ++ lets2) (Gbl equal_fn :@: [s1,s2]))
       return acts

conjuncts :: Expr a -> [Expr a]
conjuncts e0 =
  case e0 of
    Builtin And :@: es                            -> concatMap conjuncts es
    Builtin Not :@: [Builtin Or :@: es]           -> concatMap conjuncts es
    Builtin Not :@: [Builtin Implies :@: [e1,e2]] -> concatMap conjuncts [e1,neg e2]
    _                                             -> [e0]

consMon :: Act a -> Mon a -> Mon a
consMon _ (Mon _ Dead) = Mon [] Dead
consMon a (Mon as r)   = Mon (a:as) r

-- [[ e ]]
trExpr :: ConInfo Var -> Expr Var -> Fresh (Mon Var)
trExpr ci = go
  {- TODO: circular definitions will always need a new
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  ([x :<-: New False (tyConOf t) | (Local x t,_) <- matches ] ++)
         <$> go (makeLets (fn_calls ++ matches) rest)
  -}
  where
  go e0 =
    case e0 of
      Let x (Match s brs) e ->
        do c <- trMatch ci s brs
           consMon (lcl_name x :<-: CaseRhs c) <$> go e

      Let x (Gbl (Global f _ _) :@: ss) e ->
        consMon (lcl_name x :<-: Call f (map trSimple ss)) <$> go e

      Match s brs ->
         do c <- trMatch ci s brs
            return (Mon [] (CaseRet c))

      Gbl (Global (SystemCon "noop" _) _ _) :@: _ ->
        return (Mon [] Dead)

      Gbl (Global (Api "equalHere") _ _) :@: [s1,s2] ->
        return (Mon [BinPrim EqualHere (trSimple s1) (trSimple s2)] Unit)

      Gbl (Global (Api "notEqualHere") _ _) :@: [s1,s2] ->
        return (Mon [BinPrim NotEqualHere (trSimple s1) (trSimple s2)] Unit)

      s -> return (Mon [] (Simp (trSimple s)))

trMatch :: ConInfo Var -> Expr Var -> [Tip.Case Var] -> Fresh (Case Var)
trMatch ci e brs | TyCon tc _ <- exprType e =
  do s <- fresh

     let ls = Local s (exprType e)

     let others  = foldr1 intersect [ os
                                    | Tip.Case (ConPat (Global k _ _) _) _ <- brs
                                    , let Just os = ci k
                                    ]

     let brs_wo_def = case brs of
                        Tip.Case Default b:rest -> [Tip.Case (ConPat (Global k er er) er) b | k <- others ]++rest
                        _ -> brs
                      where er = error "brs_wo_def"

     brs' <- concat <$> mapM (trCase ci . replaceProj e ls) brs_wo_def

     -- conDelayed e $
     --    [ ...
     --    , (c,\ s -> do [[ br_i (sel s // sel e) ]])
     --    , ...
     --    ]

     return $ Case tc (trSimple e) s brs'

     {-
     let to_con :: Expr Var -> Maybe [Var]
         to_con (Gbl g :@: _) = ci (gbl_name g)
         to_con _             = Nothing

     let con_others =
           case (mr,sequence (map to_con (rhssUnderLet (Match e brs)))) of
             (Just r,Just (os:oss)) -> [InsistIsn't r o | o <- foldr intersect os oss]
             _                      -> []
     -}

trMatch _ _ _ = error "trMatch: Not a TyCon!"

trCase :: ConInfo Var -> Tip.Case Var -> Fresh [(Var,Mon Var)]
trCase ci (Tip.Case pat rhs) =
  do body <- trExpr ci rhs
     return $
       case body of
         Mon _ Dead -> []
         _ ->
           case pat of
             Default -> error "eek, default pattern!"
             ConPat (Global k _ _) _ -> [(k,body)]

-- sel s // sel e
replaceProj :: Expr Var -> Local Var -> Tip.Case Var -> Tip.Case Var
replaceProj e s (Tip.Case p rhs) =
  Tip.Case p $ (`transformExprIn` rhs) $
    \ e0 -> case e0 of
      hd@(Gbl (Global g _ _)) :@: [e'] | e == e', Just{} <- unproj g -> hd :@: [Lcl s]

      _ -> e0

trSimple :: Expr Var -> Simp Var
trSimple s =
  case s of
    Lcl (Local x _) -> Var x
    Gbl (Global k _ _) :@: [s] | Just i <- unproj k -> Proj i (let Var x = trSimple s in x)
    Gbl (Global k (PolyType _ _ (TyCon tc _)) _) :@: ss -> Con tc k (map trSimple ss)
    _ -> error $ "trSimple, not simple: " ++ ppRender s

isMatch :: Expr a -> Bool
isMatch Match{} = True
isMatch _       = False

tyConOf :: Type a -> a
tyConOf (TyCon x _) = x

rhssUnderLet :: Expr Var -> [Expr Var]
rhssUnderLet (Match _ brs) = concatMap (rhssUnderLet . Tip.case_rhs) brs
rhssUnderLet (Let _ _ e)   = rhssUnderLet e
rhssUnderLet e             = [ e | not (isNoop e) ]


{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
module HBMC.Monadic where

import Tip.Core
import Tip.Fresh

import HBMC.Identifiers hiding (Con,Proj,Var)
import HBMC.Identifiers (Var())

import HBMC.Bool
import Tip.Passes

import Data.Generics.Geniplate

import HBMC.ToSimple

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

-- Translation to constraint-generation DSL:

data Verbosity = Quiet | Verbose deriving (Eq,Ord,Show,Read)

data Func a = Func a [a] a a Bool (Mon a)
  deriving (Eq,Ord,Show,Functor)

data Prop a = Prop [a] (Mon a)
  deriving (Eq,Ord,Show,Functor)

data Pred a = a :=? a
  deriving (Eq,Ord,Show,Functor)

data Guard = When | Unless
  deriving (Eq,Ord,Show)

data Rhs a
  = New Bool a
  | Call a [Simp a]
  deriving (Eq,Ord,Show,Functor)

data BinPrim = EqualHere | NotEqualHere
  deriving (Eq,Ord,Show)

data Act a
  = Guard Guard [Pred a] (Mon a)
  | CaseData a (Simp a) a a (Mon a)
  | Simp a :>>>: a
  | a :<-: Rhs a
  | BinPrim BinPrim (Simp a) (Simp a)
  deriving (Eq,Ord,Show,Functor)

data Simp a
  = Con a a [Simp a]
  | Proj Int a
  | Var a
  deriving (Eq,Ord,Show,Functor)

type Mon a = [Act a]

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
  chase needle (Lcl (Local x _)) = needle == x
  chase needle (Gbl (Global g _ _) :@: [e]) | Just{} <- unproj g = chase needle e
  chase _ _ = False

trFunction :: Function Var -> Fresh (Func Var)
trFunction Function{..} =
  do r <- fresh
     let args = map lcl_name func_args
     let chk = not (terminates func_name args func_body)
     body <- trExpr func_body (Just r)
     return (Func func_name args r (tyConOf func_res) chk body)
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

trFormula :: Formula Var -> Fresh (Prop Var)
trFormula fm =
  case fm of
    Formula r      (_:_) e -> error "trFormula, TODO: translate type variables"
    Formula Prove  []    e -> trFormula (Formula Assert [] (neg e))
    Formula Assert []    e ->
      do let (vs,e') = fmap neg (forallView (neg e))
         let cs      = conjuncts (ifToBoolOp e')
         let news    = [ x :<-: New True (tyConOf t) | Local x t <- vs ]
         asserts <- mapM trToTrue cs
         return (Prop (map lcl_name vs) (news ++ concat asserts))

trToTrue :: Expr Var -> Fresh (Mon Var)
trToTrue e0 =
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
       trExpr (makeLets (lets1 ++ lets2) (Gbl equal_fn :@: [s1,s2])) Nothing

conjuncts :: Expr a -> [Expr a]
conjuncts e0 =
  case e0 of
    Builtin And :@: es                            -> concatMap conjuncts es
    Builtin Not :@: [Builtin Or :@: es]           -> concatMap conjuncts es
    Builtin Not :@: [Builtin Implies :@: [e1,e2]] -> concatMap conjuncts [e1,neg e2]
    _                                             -> [e0]

-- [[ e ]]=> r
trExpr :: Expr Var -> Maybe Var -> Fresh (Mon Var)
trExpr e00 mr =
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  ([x :<-: New False (tyConOf t) | (Local x t,_) <- matches ] ++)
         <$> go (makeLets (fn_calls ++ matches) rest)
  where
  go e0 =
    case e0 of
      Let x (Match s brs) e ->
        (:) <$> trMatch s brs (Just (lcl_name x)) <*> go e

      Let x (Gbl (Global f _ _) :@: ss) e ->
        (lcl_name x :<-: Call f (map trSimple ss) :) <$> go e

      Match s brs -> (:[]) <$> trMatch s brs mr

      Gbl (Global g _ _) :@: _ | g == noopVar -> return []

      Gbl (Global (Api "equalHere") _ _) :@: [s1,s2] ->
        return [BinPrim EqualHere (trSimple s1) (trSimple s2)]

      Gbl (Global (Api "notEqualHere") _ _) :@: [s1,s2] ->
        return [BinPrim NotEqualHere (trSimple s1) (trSimple s2)]

      s | Just r <- mr -> return [trSimple s :>>>: r]

      _ -> error $ "trExpr " ++ ppRender e0

trMatch :: Expr Var -> [Case Var] -> Maybe Var -> Fresh (Act Var)
trMatch e brs mr | TyCon tc _ <- exprType e =
  do c <- fresh
     s <- fresh

     let ls = Local s (exprType e)

     let ctors = [ k | Case (ConPat (Global k _ _) _) _ <- brs ]

     brs' <- mapM (trCase c mr ctors . replaceProj e ls) brs

     -- waitCase e $ \ (Con c s) ->
     --   ...
     --   when (c =? K_i) $ do [[ br_i (sel s // sel e) ]]=> r
     --   ...

     return $ CaseData tc (trSimple e) c s (concat brs')

trMatch _ _ _ = error "trMatch: Not a TyCon!"

-- sel s // sel e
replaceProj :: Expr Var -> Local Var -> Case Var -> Case Var
replaceProj e s (Case p rhs) =
  Case p $ (`transformExprIn` rhs) $
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

trCase :: Var -> Maybe Var -> [Var] -> Case Var -> Fresh (Mon Var)
trCase c mr cons (Case pat rhs) =
  do body <- trExpr rhs mr
     return $
       case body of
         [] -> []
         _  ->
           return $
             case pat of
               Default                 -> Guard Unless [c :=? k | k <- cons] body
               ConPat (Global k _ _) _ -> Guard When   [c :=? k] body

isMatch :: Expr a -> Bool
isMatch Match{} = True
isMatch _       = False

tyConOf :: Type a -> a
tyConOf (TyCon x _) = x
